#!/usr/bin/env python3
"""Build the proof with Lake and write receipts/build-stats.txt from this run's own measurements.

    python3 scripts/measure_build.py [--first MODULE ...] [--target Zeta2] [--out FILE] [--log FILE]

Needs Python 3.9 or later: on an older one it says so and stops before building anything.

Run `lake exe cache get` first, as scripts/verify.sh does: the measurement starts at the first
`lake build`. Every figure the statistics file holds was measured by the run that wrote it, and
the file says how, and from where; a figure that could not be measured is written "not measured"
with the reason, and that never changes the build's verdict. Beside the commit it builds at, it
records the commit the tree was exported from, as receipts/COUNTS.json names it, which ties these
statistics to those counts. Before anything else it removes git's location variables
(GIT_LOCATION_VARS) from its own environment, so that git, and lake's own git calls on its packages,
find the repository from this tree's directory and not from whatever repository the calling
environment names. Should this script itself fail after lake has run, it first writes what it had
measured, as it stands. The exit status is lake's: its exit code, or 128 plus the number of the
signal that ended it.

Memory is carried in bytes and written as bytes, as KiB when the bytes are a whole number of
KiB, and as GiB, which is bytes / 1024^3. The kernel reports a process's peak resident memory
(wait4's ru_maxrss) in KiB on Linux and in bytes on macOS, and ps reports resident memory in KiB
on both. Disk is counted as du counts it: st_blocks x 512 bytes per file or directory, a file
with several hard links once.

Lake has no jobs flag at this toolchain: how many modules compile at once is decided by the Lean
runtime's task pool, which LEAN_NUM_THREADS sizes. This script does not set it; it records the
value it saw, and the most lean processes it saw running at once. A lean process is a process
below lake whose executable is named lean and that is not a zombie: ps reads the executable from
the comm column (its path on macOS, its name on Linux) and the command line from the args column,
in two calls that each put that column last, so that a path with a space in it is read whole.
"""
import argparse
import json
import os
import platform
import re
import signal
import subprocess
import sys
import threading
import time

MIN_PYTHON = (3, 9)
GIT_LOCATION_VARS = (      # git's location variables: main removes them first
    "GIT_DIR",
    "GIT_WORK_TREE",
    "GIT_COMMON_DIR",
    "GIT_INDEX_FILE",
    "GIT_OBJECT_DIRECTORY",
    "GIT_ALTERNATE_OBJECT_DIRECTORIES",
    "GIT_NAMESPACE",
    "GIT_CONFIG",
    "GIT_CONFIG_PARAMETERS",
    "GIT_CONFIG_COUNT",
    "GIT_IMPLICIT_WORK_TREE",
    "GIT_GRAFT_FILE",
    "GIT_NO_REPLACE_OBJECTS",
    "GIT_REPLACE_REF_BASE",
    "GIT_PREFIX",
    "GIT_SHALLOW_FILE",
)
RU_MAXRSS_UNIT = {"linux": 1024, "darwin": 1}     # bytes in one unit of wait4's ru_maxrss
PS_RSS_UNIT = 1024                                   # ps prints resident memory in KiB on both
PS_TABLE = ("ps", "-A", "-ww", "-o", "pid=,ppid=,rss=,stat=,comm=")    # the executable, last
PS_ARGS = ("ps", "-A", "-ww", "-o", "pid=,args=")                     # the command line, last
BUILT = re.compile(r"^\S+ \[\d+/\d+\](?: \(Optional\))? Built (\S+)(?: \(\d+(?:\.\d+)?m?s\))?\s*$")
ROOTS = re.compile(r"^\s*roots\s*=\s*\[(.*?)\]", re.M | re.S)
SOURCE = re.compile(r"^.*(?:^|[\s/])src/((?:[^\s/]+/)*[^\s/]+)\.lean(?=\s|$)")
FIRST_HELP = """\
build these modules one at a time, each to completion and in the order given, before the full
target: `lake build M` compiles what M imports first and M itself last, with nothing else
compiling beside it. Use it on a machine whose memory is less than what the largest single lean
process needs plus what the lean processes running beside it need. There is no default list: a
previous run's statistics file names the lean processes with the largest sampled peak and the
module each was compiling."""


def platform_key():
    return "linux" if sys.platform.startswith("linux") else sys.platform


def ru_maxrss_bytes(value, key=None):
    """wait4's ru_maxrss in bytes, or None on a platform whose unit this script does not know."""
    unit = RU_MAXRSS_UNIT.get(key or platform_key())
    return None if unit is None else value * unit


def show_bytes(b):
    """`b` bytes, written exactly and as GiB (bytes / 1024^3) to one decimal."""
    kib = f"{b // 1024} KiB, " if b % 1024 == 0 else ""
    return f"{b} bytes ({kib}{b / 1024 ** 3:.1f} GiB)"


def parse_ps(text):
    """[(pid, ppid, resident KiB, state, executable)] for each line PS_TABLE prints; the executable
    is the rest of the line, spaces and all. A line that is not three whole numbers, a state and an
    executable is skipped."""
    rows = []
    for line in text.splitlines():
        f = line.split(None, 4)
        if len(f) == 5 and f[0].isdigit() and f[1].isdigit() and f[2].isdigit():
            rows.append((int(f[0]), int(f[1]), int(f[2]), f[3], f[4].rstrip()))
    return rows


def parse_args(text):
    """{pid: its command line} for each line PS_ARGS prints."""
    out = {}
    for line in text.splitlines():
        f = line.split(None, 1)
        if len(f) == 2 and f[0].isdigit():
            out[int(f[0])] = f[1].rstrip()
    return out


def is_lean(executable, state):
    """Whether a process runs the program lean: its executable is named lean, and it is no zombie."""
    return os.path.basename(executable) == "lean" and not state.startswith("Z")


def module_of(args):
    """The module a lean command line compiles: its source file under the last `src/` directory,
    as a dotted name; None when it names no such file, or there is no command line."""
    m = SOURCE.match(args) if args else None
    return m.group(1).replace("/", ".") if m else None


def lean_descendants(rows, root, args):
    """{pid: (resident KiB, its command line or None)} for the lean processes among all the
    descendants of `root` (children, grandchildren and so on); `args` is {pid: command line}."""
    children = {}
    for pid, ppid, rss, state, executable in rows:
        children.setdefault(ppid, []).append((pid, rss, state, executable))
    found, todo, seen = {}, [root], {root}
    while todo:
        for pid, rss, state, executable in children.get(todo.pop(), []):
            if pid in seen:
                continue
            seen.add(pid)
            todo.append(pid)
            if is_lean(executable, state):
                found[pid] = (rss, args.get(pid))
    return found


class Sampler:
    """Reads the process table when a lake process starts and about every `interval` seconds while
    it runs, and keeps the sampled peak resident memory of each lean process below it."""

    def __init__(self, interval, table=PS_TABLE, cmdlines=PS_ARGS):
        self.interval, self.table, self.cmdlines, self.root = interval, table, cmdlines, None
        self.peaks = {}                        # (pid, the module it compiles or None) -> sampled peak KiB
        self.module = {}                       # pid -> the module its command line last named
        self.read = self.unreadable = self.most = self.largest_sum = 0
        self.why = None
        self._lock = threading.Lock()
        self._stop = threading.Event()
        self._thread = threading.Thread(target=self._run, daemon=True)

    def start(self):
        self._thread.start()

    def stop(self):
        self._stop.set()
        self._thread.join()

    def _run(self):
        while True:
            try:
                self.sample()
            except Exception as e:             # a sampler that dies would read as a quiet build
                self.unreadable += 1
                self.why = f"{type(e).__name__}: {e}"
            if self._stop.wait(self.interval):
                return

    def sample(self):
        with self._lock:
            self._sample()

    def _sample(self):
        root = self.root
        if root is None:
            return
        texts = []
        for cmd in (self.table, self.cmdlines):
            try:
                r = subprocess.run(cmd, capture_output=True, timeout=30)
            except (OSError, subprocess.SubprocessError) as e:
                self.unreadable += 1
                self.why = f"{cmd[0]}: {e}"
                return
            if r.returncode:
                self.unreadable += 1
                self.why = f"{cmd[0]} exited with status {r.returncode}"
                return
            texts.append(r.stdout.decode("utf-8", "replace"))
        rows = parse_ps(texts[0])
        if not rows:
            self.unreadable += 1
            self.why = f"{self.table[0]} printed no process table"
            return
        self.record(rows, parse_args(texts[1]), root)

    def record(self, rows, args, root):
        """One sample: the table `rows` (parse_ps) and the command lines `args` (parse_args), read
        while `root` ran. Each figure is the largest over the samples, never the last one's. The two
        calls are moments apart, so a lean process the table shows alive may have exited by the
        second (its command line then `<defunct>`, `(lean)` or missing): a sample whose command line
        names no module is the module its pid's command line last named, or None when it never named
        one, so that one process is one entry, under its module."""
        self.read += 1
        lean = lean_descendants(rows, root, args)
        self.most = max(self.most, len(lean))
        self.largest_sum = max(self.largest_sum, sum(rss for rss, _ in lean.values()))
        for pid, (rss, line) in lean.items():
            module = module_of(line)
            if module is None:
                module = self.module.get(pid)
            else:
                self.module[pid] = module
            self.peaks[(pid, module)] = max(self.peaks.get((pid, module), 0), rss)


def run_lake(args, log, sampler):
    """Run `lake <args>`, its output copied to stdout and to `log`: (os.wait4's status for lake, the
    rusage of lake and every process it waited for, the names on Lake's "Built" lines)."""
    p = subprocess.Popen(["lake", *args], stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    sampler.root = p.pid
    sampler.sample()                           # at least one read per command, however short
    built = []
    for raw in p.stdout:
        line = raw.decode("utf-8", "replace")
        sys.stdout.write(line)
        sys.stdout.flush()
        log.write(line)
        m = BUILT.match(line.rstrip("\n"))
        if m:
            built.append(m.group(1))
    p.stdout.close()
    _pid, status, usage = os.wait4(p.pid, 0)
    sampler.root = None
    p.returncode = lake_status(status)[0]     # reaped here, so Popen must not wait for it again
    return status, usage, built


def lake_status(status):
    """(the exit status this script returns, the words the statistics file uses) for lake's
    os.wait4 status: lake's exit code, or 128 plus the number of the signal that ended it."""
    if os.WIFSIGNALED(status):
        number = os.WTERMSIG(status)
        try:
            name = signal.Signals(number).name
        except ValueError:
            name = "a signal with no name here"
        return 128 + number, f"killed by signal {number} ({name})"
    if os.WIFEXITED(status):
        code = os.WEXITSTATUS(status)
        return code, str(code)
    return 1, f"wait status {status}, neither an exit nor a signal"


def command(*args):
    """(the stripped output of `args`, None) when it runs and exits 0; else (None, why not)."""
    try:
        r = subprocess.run(args, capture_output=True, text=True, timeout=120)
    except (OSError, subprocess.SubprocessError) as e:
        return None, f"could not run: {e}"
    if r.returncode:
        return None, f"exited with status {r.returncode}"
    return r.stdout.strip(), None


def machine_cpus(count=os.cpu_count):
    """(the machine's logical CPUs, where the figure comes from) or (None, why there is none)."""
    n = count()
    return (n, "os.cpu_count()") if n else (None, "os.cpu_count() returned no number")


def machine_memory(key=None, meminfo="/proc/meminfo", sysctl=("sysctl", "-n", "hw.memsize")):
    """(the machine's memory in bytes, where the figure comes from) or (None, why there is none):
    on Linux the MemTotal line of `meminfo`, whose kB are KiB; on macOS the output of `sysctl`."""
    key = key or platform_key()
    if key == "linux":
        try:
            with open(meminfo, encoding="utf-8") as fh:
                for line in fh:
                    f = line.split()
                    if len(f) == 3 and f[0] == "MemTotal:" and f[1].isdigit() and f[2] == "kB":
                        return int(f[1]) * 1024, f"the MemTotal line of {meminfo}, in KiB"
        except (OSError, UnicodeDecodeError) as e:
            return None, f"{meminfo} could not be read: {e}"
        return None, f"{meminfo} has no line 'MemTotal: <number> kB'"
    if key == "darwin":
        out, why = command(*sysctl)
        if out is not None and out.isdigit():
            return int(out), " ".join(sysctl)
        return None, f"{' '.join(sysctl)} " + (why or f"printed {out!r}, not a number")
    return None, f"no way of reading it is known on {key}"


def allocated(*paths):
    """(the disk the files and directories under `paths` occupy as du counts it, the entries that
    could not be read): st_blocks x 512 bytes of each, a file with several hard links once over all
    of `paths`. None in place of the bytes when one of `paths` is not a directory."""
    if not all(os.path.isdir(p) for p in paths):
        return None, 0
    total, unread, seen = 0, 0, set()
    for top in paths:
        for path in [top] + [os.path.join(d, n) for d, dirs, files in os.walk(top) for n in dirs + files]:
            try:
                st = os.lstat(path)
            except OSError:
                unread += 1
                continue
            if st.st_nlink > 1:
                if (st.st_dev, st.st_ino) in seen:
                    continue
                seen.add((st.st_dev, st.st_ino))
            total += st.st_blocks * 512
    return total, unread


def exported_from(path="receipts/COUNTS.json"):
    """(the commit of the source repository this tree was exported from, as its COUNTS.json names it,
    None) or (None, why it cannot be read): what ties these statistics to the counts of the tree built."""
    try:
        with open(path, encoding="utf-8") as fh:
            commit = json.load(fh).get("commit")
    except (OSError, UnicodeDecodeError, ValueError, AttributeError) as e:
        return None, f"{path} could not be read: {e}"
    return (commit, None) if isinstance(commit, str) and commit else (None, f"{path} names no commit")


def lakefile_roots(path="lakefile.toml"):
    """The roots of the lakefile's lean_lib, or None when they cannot be read."""
    try:
        with open(path, encoding="utf-8") as fh:
            m = ROOTS.search(fh.read())
    except (OSError, UnicodeDecodeError):
        return None
    return re.findall(r'"([^"]+)"', m.group(1)) if m else None


def clock(seconds):
    """h:mm:ss, to the nearest second, a half second rounded up."""
    s = int(seconds + 0.5)
    return f"{s // 3600}:{s // 60 % 60:02d}:{s % 60:02d}"


def disk_figures(build=".lake/build", packages=".lake/packages"):
    """[(what, bytes or None, entries not read)]: each directory alone, and both together, so that a
    file hard-linked from one into the other is counted once, as du counts it."""
    out = [(p, *allocated(p)) for p in (build, packages)]
    both = allocated(build, packages)
    return out + ([("both", *both)] if both[0] is not None else [])


def measured(figure, source, shown=str):
    """A figure and where it came from, or "not measured" and why (`source` says which)."""
    return shown(figure) + ", from " + source if figure else "not measured: " + source


def stats_text(m):
    """The statistics file, from the measurements `m` (a dict; see main and gather)."""
    cpu = m["user"] + m["system_time"]
    commit, commit_why = m["commit"]
    exported, exported_why = m["exported"]
    version, version_why = m["version"]
    out = ["# receipts/build-stats.txt, written by scripts/measure_build.py from one run's own "
           "measurements; nothing in it is typed by hand.",
           "commit: " + (commit or "not measured: git rev-parse HEAD " + str(commit_why)),
           "exported from: " + (exported + ", the commit receipts/COUNTS.json names" if exported else
                                "not measured: " + str(exported_why)),
           "local changes: " + m["changes"],
           "toolchain: " + (m["toolchain"] or "not measured: lean-toolchain could not be read")
           + "; lean --version: " + (version or "not measured: lake env lean --version " + str(version_why)),
           "LEAN_NUM_THREADS: " + (m["threads"] if m["threads"] is not None else "unset"),
           "machine: " + m["system"],
           "logical CPUs: " + measured(*m["cpus"]),
           "memory: " + measured(*m["memory"], shown=show_bytes),
           "commands: " + "; ".join("lake " + " ".join(c) for c in m["ran"]),
           "lake exit status: " + m["status_text"]
           + ("" if m["status_text"] == "0" else " (from: lake " + " ".join(m["ran"][-1]) + ")"),
           f"wall clock: {m['wall']:.1f} s ({clock(m['wall'])}), from the first lake command's start "
           f"to the last one's end",
           f"CPU time: {cpu:.1f} s = {cpu / 3600:.2f} CPU-hours (user {m['user']:.1f} s + system "
           f"{m['system_time']:.1f} s), of lake and every process it waited for",
           "largest single process, peak resident memory: "
           + (show_bytes(m["peak"]) + ", the largest of lake and every process it waited for "
              "(wait4's ru_maxrss: KiB on Linux, bytes on macOS)" if m["peak"] is not None else
              f"not measured: wait4's ru_maxrss has no known unit on {sys.platform}"),
           f'Lake "Built" lines: {len(m["built"])}, each "<mark> [<i>/<n>] Built <name>" in Lake\'s '
           f"output ({m['log']}): one per job Lake ran to completion, whatever its mark"]
    roots = m["roots"]
    if roots is None:
        out.append("lakefile roots: not measured: lakefile.toml's roots could not be read")
    else:
        names = set(m["built"])
        missing = [r for r in roots if r not in names]
        out.append(f'lakefile roots: {len(roots)}; with a "Built" line: {len(roots) - len(missing)}; '
                   f"without one: {len(missing)}" + (" -- " + ", ".join(missing) if missing else ""))
        others = sorted(names - set(roots))
        out.append(f'"Built" names that are not roots: {len(others)}'
                   + (" -- " + ", ".join(others) if others else ""))
    s = m["sampler"]
    head = (f"lean processes below lake, sampled with ps every {s.interval:g} s (resident memory, "
            f"which ps reports in KiB): ")
    if not s.read:
        out.append(head + "not measured: " + (s.why or "no sample was taken"))
    else:
        out.append(head + f"{s.read} samples read, {s.unreadable} unreadable"
                   + (f" ({s.why})" if s.unreadable else ""))
        none = f"none recognised in the {s.read} samples read"
        top = sorted(s.peaks.items(), key=lambda kv: (-kv[1], kv[0][1] or ""))[:10]
        out.append("most lean processes running at once (sampled): " + (str(s.most) if s.most else none))
        out.append("largest sum of resident memory over the lean processes running at once (sampled): "
                   + (show_bytes(s.largest_sum * PS_RSS_UNIT) if s.most else none))
        if not top:
            out.append("the lean processes with the largest sampled peak resident memory: " + none)
        else:
            out.append(f"the {len(top)} lean processes with the largest sampled peak resident memory, each "
                       "with the module it was compiling:")
        for i, ((_pid, module), kib) in enumerate(top, 1):
            out.append(f"  {i}. {show_bytes(kib * PS_RSS_UNIT)} "
                       + (module or "not measured: its command line never named a source file"))
    out.append("disk after the build, as du counts it (st_blocks x 512, a file with several hard links once): "
               + "; ".join(what + " " + (show_bytes(b) if b is not None else "not present")
                           + (f" ({unread} entries could not be read)" if unread else "")
                           for what, b, unread in m["disk"]))
    return "\n".join(out) + "\n"


def too_old(version):
    """Whether the Python `version` (its first two numbers) is older than this script needs."""
    return tuple(version[:2]) < MIN_PYTHON


def gather(a, m, sampler):
    """What stats_text reads: the builds' measurements `m`, and what is read once they are over."""
    commit, commit_why = command("git", "rev-parse", "HEAD")
    if commit is None:
        changes = "not measured: there is no commit to compare with"
    else:
        changed, changed_why = command("git", "status", "--porcelain", "--untracked-files=no")
        n = None if changed is None else len(changed.splitlines())
        changes = ("not measured: git status " + changed_why if n is None else "none to tracked files" if n == 0
                   else f"{n} tracked file{'' if n == 1 else 's'} differ{'s' if n == 1 else ''} from the commit")
    try:
        with open("lean-toolchain", encoding="utf-8") as fh:
            toolchain = fh.read().strip()
    except (OSError, UnicodeDecodeError):
        toolchain = None
    return dict(m, commit=(commit, commit_why), exported=exported_from(), changes=changes, toolchain=toolchain,
                version=command("lake", "env", "lean", "--version"), threads=os.environ.get("LEAN_NUM_THREADS"),
                system=f"{platform.system()} {platform.machine()}", cpus=machine_cpus(), memory=machine_memory(),
                peak=ru_maxrss_bytes(m["peak"]), log=a.log, roots=lakefile_roots(), sampler=sampler,
                disk=disk_figures())


def keep_measured(path, m, sampler, error, t0):
    """Before `error` propagates out of a run in which lake ran: write what the run had measured, as
    it stands, to `path` (to stderr when that cannot be written), so that the script's own failure
    does not lose a multi-hour build's figures. The file says that it is not the statistics file."""
    wall = m["wall"] if m["wall"] is not None else time.monotonic() - t0
    unit = {"linux": "KiB", "darwin": "bytes"}.get(platform_key(), "a unit not known here")
    text = (f"# receipts/build-stats.txt, written by scripts/measure_build.py, which FAILED "
            f"({type(error).__name__}: {error}) before it could write this file in full. What it had "
            f"measured, as it stands; this is not the statistics file.\n"
            f"commands run: {'; '.join('lake ' + ' '.join(c) for c in m['ran'])}\n"
            f"lake's exit status, as measured: {m['status_text']}\n"
            f"seconds from the first lake command's start, as measured: {wall:.1f}\n"
            f"CPU seconds of lake and every process it waited for, as measured: user {m['user']:.1f}, "
            f"system {m['system_time']:.1f}\n"
            f"the largest ru_maxrss wait4 gave, in its unit here ({unit}): {m['peak']}\n"
            f"Lake \"Built\" lines: {len(m['built'])}\n"
            f"process table: {sampler.read} samples read, {sampler.unreadable} unreadable; most lean processes "
            f"at once {sampler.most}; largest sum {sampler.largest_sum} KiB\n")
    try:
        os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
        with open(path, "w", encoding="utf-8") as fh:
            fh.write(text)
    except OSError:
        sys.stderr.write(text)


def main(argv=None, version=None):
    for name in GIT_LOCATION_VARS:              # first: lake and every git below find the tree's own
        os.environ.pop(name, None)
    version = version or sys.version_info
    if too_old(version):
        print(f"measure_build.py needs Python {MIN_PYTHON[0]}.{MIN_PYTHON[1]} or later, and this is "
              f"{'.'.join(map(str, version[:3]))}: nothing was built", file=sys.stderr)
        return 2
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0],
                                 formatter_class=argparse.RawDescriptionHelpFormatter,
                                 epilog=__doc__.split("\n\n", 2)[2])
    ap.add_argument("--first", nargs="+", metavar="MODULE", default=[], help=FIRST_HELP)
    ap.add_argument("--target", default="Zeta2", help="the Lake target built last (default: Zeta2)")
    ap.add_argument("--out", default="receipts/build-stats.txt", help="the statistics file to write")
    ap.add_argument("--log", default="build.log", help="where Lake's output is copied")
    ap.add_argument("--sample-interval", type=float, default=1.0, metavar="SECONDS",
                    help="seconds between two reads of the process table (default: 1)")
    a = ap.parse_args(argv)
    os.chdir(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    sampler = Sampler(a.sample_interval)
    m = {"ran": [], "built": [], "status": 0, "status_text": "0", "user": 0.0, "system_time": 0.0,
         "peak": 0, "wall": None, "lake ran": False}
    sampler.start()
    t0 = time.monotonic()
    try:
        with open(a.log, "w", encoding="utf-8") as log:
            for args in [["build", mod] for mod in a.first] + [["build", a.target]]:
                m["ran"].append(args)
                try:
                    status, usage, names = run_lake(args, log, sampler)
                except OSError as e:
                    if m["lake ran"]:
                        raise
                    sampler.stop()
                    print(f"measure_build.py: cannot run lake: {e}", file=sys.stderr)
                    return 2
                m["lake ran"] = True
                m["user"] += usage.ru_utime
                m["system_time"] += usage.ru_stime
                m["peak"] = max(m["peak"], usage.ru_maxrss)
                m["built"] += names
                m["status"], m["status_text"] = lake_status(status)
                if m["status"] != 0:
                    break
        m["wall"] = time.monotonic() - t0
        sampler.stop()
        text = stats_text(gather(a, m, sampler))
    except BaseException as e:
        sampler.stop()
        if m["lake ran"]:
            keep_measured(a.out, m, sampler, e, t0)
        raise
    os.makedirs(os.path.dirname(a.out) or ".", exist_ok=True)
    with open(a.out, "w", encoding="utf-8") as fh:
        fh.write(text)
    sys.stdout.write(text)
    return m["status"]


if __name__ == "__main__":
    sys.exit(main())
