#!/bin/sh
# Build the whole proof, elaborate src/Receipts.lean, and check what it prints.
#
# Writes receipts/local-run.txt, a new file stamped with the commit and the toolchain it ran at,
# holding everything lean printed and the exit status lean returned. It removes the file a
# previous run left before it starts, so that a run that fails before writing leaves none. The
# committed receipt, receipts/this-machine.txt, is left as it is, to compare with. Exit 0 only when
# the build succeeds, lean exits 0, and scripts/check_receipts.py finds the output clean.
# Before anything else it unsets git's location variables (GIT_DIR and the others on its unset
# line), so that git, and lake's own git calls on its packages, find the repository from this
# tree's directory and not from whatever repository the calling environment names.
# POSIX sh: it runs the same under dash, bash and macOS's /bin/sh.
set -eu
unset GIT_DIR GIT_WORK_TREE GIT_COMMON_DIR GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES GIT_NAMESPACE GIT_CONFIG GIT_CONFIG_PARAMETERS GIT_CONFIG_COUNT GIT_IMPLICIT_WORK_TREE GIT_GRAFT_FILE GIT_NO_REPLACE_OBJECTS GIT_REPLACE_REF_BASE GIT_PREFIX GIT_SHALLOW_FILE
case "$0" in
  */*) cd "${0%/*}/.." ;;
  *) cd .. ;;
esac
out=receipts/local-run.txt
rm -f "$out"
lake exe cache get
lake build Zeta2
if commit=$(git rev-parse HEAD 2>/dev/null); then
  if [ -n "$(git status --porcelain --untracked-files=no 2>/dev/null)" ]; then
    commit="$commit, with local changes to tracked files"
  fi
else
  commit="not recorded: this is not a git checkout"
fi
toolchain=$(cat lean-toolchain)
version=$(lake env lean --version 2>&1) || version="not recorded: lake env lean --version failed"
nl='
'
version=${version%%"$nl"*}
{
  echo "# scripts/verify.sh, commit: $commit"
  echo "# toolchain: $toolchain; lean --version: $version"
} > "$out"
status=0
lake env lean src/Receipts.lean >> "$out" 2>&1 || status=$?
echo "# lean exit status: $status" >> "$out"
cat "$out"
verdict=0
python3 scripts/check_receipts.py "$out" || verdict=1
if [ "$status" -ne 0 ]; then
  echo "verify.sh: FAILED: lean exited with status $status on src/Receipts.lean"
  verdict=1
fi
echo "verify.sh: this run's output is $out; the committed receipt, which this script never writes, is receipts/this-machine.txt"
exit "$verdict"
