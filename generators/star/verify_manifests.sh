#!/bin/sh
# Check every generated STAR module in src/ against the sha256 its committed manifest records.
#
# Needs a sha256sum or a shasum on PATH: it uses sha256sum when there is one, and `shasum -a 256`
# otherwise. With neither it stops with exit 2 and says so, instead of reporting every module as a
# mismatch. A manifest entry is a line whose first word is 64 lower-case hexadecimal digits, as
# sha256sum and shasum print a digest. A line whose first word is 64 hexadecimal digits with an
# upper-case one among them is reported UNREADABLE and fails the check, since the module it lists
# would otherwise be checked by nothing; every other line (a comment, a shorter word) is skipped.
# Exit 0 only when every module a manifest lists is present and matches, and no line is unreadable.
# POSIX sh: it runs the same under dash, bash and macOS's /bin/sh.
set -eu
case "$0" in
  */*) cd "${0%/*}/../.." ;;
  *) cd ../.. ;;
esac
if command -v sha256sum >/dev/null 2>&1; then
  digest() { sha256sum < "$1"; }
elif command -v shasum >/dev/null 2>&1; then
  digest() { shasum -a 256 < "$1"; }
else
  echo "verify_manifests.sh: no sha256 tool: put a sha256sum or a shasum on PATH; nothing was checked" >&2
  exit 2
fi
bad=0
unread=0
n=0
for man in generators/star/modules/MANIFEST-cand-t1-kernel.sha256 generators/star/modules/MANIFEST-cand-t2-kernel.sha256; do
  while read -r h f rest; do
    case "$h" in
      ''|*[!0123456789abcdefABCDEF]*) continue ;;
      *[ABCDEF]*)
        if [ ${#h} -eq 64 ]; then
          echo "UNREADABLE $man: the digest $h has upper-case hexadecimal digits, and an entry is read in lower case"
          unread=$((unread + 1))
        fi
        continue ;;
    esac
    [ ${#h} -eq 64 ] || continue
    n=$((n + 1))
    if [ ! -f "src/$f" ]; then
      echo "MISSING $f"
      bad=$((bad + 1))
      continue
    fi
    got=$(digest "src/$f")
    got=${got%% *}
    if [ "$got" != "$h" ]; then
      echo "MISMATCH $f"
      bad=$((bad + 1))
    fi
  done < "$man"
done
echo "checked $n generated modules against the two manifests: $bad missing or mismatched"
if [ "$unread" -ne 0 ]; then
  echo "verify_manifests.sh: $unread manifest line(s) UNREADABLE, so the modules they list were not checked"
fi
[ "$bad" -eq 0 ] && [ "$unread" -eq 0 ]
