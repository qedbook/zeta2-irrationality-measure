#!/bin/sh
# Every generated STAR module in src/ must match the sha256 in the committed manifests.
set -eu
cd "$(dirname "$0")/../.."
bad=0; n=0
for man in generators/star/modules/MANIFEST-cand-t1-kernel.sha256 generators/star/modules/MANIFEST-cand-t2-kernel.sha256; do
  while read -r h f rest; do
    case "$h" in [0-9a-f]*) ;; *) continue ;; esac
    [ ${#h} -eq 64 ] || continue
    n=$((n+1))
    got=$(sha256sum < "src/$f" | cut -d' ' -f1)
    [ "$got" = "$h" ] || { echo "MISMATCH $f"; bad=$((bad+1)); }
  done < "$man"
done
echo "checked $n generated modules, $bad mismatch(es)"
[ "$bad" -eq 0 ]
