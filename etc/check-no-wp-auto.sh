#!/bin/bash
# Branch `no-wp-auto`: fail if a proof uses `wp_auto`/`wp_auto_lc` (outside comments)
# or still carries a `TODO(no-wp-auto)` from the mechanical conversion.
# `EtcdGrove/NoWpAuto.lean` makes an explicit `wp_auto` an error and the implicit one a
# no-op; this also catches `wp_auto_lc 0`, which that module turns into a silent no-op.
cd "$(dirname "$0")/.." || exit 2
hits=$(grep -rnE '\bwp_auto(_lc)?\b' EtcdGrove --include='*.lean' \
  | grep -v '^EtcdGrove/NoWpAuto.lean:' \
  | grep -vE '^[^:]+:[0-9]+:\s*--' \
  | grep -vE '`[^`]*wp_auto[^`]*`' )
todos=$(grep -rn 'TODO(no-wp-auto)' EtcdGrove --include='*.lean')
status=0
if [ -n "$hits" ]; then echo "wp_auto in proofs:"; echo "$hits"; status=1; fi
if [ -n "$todos" ]; then echo "unresolved conversion TODOs:"; echo "$todos"; status=1; fi
exit $status
