# lease-mono3 step 2: handoff

Branch `lease-mono3-s2` (off `lean` `89ef103d5b`), worktree `/shared/etcd-grove-auth3`.

- Done: Scope (approved by etcd-grove-81, `questions.md`); Go tests; the Lean change, full build green;
  Freeze package (`notes/lease-mono3-plan.md`, "Step 2 Freeze package") at etcd-grove-81 (hard stop 2).
- Next: review fixes; then merge `lean`, rebuild, `etc/land.sh` only after 81's go (hard stop 3).
- Build: `flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G lake build
  --packages=/shared/tmp/manifest-ddc.json` (a `KVNames` change rebuilds ~1600 modules, ~15 min).
  Go tests: `systemd-run --scope -q -p MemoryMax=32G`, `GOWORK=off`; `TestGrantEveryMember` one run per
  process (`go test -c`, then a loop).
- Pitfalls: positional `KVNames` literals (grep `, .none⟩` / `γk.lm⟩`); `List.nodup_singleton` does not
  exist here (`by simp`); a `pgrep -f` wait loop whose pattern is in its own command line never ends.
