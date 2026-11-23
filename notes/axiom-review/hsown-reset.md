# Axiom review: `WalHsOwn.reset` at `walRaftHsO` (`(*raftpb.HardState).Reset`)

- Statement: the field `reset` of `structure WalHsOwn` (`Spec/go_etcd_io/etcd/server/v3/storage/wal/ReadAllCallees.lean:68`),
  passed as `h_reset` to `walRaftHsO_own` (`Proof/.../wal/RaftModel/Laws.lean:83`). It is a hypothesis of
  `etcd_wal_crash_safety_bounded` (field `resetHs` of `TOpen`), at etcd-grove `5688ee668f`:

      ∀ p h, {{ walRaftHsO p h }} p.Reset() {{ RET (); walRaftHsO p hsZero }}

  Here `walRaftHsO p h = hsOwnC p (walHsCanon h)` (`RaftModel/Pb.lean:129`) and `walHsCanon hsZero = walHsC0`
  (all fields nil, `uf = []`). `hsOwnC` includes `p ≠ null`, owns all six fields at 1, and
  existentially quantifies `state`, `sizeCache` and the unknown-fields slice.
- Go: raftpb at raft `d2c16c5`, `raftpb/raft.pb.go:702-707`:
  `*x = HardState{}; mi := &file_raft_proto_msgTypes[4]; ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x)); ms.StoreMessageInfo(mi)`.
  It is names-only in the translation (`Code/go_etcd_io/raft/v3/raftpb.toml`: `!*.Reset`), so this
  hypothesis is its only model in the WAL proof. Callers: `readAll`'s error arms (`state.Reset()`,
  fork `d7c7f6434` `wal.go`).
- Tests: `/shared/tmp/coord-03/review-wal4/probe_test.go` (`TestT4Reset`), go1.27.3, `-race`.

## Verdict: sound

`*x = HardState{}` writes every field: the three pointers become nil, `unknownFields` nil, `sizeCache` 0,
and `state` zero. Then `state` gets the `MessageInfo` pointer (atomic store). The post `hsOwnC p walHsC0`
asks for nil cells (`optCell _ none` is `= null`), owned hidden fields at some `state`/`sizeCache`, and
`us ↦* []` (true at `us = nil`). The existential `st` covers the non-zero `state`. `TestT4Reset` checks
this on a decoded state with an unknown field added. After `Reset`: fields nil, unknown fields gone and
nil, `state` non-zero, the old `Term` cell unchanged (it is frozen `↦□` in the pre and is not written),
and the message marshals to zero bytes.

On ghost ownership: `Reset` writes all six fields, and the pre owns all six at 1. Nothing else holds a
reference: `HsO` comes only from `zero` (a fresh `&raftpb.HardState{}`) or `unmarshal` (a fresh
decode), and turns into the shared form only through `freeze`, after which `reset` no longer applies.
The receiver cannot be nil: `hsOwnC` carries `p ≠ null`, and Go's nil `Reset` panics
(`TestT4Reset`: `invalid memory address or nil pointer dereference`).

**Suggestion (not a soundness fix):** treat `(*raftpb.HardState).Reset` like `(*walpb.Record).Reset`.
Give it a TrustedCode model (store `zero_val`, with a docstring saying why leaving out the
message-state store is faithful) and prove this triple from it. The trusted statement then becomes a
one-line model of Go instead of a hypothesis about an opaque call. If that is done, note the
Record-review caveat: the model's `state` would be zero where Go's is not. That is harmless here,
because `hsOwnC` existentially quantifies `state`.

## Attacks tried, and why each failed

| # | Claim attacked | Attack | Result / why it fails |
|---|---|---|---|
| 1 | Unknown fields cleared | Reset a state carrying unknown field 9 | `unknownFields` is nil afterwards, so `us ↦* []` holds. |
| 2 | Internal state | Inspect `state` after Reset (reflection) | Non-zero (`MessageInfo` stored). The post's `∃ st` allows it. |
| 3 | Old cells | Reset, then read the old `Term` cell | Unchanged. The pre gives it frozen and the post forgets it; Go does not write it. |
| 4 | nil receiver | `(*HardState)(nil).Reset()` panics | Excluded: `hsOwnC`'s `p ≠ null`. |
| 5 | Shared object (ownership too strong) | Could a reset hard state still be visible to another holder (a frozen `hsIn` or `w.state`)? | `HsO` is exclusive. The freeze is one-way, and `w.state` is a `Clone` (fresh). `readAll` resets only the local `state`, before any freeze. |
| 6 | Cross-world pattern | — | A triple; no entailment over persistent cells. |

## Follow-up (2026-11-22, the user's approval)

Done as suggested: `(*raftpb.HardState).Reset` is trusted (`Code/go_etcd_io/raft/v3/raftpb.toml`'s `trusted`),
its model `HardState.Reset.impl` (`TrustedCode/go_etcd_io/raft/v3/raftpb.lean`, the store of the zero value, the
message-state store left out, as `walpb`'s `Record.Reset.impl`), and the law is proved from it
(`walRaftHsO_reset`, `Proof/go_etcd_io/etcd/server/v3/storage/wal/RaftModel/LawsHsReset.lean`). `resetHs` is gone
from the tester's `TOpen`. (The probe test is `/shared/tmp/coord-03/review-wal4/probe_test.go`, not kept in the
repository.)
