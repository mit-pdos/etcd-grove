/-
## `(*unstable).truncateAndAppend` (internal)

The embedded `unstable` of a `raftLog` (`raftLog`'s realization holds `unstable` of its field).
Users: `raftLog`'s methods only. Mirrors the code over `UnstableState`. The slice `es` is kept by reference when it replaces the entries (`u.entries = ents`), read-only.
**Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/unstable__truncateAndAppend.lean`: over `UnstableState`.
-/
module

public import Spec.go_etcd_io.raft.v3.ApiLog

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Raft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (internal) Append `es` at `k`, truncating after `k - 1`. -/
def unstable.truncateAndAppend.spec : Prop :=
  ∀ (u : Loc) (us : UnstableState) (sl : GoSlice) (k : Nat) (es : List LogEntry),
  us.Wf → es ≠ [] → 1 ≤ k → k ≤ us.offset + us.ents.length → k + es.length < 2 ^ 64 →
  (∀ s, us.snap = some s → uint.nat s.index < k) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ unstable u us ∗ entriesRO sl k es }}
    (App (Val (u @!! go.GoType.PointerType go_etcd_io.raft.v3.unstable.ty @!! go!"truncateAndAppend")) (Val #sl))
  {{ RET #(); unstable u (us.truncateAndAppend k es) }}

end spec
end Raft
end EtcdGrove
end Perennial
