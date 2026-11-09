/-
## `(*unstable).maybeLastIndex` (internal)

The embedded `unstable` of a `raftLog` (`raftLog`'s realization holds `unstable` of its field).
Users: `raftLog`'s methods only. Mirrors the code over `UnstableState`.
**Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/unstable__maybeLastIndex.lean`: over `UnstableState`.
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

/-- (internal) The last unstable entry's index, else the pending snapshot's, if any. -/
def unstable.maybeLastIndex.spec : Prop :=
  ∀ (u : Loc) (us : UnstableState),
  us.Wf →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ unstable u us }}
    (App (Val (u @!! go.GoType.PointerType go_etcd_io.raft.v3.unstable.ty @!! go!"maybeLastIndex")) (Val #()))
  {{ (i : w64) (ok : Bool), RET (PairV #i #ok); unstable u us ∗
      ⌜(ok = true ∧ us.maybeLastIndex = some (uint.nat i)) ∨
       (ok = false ∧ us.maybeLastIndex = none ∧ i = W64 0)⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
