/-
## `(*unstable).maybeTerm` (internal)

The embedded `unstable` of a `raftLog` (`raftLog`'s realization holds `unstable` of its field).
Users: `raftLog`'s methods only. Mirrors the code over `UnstableState`. `us.Wf` excludes the out-of-range index when there are no entries and the snapshot is at or past
`offset`.
**Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/unstable__maybeTerm.lean`: over `UnstableState`.
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

/-- (internal) The term of `i` if the unstable part has it. -/
def unstable.maybeTerm.spec : Prop :=
  ∀ (u : Loc) (us : UnstableState) (i : w64),
  us.Wf →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ unstable u us }}
    (App (Val (u @!! go.GoType.PointerType go_etcd_io.raft.v3.unstable.ty @!! go!"maybeTerm")) (Val #i))
  {{ (t : w64) (ok : Bool), RET (PairV #t #ok); unstable u us ∗
      ⌜(ok = true ∧ us.maybeTerm (uint.nat i) = some t) ∨
       (ok = false ∧ us.maybeTerm (uint.nat i) = none ∧ t = W64 0)⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
