/-
## `(*unstable).stableTo` (internal)

The embedded `unstable` of a `raftLog` (`raftLog`'s realization holds `unstable` of its field).
Users: `raftLog`'s methods only. Mirrors the code over `UnstableState`.
**Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/unstable__stableTo.lean`: over `UnstableState`.
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

/-- (internal) Drop the entries through `id` if it is an unstable entry of its term. -/
def unstable.stableTo.spec : Prop :=
  ∀ (u : Loc) (us : UnstableState) (id : go_etcd_io.raft.v3.entryID),
  us.Wf →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ unstable u us }}
    (App (Val (u @!! go.GoType.PointerType go_etcd_io.raft.v3.unstable.ty @!! go!"stableTo")) (Val #id))
  {{ RET #(); unstable u (us.stableTo (uint.nat id.index') id.term') }}

end spec
end Raft
end EtcdGrove
end Perennial
