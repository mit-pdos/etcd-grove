/-
## `(*unstable).nextSnapshot` (internal)

The embedded `unstable` of a `raftLog` (`raftLog`'s realization holds `unstable` of its field).
Users: `raftLog`'s methods only. Mirrors the code over `UnstableState`.
**Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/unstable__nextSnapshot.lean`: over `UnstableState`.
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.ApiLog

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

/-- (internal) A fresh copy of the snapshot if not in progress, else `nil`. -/
def unstable.nextSnapshot.spec : Prop :=
  ∀ (u : Loc) (us : UnstableState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ unstable u us }}
    (App (Val (u @!! go.GoType.PointerType go_etcd_io.raft.v3.unstable.ty @!! go!"nextSnapshot")) (Val #()))
  {{ (sp : Loc), RET #sp; unstable u us ∗
      (match us.nextSnapshot with
       | none => ⌜sp = null⌝
       | some s => snapshotPts sp (DFrac.own 1) s) }}

end spec
end Raft
end EtcdGrove
end Perennial
