/-
`(*ConfChange).AsV1` (`raftpb/confchange.go:70`): the change itself and `true`.

Users: `MarshalConfChange` (this batch), etcd's `applyConfChange` (through `ConfChangeI`).
Proof sketch: returns its receiver. Changes: from `specs-ref/.../raftpb/ConfChange__AsV1.lean`:
no predicate needed (nothing is read). Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.raftpb.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace RaftPb

open Iris Iris.BI
open go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.raftpb.Assumptions]

/-- `p.AsV1()` returns `(p, true)` (any `p`). -/
def ConfChange.AsV1.spec : Prop :=
  ∀ (p : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb }}
    (App (Val (p @!! go.GoType.PointerType raftpb.ConfChange.ty @!! go!"AsV1")) (Val #()))
  {{ RET (PairV #p #true); True }}

end spec

end RaftPb
end EtcdGrove
end Perennial
