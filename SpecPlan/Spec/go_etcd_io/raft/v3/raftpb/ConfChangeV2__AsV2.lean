/-
`(*ConfChangeV2).AsV2` (`raftpb/confchange.go:75`): the identity.

Users: as `ConfChange.AsV2` (through `ConfChangeI.AsV2`), `MarshalConfChange`.
Proof sketch: returns its receiver. Changes: from `specs-ref/.../raftpb/ConfChangeV2__AsV2.lean`:
no predicate needed. Margin: none.
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

/-- `p.AsV2()` returns `p` (any `p`). -/
def ConfChangeV2.AsV2.spec : Prop :=
  ∀ (p : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb }}
    (App (Val (p @!! go.GoType.PointerType raftpb.ConfChangeV2.ty @!! go!"AsV2")) (Val #()))
  {{ RET #p; True }}

end spec

end RaftPb
end EtcdGrove
end Perennial
