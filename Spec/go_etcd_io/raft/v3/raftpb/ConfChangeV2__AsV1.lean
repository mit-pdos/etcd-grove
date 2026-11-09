/-
`(*ConfChangeV2).AsV1` (`raftpb/confchange.go:78`): `nil` and `false`.

Users: `MarshalConfChange`, etcd's `applyConfChange`.
Proof sketch: returns constants. Changes: from `specs-ref/.../raftpb/ConfChangeV2__AsV1.lean`:
unchanged. Margin: none.
-/
module

public import Spec.go_etcd_io.raft.v3.raftpb.Api

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

/-- `p.AsV1()` returns `(nil, false)` (any `p`). -/
def ConfChangeV2.AsV1.spec : Prop :=
  ∀ (p : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb }}
    (App (Val (p @!! go.GoType.PointerType raftpb.ConfChangeV2.ty @!! go!"AsV1")) (Val #()))
  {{ RET (PairV #(null : Loc) #false); True }}

end spec

end RaftPb
end EtcdGrove
end Perennial
