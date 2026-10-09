/- Lean-first (no Rocq counterpart). -/
module

public import Proof.go_etcd_io.raft.v3.InvRawnode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `r.softState()`: `SoftState{Lead: r.lead, RaftState: r.state}`. -/
abbrev raft.softState.spec : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState),
  {{ ownRaftPhys (GF := GF) cfg r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"softState")) (Val #()))
  {{ RET #(softstateVal (nodeSoftstate s)); ownRaftPhys cfg r id s }}

end spec

end EtcdGrove
end Perennial
