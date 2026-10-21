/-
`NewWitness` (raft#168, `witness.go`; 2026-10-20, witness support, W3b).
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvWitnessStorage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `NewWitness(cfg)`: a fresh `*witness` (as a `Witness`) of `cfg`'s id, storage and options,
its cache nil (the zero state, which every storage state is at least) and no error. -/
abbrev NewWitness.spec : Prop :=
  ∀ (cfg : WitnessConfig),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }}
    (App (Val #(functions NewWitness [])) (Val #cfg))
  {{ (w : Loc), RET #(interface.mkOk (go.GoType.PointerType witness.ty) #w);
      ownWitness w cfg.ID' cfg.Storage' cfg.CheckQuorum' cfg.PreVote' WHS.zero true }}

end spec

end EtcdGrove
end Perennial
