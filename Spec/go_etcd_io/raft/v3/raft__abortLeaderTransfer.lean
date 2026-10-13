/- Port of election_proof/spec_raft__abortLeaderTransfer.v (feb5c73d4). -/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

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

/-- `abortLeaderTransfer` clears `leadTransferee` (`NState.lt`, tracked since 2026-10-13;
until then `ownRaftPhys` pinned it to zero). -/
abbrev raft.abortLeaderTransfer.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"abortLeaderTransfer")) (Val #()))
  {{ RET #(); ownRaftPhysCV c c.voters r id { s with lt := W64 0 } }}

/-- The statement on `ownRaftPhys` (the simple configuration `cfg`) until 2026-10-13,
derived from `raft.abortLeaderTransfer.spec` by `raft.abortLeaderTransfer.spec_simple`. -/
abbrev raft.abortLeaderTransfer.specS : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"abortLeaderTransfer")) (Val #()))
  {{ RET #(); ownRaftPhys cfg r id { s with lt := W64 0 } }}

open Iris.ProofMode in
theorem raft.abortLeaderTransfer.spec_simple
    (H : raft.abortLeaderTransfer.spec (GF := GF) (hG := hG)) :
    raft.abortLeaderTransfer.specS (GF := GF) (hG := hG) := by
  intro cfg r id s
  iintro %Φ ⟨#Hpkg, Hphys⟩ HΦ
  ihave Hphys := ownRaftPhys_toC' $$ Hphys
  iapply H $$ [$Hpkg $Hphys]
  inext
  iintro Hphys
  iapply HΦ $$ [Hphys]
  iapply ownRaftPhysC_toS $$ Hphys

end spec

end EtcdGrove
end Perennial
