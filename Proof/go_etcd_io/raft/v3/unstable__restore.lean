/- Port of election_proof/proof_unstable__restore.v. -/
module

public import Spec.go_etcd_io.raft.v3.unstable__restore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- Straight-line: five field stores, the last of which installs the address of the
parameter's own cell. That cell is persisted, which is what `ownSnap` holds. -/
theorem unstable.restore.wp_proof : unstable.restore.spec (GF := GF) (hG := hG) := by
  intro u us sv voters
  wp_start as H
  iNamed H
  iunfold ownUnstable at Hun
  iNamed Hun
  iapply wp_fupd
  wp_auto
  ipersist s
  imodintro
  iapply HΦ
  iapply ownUnstable_intro $$ Hu
  · iapply ownSliceCap_nil
  · iapply ownSlice_nil
  · iapply (ownSnap_Some _ _).2
    iexists sv
    iframe s
    isplitl []
    · ipureintro; exact ⟨rfl, rfl⟩
    iexists voters
    iexact Hvoters
  · iexact Hlogger
  · ipureintro; exact ⟨rfl, rfl⟩

end proof

end EtcdGrove
end Perennial
