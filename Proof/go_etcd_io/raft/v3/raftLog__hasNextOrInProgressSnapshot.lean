/- Port of election_proof/proof_raftLog__hasNextOrInProgressSnapshot.v. -/
module

public import Spec.go_etcd_io.raft.v3.raftLog__hasNextOrInProgressSnapshot

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

theorem raftLog.hasNextOrInProgressSnapshot.wp_proof :
    raftLog.hasNextOrInProgressSnapshot.spec (GF := GF) (hG := hG) := by
  intro l ls
  wp_start as Hlog
  iNamed Hlog
  wp_auto
  cases Hs : ls.snap with
  | some sid =>
    ihave Hus := (ownSnap_Some _ sid).1 $$ Husnap
    icases Hus with ⟨%sv, #Hsv, -⟩
    ihave %Hnn := typedPointsto_not_null $$ Hsv
    rw [decide_eq_false Hnn]
    iapply HΦ
    isplitl
    · reseal_raftLog
    · ipureintro; simp
  | none =>
    ihave %Hnosnap := (ownSnap_None _).1 $$ Husnap
    rw [decide_eq_true Hnosnap]
    iapply HΦ
    isplitl
    · reseal_raftLog
    · ipureintro; simp

end proof

end EtcdGrove
end Perennial
