/-
Port of election_proof/proof_raft__sendAppend.v.
-/
import EtcdGrove.Raft.Spec.raft__sendAppend
import EtcdGrove.Raft.Spec.raft__maybeSendAppend

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem raft.sendAppend.wp_proof
    (wp_raft_maybeSendAppend : raft.maybeSendAppend.spec (GF := GF) (hG := hG)) :
    raft.sendAppend.spec (GF := GF) (hG := hG) := by
  intro cfg r id s to Hto Hcfg
  wp_start as Hphys
  wp_auto
  wp_apply wp_raft_maybeSendAppend cfg r id s to true Hto Hcfg $$ [$Hphys]
    as %b %ms %pvs ⟨Hphys, %Hms, %Hmm⟩
  iapply HΦ
  iframe
  ipureintro
  exact ⟨Hms, Hmm⟩

end proof

end EtcdGrove
end Perennial
