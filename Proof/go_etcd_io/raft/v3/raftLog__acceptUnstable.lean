/- Port of election_proof/proof_raftLog__acceptUnstable.v (857d09190). -/
module

public import Spec.go_etcd_io.raft.v3.raftLog__acceptUnstable
public import Spec.go_etcd_io.raft.v3.unstable__acceptInProgress

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

theorem raftLog.acceptUnstable.wp_proof
    (wp_unstable_acceptInProgress : unstable.acceptInProgress.spec (GF := GF) (hG := hG)) :
    raftLog.acceptUnstable.spec (GF := GF) (hG := hG) := by
  intro l ls Hpend
  wp_start as H
  iNamed H
  iNamed Hlog
  wp_auto
  have Hcontig : ∀ (k : Nat) (e : raftpb.Entry), ls.uents[k]? = some e →
      uint.Z e.Index' = uint.Z lv.unstable'.offset' + (k : Int) := by
    intro k e Hk
    have Hk' : (ls.sents ++ ls.uents)[ls.sents.length + k]? = some e := by
      rw [List.getElem?_append_right (by omega)]
      simpa using Hk
    have := Hidx _ _ Hk'
    push_cast at this
    omega
  have Hnw' : uint.Z lv.unstable'.offset' + (ls.uents.length : Int) < 2^64 := by omega
  lend_unstable
  wp_apply wp_unstable_acceptInProgress _ (unstableOf lv ls) Hcontig Hnw' $$ [$Hun]
    as %nip ⟨Hun, %Hnip⟩
  obtain ⟨Hip0, Hip1⟩ := Hnip
  iclear Husnap Hu_logger
  icases ownUnstable_reopen _ _ _ $$ Hlback Hun
    with ⟨%uv', Hl, Huents_cap, Huents, #Husnap, #Hu_logger, %Huoff, %Hipv⟩
  iapply HΦ
  -- the new `offsetInProgress` is the end of the log
  have Hend : uint.Z uv'.offsetInProgress'
      = uint.Z lv.unstable'.offset' + (ls.uents.length : Int) := by
    by_cases He : ls.uents = []
    · have H0 := Hip0 He
      simp only [He, List.length_nil] at Hipb ⊢
      word
    · have H1 := Hip1 He
      word
  unfold logAcceptUnstable
  reseal_raftLog
  · simp only [logEnd, logLast]; word
  · simp only [logEnd, logLast]; word
  · intro Hs
    obtain ⟨Hsp, -, -⟩ : LogStoreOk none σ ls.prev ls.sents ls.uents := Hs ▸ Hstore
    have Hp := Hpersist Hs
    have Hipo : uint.Z (logEnd ls) - uint.Z uv'.offset' = (ls.uents.length : Int) := by
      simp only [logEnd, logLast]; word
    simp only [Hipo, nextUnstable, logOffset, ← Hoffset]
    exact persist_accept ls.prev σ ls.sents ls.uents _ Hidx Hsp (by omega) ls.stored (Hpend ▸ Hp)

end proof

end EtcdGrove
end Perennial
