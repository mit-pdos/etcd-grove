/- Port of election_proof/proof_raftLog__acceptUnstable.v (857d09190).

Since 2026-10-10 the proof also runs the storage's hand-out law (`isStorage`'s
`Hhandout`, `InvStorage.lean`) for the entries handed out, before the call (a ghost
update, so while the goal is still a `WP`): the storage's pending batch becomes
`nextUnstable ls`, and the right to append it is the postcondition's `appendRight`. -/
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
  intro l ls Hunp0 Hs0
  wp_start as H
  iNamed H
  iNamed Hlog
  simp only [logHanded] at *
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
  -- the batch handed out (2026-10-10): `uents` from `offsetInProgress` on, which starts
  -- above the storage's boundary and at most one past what it holds (`LogPersistOk`)
  obtain ⟨Hsp, -, -⟩ : LogStoreOk none σ ls.prev ls.sents ls.uents := Hs0 ▸ Hstore
  have Hp0 := Hpersist Hs0
  have Hhead : ∀ e0, (nextUnstable ls).head? = some e0 →
      uint.Z e0.Index' = uint.Z ls.inprogress ∧
      uint.Z ls.inprogress - uint.Z lv.unstable'.offset' < (ls.uents.length : Int) := by
    intro e0 He0
    simp only [nextUnstable, List.head?_drop] at He0
    have Hlt := (List.getElem?_eq_some_iff.1 He0).1
    have Hc := Hcontig _ _ He0
    simp only [logOffset] at Hc Hlt
    constructor <;> omega
  lend_unstable
  wp_apply wp_unstable_acceptInProgress _ (unstableOf lv ls) Hcontig Hnw' $$ [$Hun]
    as %nip ⟨Hun, %Hnip⟩
  obtain ⟨Hip0, Hip1⟩ := Hnip
  iclear Husnap Hu_logger
  icases ownUnstable_reopen _ _ _ $$ Hlback Hun
    with ⟨%uv', Hl, Huents_cap, Huents, #Husnap, #Hu_logger, %Huoff, %Hipv⟩
  -- the new `offsetInProgress` is the end of the log
  have Hend : uint.Z uv'.offsetInProgress'
      = uint.Z lv.unstable'.offset' + (ls.uents.length : Int) := by
    by_cases He : ls.uents = []
    · have H0 := Hip0 He
      simp only [He, List.length_nil] at Hipb ⊢
      word
    · have H1 := Hip1 He
      word
  have Hipo : uint.Z (logEnd ls) - uint.Z uv'.offset' = (ls.uents.length : Int) := by
    simp only [logEnd, logLast]; word
  have HpendN : PendLogOk σ
      { ls with inprogress := logEnd ls, unpersisted := nextUnstable ls,
                stored := ls.sents ++ ls.uents } := by
    refine ⟨Hpend.1, fun _ e0 He0 => ?_⟩
    obtain ⟨Hi, Hlt⟩ := Hhead e0 He0
    word
  have HpersistN : ls.snap = none → LogPersistOk σ ls.sents
      ls.uents (uint.Z (logEnd ls) - uint.Z uv'.offset') (nextUnstable ls)
      (ls.sents ++ ls.uents) := by
    intro _
    obtain ⟨-, -, H3, H4⟩ := Hp0
    refine ⟨?_, fun _ => H4.symm, H3, H4⟩
    rw [H4]
    exact (List.prefix_append_right_inj ls.sents).mpr (List.take_prefix _ _)
  iapply HΦ
  unfold logAcceptUnstable
  reseal_raftLog
  · simp only [logEnd, logLast]; word
  · simp only [logEnd, logLast]; word

end proof

end EtcdGrove
end Perennial
