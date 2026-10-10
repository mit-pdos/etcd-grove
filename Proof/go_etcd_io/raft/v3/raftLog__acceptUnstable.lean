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
  rw [Hunp0] at Hp0
  have Hplen := Hp0.1.length_le
  simp only [storApp, List.length_append, List.length_take] at Hplen
  have Hhead : ∀ e0, (nextUnstable ls).head? = some e0 →
      uint.Z e0.Index' = uint.Z ls.inprogress ∧
      uint.Z ls.inprogress - uint.Z lv.unstable'.offset' < (ls.uents.length : Int) := by
    intro e0 He0
    simp only [nextUnstable, List.head?_drop] at He0
    have Hlt := (List.getElem?_eq_some_iff.1 He0).1
    have Hc := Hcontig _ _ He0
    simp only [logOffset] at Hc Hlt
    constructor <;> omega
  have Hpo : σ.pend = [] ∧ (nextUnstable ls ≠ [] → PendOk σ (nextUnstable ls)) := by
    refine ⟨Hpend.1.trans Hunp0, fun Hne => ⟨Hne, fun e0 He0 => ?_⟩⟩
    obtain ⟨Hi, Hlt⟩ := Hhead e0 He0
    rw [Hsp]
    constructor <;> omega
  -- the storage's hand-out law: the right to append the batch, and the storage at
  -- `{ σ with pend := nextUnstable ls }`, which reads as before below the batch (with
  -- nothing to hand out, the storage keeps its state, which is that one)
  imod isStorage_handout lv.storage' σ (nextUnstable ls) Hpo $$ HisStorage HStorage
    with ⟨HStorage, Happ⟩
  ihave Happ : appendRight ls.storage (nextUnstable ls) $$ [Happ]
  · rw [← Hstor]; iexact Happ
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
  have Hstore' : LogStoreOk ls.snap { σ with pend := nextUnstable ls } ls.prev ls.sents
      ls.uents := Hstore
  have Hssnap' : ls.snap = none →
      StoredSnapOk { σ with pend := nextUnstable ls } ls.committed ls.prev
        (ls.sents ++ ls.uents) := Hssnap
  have HpendN : PendLogOk { σ with pend := nextUnstable ls }
      { ls with inprogress := logEnd ls, unpersisted := nextUnstable ls,
                stored := ls.sents ++ ls.uents } := by
    refine ⟨rfl, fun _ e0 He0 => ?_⟩
    obtain ⟨Hi, Hlt⟩ := Hhead e0 He0
    word
  have HpersistN : ls.snap = none → LogPersistOk { σ with pend := nextUnstable ls } ls.sents
      ls.uents (uint.Z (logEnd ls) - uint.Z uv'.offset') (nextUnstable ls)
      (ls.sents ++ ls.uents) := by
    intro _
    simp only [LogPersistOk, storApp_pend]
    simp only [Hipo, nextUnstable, logOffset, ← Hoffset]
    exact persist_accept ls.prev σ ls.sents ls.uents _ Hidx Hsp (by omega) ls.stored Hp0
  iapply HΦ
  unfold logAcceptUnstable
  iframe Happ
  reseal_raftLog
  · simp only [logEnd, logLast]; word
  · simp only [logEnd, logLast]; word

end proof

end EtcdGrove
end Perennial
