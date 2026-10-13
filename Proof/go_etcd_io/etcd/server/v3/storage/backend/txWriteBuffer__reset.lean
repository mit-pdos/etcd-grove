/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/txWriteBuffer__reset.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.txWriteBuffer__reset
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.txBuffer__reset
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.WBufLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

theorem backend.WBuf.reset_seq_lookup (W : WBuf) (id : w64) :
    W.reset.seq !! id =
      ((W.seq !! id).filter (fun _ => decide (id ∈ bksReset W.bks))).map (fun _ => true) := by
  simp [WBuf.reset]

/-- The loop's invariant after one more key. -/
theorem backend.reset_step {W : WBuf} {m' m'' : GMap w64 Bool} {pre : List w64} {key : w64}
    (Hm' : ∀ id, m' !! id = if id ∈ pre then W.reset.seq !! id else W.seq !! id)
    (Hkey : m'' !! key = W.reset.seq !! key) (Hne : ∀ id, id ≠ key → m'' !! id = m' !! id) :
    ∀ id, m'' !! id = if id ∈ pre ++ [key] then W.reset.seq !! id else W.seq !! id := by
  intro id
  by_cases h : id = key
  · subst h; simp [Hkey]
  · rw [Hne id h, Hm' id]; simp [h]

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

theorem backend.txWriteBuffer.reset.wp_proof
    (hReset : backend.txBuffer.reset.spec (GF := GF) (hG := hG)) :
    backend.txWriteBuffer.reset.spec (GF := GF) (hG := hG) := by
  intro txw W
  wp_start as HW
  unfold ownWB
  icases HW with ⟨%m, %s, Hbk, Hseq, Hbks, Hs⟩
  wp_auto
  wp_apply hReset $$ [$Hbk $Hbks] as ⟨Hbk, Hbks⟩
  icases ownBks_open m _ $$ Hbks with ⟨%M, Hm, Hbks⟩
  ihave %Hdom := bksOwn_dom M _ $$ Hbks
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range_gen (fun (keys : List w64) (i : Nat) (m' : GMap w64 Bool) =>
      iprop(∃ kv : w64,
        "k" ∷ k_ptr ↦ kv ∗ "txw" ∷ txw_ptr ↦ txw ∗
        "Hbk" ∷ structFieldRef txWriteBuffer go!"txBuffer" txw ↦ ({ buckets' := m } : txBuffer) ∗
        "Hseq" ∷ structFieldRef txWriteBuffer go!"bucket2seq" txw ↦ s ∗
        "Hm" ∷ m ↦$ M ∗ "Hbks" ∷ bksOwn M (bksReset W.bks) ∗
        "%Hm'" ∷ ⌜∀ id, m' !! id = if id ∈ keys.take i then W.reset.seq !! id else W.seq !! id⌝))
    _ _ _ s W.seq (DFrac.own 1) $$ Hs
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [k txw Hbk Hseq Hm Hbks]
  · iexists _
    simp only [named]
    iframe
    ipureintro
    intro id; simp
  isplitr
  · imodintro
    iintro %i %key %v %m' ⟨%Hki, %Hmv⟩ HP Hs
    iNamed HP
    wp_auto
    wp_apply wp_map_lookup2 $$ Hm as Hm
    have hnot := not_mem_take_of_getElem?' Hknodup Hki
    have hseq : W.seq !! key = some v := by rw [← Hmv, Hm' key]; simp [hnot]
    have htake := take_succ_of_getElem? Hki
    cases hM : M !! key with
    | none =>
      have hB := bksOwn_none Hdom hM
      simp only [Option.isSome_none, Bool.false_eq_true, decide_false, Bool.not_false]
      wp_auto
      wp_apply wp_mapDelete $$ Hs as Hs
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists _
      iframe Hs
      iexists key
      simp only [named]
      iframe
      ipureintro
      rw [htake]
      refine reset_step Hm' ?_ (fun id h => GMap.lookup_delete_ne _ (Ne.symm h))
      rw [GMap.lookup_delete, WBuf.reset_seq_lookup, hseq]
      simp [GMap.mem_iff, hB]
    | some bb =>
      obtain ⟨es, hB⟩ := bksOwn_some Hdom hM
      have hes := bksReset_lookup_some hB
      subst hes
      simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
      icases bksOwn_acc hM hB $$ Hbks with ⟨Hbb, Hback⟩
      unfold ownBB bbAt
      icases Hbb with ⟨%p, ⟨Hbb, Hsl, Hcap, #Hro, #Hin⟩, %Hok⟩
      wp_auto
      wp_apply wp_mapInsert $$ Hs as Hs
      ihave Hbks := Hback $$ %([] : List Ent) [Hbb Hsl Hcap]
      · iexists p
        iframe Hbb Hsl Hcap Hro Hin
        ipureintro; exact Hok
      rw [GMap.insert_id _ _ _ hB]
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists _
      iframe Hs
      iexists key
      simp only [named]
      iframe
      ipureintro
      rw [htake]
      refine reset_step Hm' ?_ (fun id h => GMap.lookup_insert_ne _ _ (Ne.symm h))
      rw [GMap.lookup_insert, WBuf.reset_seq_lookup, hseq]
      simp [GMap.mem_iff, hB]
      rfl
  isplitr
  · imodintro
    iintro %i %key %m' ⟨%Hki, %Hnone⟩ HP
    iNamed HP
    exfalso
    have hnot := not_mem_take_of_getElem?' Hknodup Hki
    have := (Hkset key).1 (List.mem_of_getElem? Hki)
    simp only [Hm' key, hnot, ↓reduceIte] at Hnone
    rw [Hnone] at this
    cases this
  iintro %m' HP Hs
  iNamed HP
  have hfin : m' = W.reset.seq := by
    apply GMap.ext; intro id
    show m' !! id = W.reset.seq !! id
    rw [Hm' id, List.take_length]
    by_cases h : id ∈ keys
    · simp only [h, ↓reduceIte]
    · simp only [h, ↓reduceIte]
      rw [WBuf.reset_seq_lookup]
      have : W.seq !! id = none := by
        cases h' : W.seq !! id with
        | none => rfl
        | some _ => exact absurd ((Hkset id).2 (by rw [h']; rfl)) h
      rw [this]; rfl
  subst hfin
  wp_auto
  iapply HΦ
  iexists m, s
  iframe Hbk Hseq Hs
  iapply ownBks_close
  rw [show W.reset.bks = bksReset W.bks from rfl]
  iframe Hm Hbks

end proof

end EtcdGrove
end Perennial
