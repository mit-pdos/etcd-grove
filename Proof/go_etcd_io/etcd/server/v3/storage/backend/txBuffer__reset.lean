/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/txBuffer__reset.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.txBuffer__reset
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.BksLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- The loop's invariant: before the `i`-th key, the buckets map is `P'` with entries `B'`; the
keys visited are as `bksReset B` has them, the others as they were. -/
def backend.resetInv (txb : Loc) (m : GoMap) (P : BksPhys) (B : GMap w64 (List Ent)) (txb_ptr k_ptr v_ptr : Loc)
    (keys : List w64) (i : Nat) (m' : GMap w64 Loc) : IProp GF :=
  iprop(∃ (P' : BksPhys) (B' : GMap w64 (List Ent)) (kv : w64) (vv : Loc),
    "%Hm'" ∷ ⌜m' = P'.fmap Prod.fst⌝ ∗
    "Hbbs" ∷ ([∗map] _id ↦ x;es ∈ P';B', bbAt (GF := GF) x.1 (DFrac.own 1) x.2 es) ∗
    "%Hok" ∷ ⌜∀ id x es, P' !! id = some x → B' !! id = some es → bbOk x.2 es⌝ ∗
    "Htb" ∷ txb ↦ ({ buckets' := m } : txBuffer) ∗
    "txb" ∷ txb_ptr ↦ txb ∗ "k" ∷ k_ptr ↦ kv ∗ "v" ∷ v_ptr ↦ vv ∗
    "%Hdone" ∷ ⌜∀ j, j ∈ keys.take i → B' !! j = bksReset B !! j⌝ ∗
    "%Hrest" ∷ ⌜∀ j, j ∉ keys.take i → B' !! j = B !! j ∧ P' !! j = P !! j⌝)

theorem backend.bksReset_lookup (B : GMap w64 (List Ent)) (j : w64) :
    bksReset B !! j = ((B !! j).filter (fun es => !es.isEmpty)).map (fun _ => []) := by
  simp [bksReset, GMap.lookup_fmap, GMap.lookup_filter]

theorem backend.txBuffer.reset.wp_proof :
    backend.txBuffer.reset.spec (GF := GF) (hG := hG) := by
  intro txb m B
  wp_start as ⟨Htb, Hbks⟩
  unfold ownBks bksAt
  icases Hbks with ⟨%P, ⟨Hm, Hbbs⟩, %Hok⟩
  ihave %Hiff := bbs_lookup_iff P B (DFrac.own 1) $$ Hbbs
  wp_auto
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  wp_func_lits
  iapply wp_map_for_range_gen (K := w64) (V := Loc) (resetInv txb m P B txb_ptr k_ptr v_ptr)
    _ BucketID.ty (go.GoType.PointerType bucketBuffer.ty) m (P.fmap Prod.fst) (DFrac.own 1) $$ Hm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [Hbbs Htb txb k v]
  · unfold resetInv
    iexists P, B, _, _
    simp only [named]
    iframe
    ipureintro
    exact ⟨Hok, fun j hj => by simp at hj, fun j _ => by simp⟩
  isplitr
  · imodintro
    iintro %i %key %v %m' ⟨%Hki, %Hmv⟩ HP Hm
    unfold resetInv
    iNamed HP
    subst Hm'
    have hnotin := not_mem_take_of_getElem? Hknodup Hki
    obtain ⟨hBk, hPk⟩ := Hrest key hnotin
    obtain ⟨x, hP'k, rfl⟩ : ∃ x, P' !! key = some x ∧ x.1 = v := by
      simp only [GMap.lookup_fmap, Option.map_eq_some_iff] at Hmv
      exact Hmv
    ihave %Hs := bbs_lookup_some P' B' _ key x hP'k $$ Hbbs
    obtain ⟨es, hB'k⟩ := Hs
    have hok := Hok key x es hP'k hB'k
    icases (bbs_delete P' B' _ key x es hP'k hB'k).1 $$ Hbbs with ⟨Hbb, Hbbs⟩
    iunfold bbAt at Hbb
    icases Hbb with ⟨Hbb, Hs, Hcap, #Hro, #Hin⟩
    wp_auto
    have hBkey : B !! key = some es := hBk ▸ hB'k
    have hlen : es.length < 2 ^ 61 := by have := hok.1; have := hok.2.2; omega
    by_cases hes : es = []
    · subst hes
      rw [show decide (W64 ((([] : List Ent).length : Nat) : Int) = W64 0) = true from rfl]
      wp_auto
      wp_apply wp_mapDelete $$ Hm as Hm
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists _
      iframe Hm
      iexists GMap.delete key P', GMap.delete key B', key, x.1
      simp only [named]
      iframe
      ipureintro
      refine ⟨(GMap.fmap_delete _ _ _).symm, ?_, ?_, ?_⟩
      · intro id y fs h1 h2
        simp only [GMap.lookup_delete_iff] at h1 h2
        by_cases hk : key = id
        · simp [hk] at h1
        · simp only [hk, ↓reduceIte] at h1 h2
          exact Hok id y fs h1 h2
      · intro j hj
        rw [mem_take_succ_iff Hki] at hj
        simp only [GMap.lookup_delete_iff]
        by_cases hk : key = j
        · subst hk
          rw [bksReset_lookup, hBkey]; simp [Option.filter]
        · simp only [hk, ↓reduceIte]
          exact Hdone j (hj.resolve_right (Ne.symm hk))
      · intro j hj
        rw [mem_take_succ_iff Hki] at hj
        have hk : key ≠ j := fun h => hj (Or.inr h.symm)
        simp only [GMap.lookup_delete_iff, hk, ↓reduceIte]
        exact Hrest j (fun h => hj (Or.inl h))
    · have hne : decide (W64 ((es.length : Nat) : Int) = W64 0) = false := by
        rw [decide_eq_false_iff_not]
        have hpos : 0 < es.length := List.length_pos_iff.2 hes
        intro h
        have := congrArg (fun w : w64 => w.toNat) h
        rw [show (W64 ((es.length : Nat) : Int)).toNat = es.length by word] at this
        rw [show (W64 0).toNat = 0 by rfl] at this
        omega
      rw [hne]
      wp_auto
      ihave Hbb := bbAt_nil_intro x.1 (DFrac.own 1) x.2 $$ Hbb Hs Hcap Hro
      ihave Hbbs := (bbs_insert (GMap.delete key P') (GMap.delete key B') (DFrac.own 1) key x []
        (GMap.lookup_delete _ _) (GMap.lookup_delete _ _)).2 $$ [Hbb Hbbs]
      · iframe
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists _
      iframe Hm
      iexists <[key := x]> (GMap.delete key P'), <[key := []]> (GMap.delete key B'), key, x.1
      simp only [named]
      iframe
      ipureintro
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [GMap.insert_delete, GMap.insert_id _ _ _ hP'k]
      · intro id y fs h1 h2
        simp only [GMap.lookup_insert_eq_iff, GMap.lookup_delete_iff] at h1 h2
        by_cases hk : key = id
        · simp only [hk, ↓reduceIte, Option.some.injEq] at h1 h2
          subst h1; subst h2
          exact ⟨by simp only [List.length_nil]; have := hok.1; omega, hok.2⟩
        · simp only [hk, ↓reduceIte] at h1 h2
          exact Hok id y fs h1 h2
      · intro j hj
        rw [mem_take_succ_iff Hki] at hj
        simp only [GMap.lookup_insert_eq_iff, GMap.lookup_delete_iff]
        by_cases hk : key = j
        · subst hk
          rw [bksReset_lookup, hBkey]
          cases es with
          | nil => exact absurd rfl hes
          | cons _ _ => simp [Option.filter]
        · simp only [hk, ↓reduceIte]
          exact Hdone j (hj.resolve_right (Ne.symm hk))
      · intro j hj
        rw [mem_take_succ_iff Hki] at hj
        have hk : key ≠ j := fun h => hj (Or.inr h.symm)
        simp only [GMap.lookup_insert_eq_iff, GMap.lookup_delete_iff, hk, ↓reduceIte]
        exact Hrest j (fun h => hj (Or.inl h))
  isplitr
  · imodintro
    iintro %i %key %m' ⟨%Hki, %Hnone⟩ HP
    unfold resetInv
    iNamed HP
    subst Hm'
    exfalso
    have hnotin := not_mem_take_of_getElem? Hknodup Hki
    obtain ⟨-, hPk⟩ := Hrest key hnotin
    have := (Hkset key).1 (List.mem_of_getElem? Hki)
    simp only [GMap.lookup_fmap] at this Hnone
    rw [hPk] at Hnone
    rw [Hnone] at this
    cases this
  iintro %m' HP Hm
  unfold resetInv
  iNamed HP
  subst Hm'
  have hB' : B' = bksReset B := by
    apply GMap.ext; intro j
    by_cases hj : j ∈ keys
    · exact Hdone j (by rw [List.take_length]; exact hj)
    · obtain ⟨hBj, hPj⟩ := Hrest j (by rw [List.take_length]; exact hj)
      have hPn : P !! j = none := by
        cases h : P !! j with
        | none => rfl
        | some _ => exact absurd ((Hkset j).2 (by simp [GMap.lookup_fmap, h])) hj
      have hBn : B !! j = none := by
        cases h : B !! j with
        | none => rfl
        | some _ =>
          have := (Hiff j).2 (by rw [h]; rfl)
          rw [hPn] at this; cases this
      rw [hBj, bksReset_lookup, hBn]; rfl
  subst hB'
  wp_auto
  iapply HΦ
  iframe
  ipureintro; exact Hok

end proof

end EtcdGrove
end Perennial
