/-
`verifyPageReachable` on a page `freepages`' check visits (U10e of `notes/bbolt-proof-plan.md`):
the page is below the high-water mark, none of its slots is reachable yet, `freed` is empty and
the page is a branch or a leaf, so nothing is sent; its slots become reachable.
-/
module

public import Proof.go_etcd_io.bbolt.Commit.CheckSpec
public import Spec.go_etcd_io.bbolt.internal.common.Page__Id
public import Spec.go_etcd_io.bbolt.internal.common.Page__Overflow
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsBranchPage
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsLeafPage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The slots of a page with header `hd` (`id` to `id + overflow`). -/
def hdSlot (hd : Page) (x : Nat) : Prop :=
  hd.id'.toNat ≤ x ∧ x ≤ hd.id'.toNat + hd.overflow'.toNat

/-- **`verifyPageReachable(p, hwm, stack, reachable, freed, ch)`** on a page nothing reports:
its slots are added to `reachable`. -/
abbrev verifyPageReachable_ok.spec : Prop :=
  ∀ (p : Loc) (hd : Page) (dq : DFrac) (hwm : w64) (stk : GoSlice) (rm fm ch : Loc)
    (M : GMap w64 Loc),
  hd.id'.toNat ≤ hwm.toNat → hd.id'.toNat + hd.overflow'.toNat < 2 ^ 64 →
  (∀ x : w64, (M !! x).isSome = true → ¬ hdSlot hd x.toNat) →
  (hd.flags' = W16 1 ∨ hd.flags' = W16 2) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ p ↦{dq} hd ∗ rm ↦$ M ∗
      fm ↦$ (∅ : GMap w64 Bool) }}
    (App (App (App (App (App (App (Val #(functions verifyPageReachable [])) (Val #p)) (Val #hwm))
      (Val #stk)) (Val #rm)) (Val #fm)) (Val #ch))
  {{ RET #(); p ↦{dq} hd ∗ fm ↦$ (∅ : GMap w64 Bool) ∗ ∃ M' : GMap w64 Loc, rm ↦$ M' ∗
      ⌜∀ x : w64, (M' !! x).isSome = true ↔ ((M !! x).isSome = true ∨ hdSlot hd x.toNat)⌝ }}

theorem verifyPageReachable_ok.wp_proof
    (wp_Id : internal.common.Page.Id.spec (GF := GF) (hG := hG))
    (wp_Overflow : internal.common.Page.Overflow.spec (GF := GF) (hG := hG))
    (wp_IsBranch : internal.common.Page.IsBranchPage.spec (GF := GF) (hG := hG))
    (wp_IsLeaf : internal.common.Page.IsLeafPage.spec (GF := GF) (hG := hG)) :
    verifyPageReachable_ok.spec (GF := GF) (hG := hG) := by
  intro p hd dq hwm stk rm fm ch M hle hlt hdis hfl
  wp_start as ⟨Hp, Hrm, Hfm⟩
  ihave #Hpkc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_Id p hd dq $$ [Hp] as Hp
  · iframe
  rw [decide_eq_false (show ¬ uint.Z hd.id' > uint.Z hwm by
    rw [show uint.Z hd.id' = (hd.id'.toNat : Int) from rfl,
      show uint.Z hwm = (hwm.toNat : Int) from rfl]; omega)]
  wp_auto
  have hov : hd.overflow'.toNat < 2 ^ 32 := hd.overflow'.isLt
  ihave IH : (∃ (k : w64) (M' : GMap w64 Loc),
      "i" ∷ i_ptr ↦ k ∗ "Hp" ∷ p ↦{dq} hd ∗ "Hrm" ∷ rm ↦$ M' ∗
      "%Hk" ∷ ⌜k.toNat ≤ hd.overflow'.toNat + 1 ∧ ∀ x : w64, (M' !! x).isSome = true ↔
        ((M !! x).isSome = true ∨ (hd.id'.toNat ≤ x.toNat ∧ x.toNat < hd.id'.toNat + k.toNat))⌝ :
      IProp GF) $$ [i Hp Hrm]
  · iexists W64 0, M
    simp only [named]
    iframe
    ipureintro
    refine ⟨by simp, fun x => ?_⟩
    try simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero]
    constructor
    · intro h; exact .inl h
    · rintro (h | ⟨a, b⟩)
      · exact h
      · have : (W64 0 : w64).toNat = 0 := rfl
        omega
  wp_for IH
  wp_apply wp_Overflow p hd dq $$ [Hp] as Hp
  · iframe
  have hkov : uint.Z k ≤ uint.Z (W64 (uint.Z hd.overflow')) ↔ k.toNat ≤ hd.overflow'.toNat := by
    rw [show uint.Z (W64 (uint.Z hd.overflow')) = (hd.overflow'.toNat : Int) by
      rw [show uint.Z hd.overflow' = (hd.overflow'.toNat : Int) from rfl]; word]
    rw [show uint.Z k = (k.toNat : Int) from rfl]; omega
  by_cases hk : k.toNat ≤ hd.overflow'.toNat
  · rw [decide_eq_true (hkov.2 hk)]
    simp only [_root_.decide_true, ↓reduceIte]
    wp_auto
    wp_apply wp_Id p hd dq $$ [Hp] as Hp
    · iframe
    try wp_auto
    have hik : (hd.id' + k).toNat = hd.id'.toNat + k.toNat := by
      rw [BitVec.toNat_add]; omega
    have hnone : ¬ (M' !! (hd.id' + k)).isSome = true := by
      intro h
      rcases (Hk.2 _).1 h with h1 | ⟨-, h2⟩
      · exact hdis _ h1 ⟨by omega, by omega⟩
      · omega
    wp_apply (wp_map_lookup2 _ _ rm M' (hd.id' + k) (DFrac.own 1)) $$ Hrm as Hrm
    rw [decide_eq_false hnone]
    try wp_auto
    wp_apply (wp_mapInsert _ rm M' (hd.id' + k) p) $$ Hrm as Hrm
    try wp_auto
    wp_for_post
    iframe
    iexists (k + W64 1), _
    simp only [named]
    iframe
    have hk1 : (k + W64 1).toNat = k.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    ipureintro
    refine ⟨by omega, fun x => ?_⟩
    rw [hk1]
    by_cases hx : x = hd.id' + k
    · subst hx
      rw [GMap.lookup_insert]
      simp only [Option.isSome_some, true_iff]
      right; omega
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hx), Hk.2 x]
      have hxk : x.toNat ≠ hd.id'.toNat + k.toNat := fun e =>
        hx (BitVec.eq_of_toNat_eq (by rw [hik, e]))
      constructor
      · rintro (h | ⟨a, b⟩)
        · exact .inl h
        · exact .inr ⟨a, by omega⟩
      · rintro (h | ⟨a, b⟩)
        · exact .inl h
        · exact .inr ⟨a, by omega⟩
  · rw [decide_eq_false (fun h => hk (hkov.1 h))]
    try simp only [val_bool_eq, _root_.decide_false, Bool.false_eq_true, ↓reduceIte]
    try wp_auto
    try simp only [_root_.decide_true, ↓reduceIte]
    try wp_auto
    wp_apply wp_Id p hd dq $$ [Hp] as Hp
    · iframe
    wp_apply (wp_map_lookup1 _ _ fm (∅ : GMap w64 Bool) hd.id' (DFrac.own 1)) $$ Hfm as Hfm
    try wp_auto
    rw [show (zero_val Bool : Bool) = false from rfl]
    try wp_auto
    wp_apply wp_IsBranch p hd dq $$ [Hp] as Hp
    · iframe
    have hpost : ∀ x : w64, (M' !! x).isSome = true ↔ ((M !! x).isSome = true ∨ hdSlot hd x.toNat) := by
      intro x; rw [Hk.2 x]; unfold hdSlot
      have : k.toNat = hd.overflow'.toNat + 1 := by omega
      constructor
      · rintro (h | ⟨a, b⟩)
        · exact .inl h
        · exact .inr ⟨a, by omega⟩
      · rintro (h | ⟨a, b⟩)
        · exact .inl h
        · exact .inr ⟨a, by omega⟩
    rcases hfl with hf | hf
    · rw [hf]
      try wp_auto
      iapply HΦ
      iframe
      ipureintro; exact hpost
    · rw [hf]
      try wp_auto
      wp_apply wp_IsLeaf p hd dq $$ [Hp] as Hp
      · iframe
      rw [hf]
      try wp_auto
      iapply HΦ
      iframe
      ipureintro; exact hpost

end spec

end bbolt
end EtcdGrove
end Perennial
