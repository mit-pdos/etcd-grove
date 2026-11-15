/- Lean-first (no Rocq counterpart). The proof of `(*decoder).ops` (W4c U5): the count, then each
operation's fields and entries; `ok` stays set (every read is within the encoding), so the loops run
the counts read. -/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.decoder__ops
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.decoder__hs
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.decoder__u64

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal

section pure
variable [GooseExts]

/-- A count read before its elements is below `2^30` (each element at least 8 bytes). -/
theorem flat_len_bound {α : Type} (bs : List w8) (k : Nat) (l : List α) (f : α → List w8)
    (r : List w8) (hf : ∀ x, 8 ≤ (f x).length) (h : bs.drop k = l.flatMap f ++ r)
    (hn : bs.length ≤ 0x40000000) : l.length ≤ 0x40000000 := by
  have e := congrArg List.length h
  have := flatMap_length_ge l f 8 hf
  simp only [List.length_drop, List.length_append] at e; omega

/-- The next element of a `flatMap` over a suffix. -/
theorem flatMap_drop_cons {α : Type} (l : List α) (f : α → List w8) (i : Nat) (x : α)
    (hx : l[i]? = some x) : (l.drop i).flatMap f = f x ++ (l.drop (i + 1)).flatMap f := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hx
  rw [List.drop_eq_getElem_cons hi, List.flatMap_cons]

theorem take_succ_of {α : Type} (l : List α) (i : Nat) (x : α) (hx : l[i]? = some x) :
    l.take (i + 1) = l.take i ++ [x] := by
  rw [List.take_add_one, hx]; simp

theorem snap_dec (b : Bool) : decide ((if b then W64 1 else W64 0) = W64 1) = b := by
  cases b <;> decide

/-- A loop counter below a count read. -/
theorem lt_count (i : w64) (n : Nat) (hn : n ≤ 0x40000000) :
    (uint.Z i < uint.Z (W64 (n : Int))) ↔ uint.nat i < n := by
  constructor <;> intro h <;> word

theorem nat_succ (i : w64) (n : Nat) (hn : n ≤ 0x40000000) (h : uint.nat i < n) :
    uint.nat (i + W64 1) = uint.nat i + 1 := by word

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

theorem decoder.ops.wp_proof (wp_u64 : decoder.u64.spec (GF := GF) (hG := hG))
    (wp_hs : decoder.hs.spec (GF := GF) (hG := hG)) :
    decoder.ops.spec (GF := GF) (hG := hG) := by
  intro d bs k h r hdrop
  have h1 : bs.drop k = tU64 (W64 h.length) ++ (h.flatMap tOpBytes ++ r) := by
    rw [hdrop]; simp [tOpsBytes]
  have h2 := drop_app' h1
  rw [tU64_length] at h2
  wp_start as Hd
  icases decRep_len d bs k $$ Hd with ⟨Hd, %Hb⟩
  have hhl := flat_len_bound bs (k + 8) h tOpBytes r tOpBytes_length h2 Hb.2
  wp_auto
  wp_apply wp_u64 d bs k _ _ h1 $$ Hd as Hd
  wp_apply +noauto (wp_slice_make2 (V := walOp) (W64 0)) as %h0 ⟨Hh0, Hh0cap⟩
  · ipureintro; word
  simp only [List.replicate_zero]
  imod ownSlice_persist $$ Hh0 with #Hh0
  wp_auto
  ihave HI : (∃ (i : w64) (hsl : GoSlice) (vs : List walOp) (k' : Nat),
      "i" ∷ i_ptr ↦ i ∗ "h" ∷ h_ptr ↦ hsl ∗ "Hh" ∷ hsl ↦*□ vs ∗
      "Hcap" ∷ ownSliceCap walOp hsl (DFrac.own 1) ∗ "Hel" ∷ opsElems vs (h.take (uint.nat i)) ∗
      "Hd" ∷ decRep d bs k' ∗
      "%Hi" ∷ ⌜bs.drop k' = (h.drop (uint.nat i)).flatMap tOpBytes ++ r ∧
        uint.nat i ≤ h.length ∧ k ≤ bs.length⌝ : IProp GF) $$ [i h Hh0 Hh0cap Hd]
  · iexists W64 0, h0, [], k + 8
    simp only [show uint.nat (W64 0) = 0 from rfl, List.take_zero, List.drop_zero]
    iframe
    isplitl []
    · iexact Hh0
    isplitl []
    · iapply opsElems_nil
    ipureintro; exact ⟨h2, Nat.zero_le _, Hb.1⟩
  wp_for HI
  wp_if_destruct
  · have hil : uint.nat i < h.length := (lt_count i h.length hhl).mp Hif
    obtain ⟨oo, Hoo⟩ : ∃ oo, h[uint.nat i]? = some oo := ⟨_, List.getElem?_eq_getElem hil⟩
    have hd1 := Hi.1
    rw [flatMap_drop_cons h tOpBytes _ oo Hoo, List.append_assoc] at hd1
    generalize hR : (h.drop (uint.nat i + 1)).flatMap tOpBytes ++ r = R at hd1
    have e1 : bs.drop k' = tU64 (if oo.snap then W64 1 else W64 0) ++ (tHsBytes oo.hs ++
        (tU64 oo.idx ++ (tU64 oo.term ++ (tU64 (W64 oo.ents.length) ++
          (oo.ents.flatMap tEntBytes ++ R))))) := by
      rw [hd1]; simp [tOpBytes]
    have e2 := drop_app' e1
    have e3 := drop_app' e2
    have e4 := drop_app' e3
    have e5 := drop_app' e4
    have e6 := drop_app' e5
    simp only [tU64_length, tHsBytes_length] at e2 e3 e4 e5 e6
    icases decRep_acc d bs k' $$ Hd with ⟨%sl, Hd, Hclose⟩
    wp_auto
    simp only [decide_true, ↓reduceIte]
    wp_auto
    ihave Hd := Hclose $$ Hd
    wp_apply wp_u64 d bs k' _ _ e1 $$ Hd as Hd
    wp_apply wp_hs d bs (k' + 8) _ _ e2 $$ Hd as Hd
    wp_apply wp_u64 d bs (k' + 8 + 24) _ _ e3 $$ Hd as Hd
    wp_apply wp_u64 d bs (k' + 8 + 24 + 8) _ _ e4 $$ Hd as Hd
    wp_apply wp_u64 d bs (k' + 8 + 24 + 8 + 8) _ _ e5 $$ Hd as Hd
    simp only [snap_dec]
    have hel := flat_len_bound bs _ oo.ents tEntBytes R tEntBytes_length e6 Hb.2
    wp_apply +noauto (wp_slice_make2 (V := entry) (W64 0)) as %e0 ⟨He0, He0cap⟩
    · ipureintro; word
    simp only [List.replicate_zero]
    imod ownSlice_persist $$ He0 with #He0
    wp_auto
    ihave HJ : (∃ (j : w64) (esl : GoSlice) (k'' : Nat),
        "j" ∷ j_ptr ↦ j ∗ "o" ∷ o_ptr ↦ (walOp.mk oo.snap oo.hs esl oo.idx oo.term) ∗
        "He" ∷ esl ↦*□ oo.ents.take (uint.nat j) ∗ "Hecap" ∷ ownSliceCap entry esl (DFrac.own 1) ∗
        "Hd" ∷ decRep d bs k'' ∗
        "%Hj" ∷ ⌜bs.drop k'' = (oo.ents.drop (uint.nat j)).flatMap tEntBytes ++ R ∧
          uint.nat j ≤ oo.ents.length⌝ : IProp GF) $$ [j o He0 He0cap Hd]
    · iexists W64 0, e0, k' + 8 + 24 + 8 + 8 + 8
      simp only [show uint.nat (W64 0) = 0 from rfl, List.take_zero, List.drop_zero]
      iframe
      isplitl []
      · iexact He0
      ipureintro; exact ⟨e6, Nat.zero_le _⟩
    wp_for HJ
    wp_if_destruct
    · have hjl : uint.nat j < oo.ents.length := (lt_count j _ hel).mp Hif
      obtain ⟨e, He'⟩ : ∃ e, oo.ents[uint.nat j]? = some e := ⟨_, List.getElem?_eq_getElem hjl⟩
      have f1 := Hj.1
      rw [flatMap_drop_cons oo.ents tEntBytes _ e He', List.append_assoc] at f1
      have g1 : bs.drop k'' = tU64 e.index' ++ (tU64 e.term' ++ (tU64 e.size' ++ (tU64 e.salt' ++
          ((oo.ents.drop (uint.nat j + 1)).flatMap tEntBytes ++ R)))) := by
        rw [f1]; simp [tEntBytes]
      have g2 := drop_app' g1
      have g3 := drop_app' g2
      have g4 := drop_app' g3
      have g5 := drop_app' g4
      simp only [tU64_length] at g2 g3 g4 g5
      icases decRep_acc d bs k'' $$ Hd with ⟨%sl2, Hd, Hclose⟩
      wp_auto
      simp only [decide_true, ↓reduceIte]
      wp_auto
      ihave Hd := Hclose $$ Hd
      wp_apply wp_u64 d bs k'' _ _ g1 $$ Hd as Hd
      wp_apply wp_u64 d bs (k'' + 8) _ _ g2 $$ Hd as Hd
      wp_apply wp_u64 d bs (k'' + 8 + 8) _ _ g3 $$ Hd as Hd
      wp_apply wp_u64 d bs (k'' + 8 + 8 + 8) _ _ g4 $$ Hd as Hd
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %esl1 ⟨Hesl1, -⟩
      wp_apply wp_slice_append_persistent $$ [$He $Hecap $Hesl1] as %esl' ⟨He, Hecap, -⟩
      wp_for_post
      iframe
      iexists j + W64 1, esl', k'' + 8 + 8 + 8 + 8
      have hj1 := nat_succ j _ hel hjl
      rw [hj1, take_succ_of oo.ents _ e He']
      iframe
      ipureintro
      exact ⟨g5, by omega⟩
    · have hjl : uint.nat j = oo.ents.length := by
        have := mt (lt_count j _ hel).mpr Hif; omega
      have htk : oo.ents.take (uint.nat j) = oo.ents := by rw [hjl, List.take_length]
      rw [htk]
      ihave #Hop : opRep (walOp.mk oo.snap oo.hs esl oo.idx oo.term) oo $$ [He]
      · iunfold opRep
        isplitr
        · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
        iexact He
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %osl ⟨Hosl, -⟩
      wp_apply wp_slice_append_persistent $$ [$Hh $Hcap $Hosl] as %hsl' ⟨Hh, Hcap, -⟩
      ihave Hel := opsElems_snoc vs (h.take (uint.nat i)) _ oo $$ [$Hel $Hop]
      wp_for_post
      iframe
      iexists i + W64 1, hsl', vs ++ [walOp.mk oo.snap oo.hs esl oo.idx oo.term], k''
      have hi1 := nat_succ i h.length hhl hil
      rw [hi1, take_succ_of h _ oo Hoo]
      iframe
      ipureintro
      refine ⟨?_, by omega, Hi.2.2⟩
      rw [Hj.1, hjl, List.drop_length, List.flatMap_nil, List.nil_append, hR]
  · have hil : uint.nat i = h.length := by
      have := mt (lt_count i h.length hhl).mpr Hif; omega
    have htk : List.take (uint.nat i) h = h := by rw [hil, List.take_length]
    rw [htk]
    icases decRep_len d bs k' $$ Hd with ⟨Hd, %Hb'⟩
    have hk' : k' = k + (tOpsBytes h).length :=
      drop_eq_len hdrop (by rw [Hi.1, hil, List.drop_length]; rfl) Hi.2.2 Hb'.1
    rw [← hk']
    iapply HΦ
    iframe
    iunfold opsRep
    iexists vs
    iframe

end proof

end etcd_wal
end EtcdGrove
end Perennial
