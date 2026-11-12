/-
The proof of `Spec/go_etcd_io/bbolt/Cursor__prev_r.lean` (U6h, `notes/bbolt-proof-plan.md`): the
up-loop over the stack's elements at index `0` (truncating the stack), the element found moved
one back (`rPrev_found`) and `last` (`Cursor.last_r`) down to the entry before; at the root with
every index at most `0` the position is `0` (`rPosF_zero`) and `first` (`Cursor.first_r`) resets
the stack.
-/
module

public import Spec.go_etcd_io.bbolt.Cursor__prev_r
public import Spec.go_etcd_io.bbolt.Cursor__first_r
public import Spec.go_etcd_io.bbolt.Cursor__last_r
public import Proof.go_etcd_io.bbolt.Read.CurPos

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- What the up-loop knows of the original stack at `pos`. -/
def rPrevPre (v : View) (bv : List w8) (pp : Loc) (els : List elemRef) : Option Nat → Prop
  | none => els = []
  | some j => (∃ s, rPosAt v bv pp els j s) ∨ (j = 0 ∧ rEmptyAt v bv pp els)

theorem take_set_last {α : Type} (l : List α) (n : Nat) (x : α) (hn : n < l.length) :
    (l.take (n + 1)).set n x = l.take n ++ [x] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hn]
  have : (l.take n).length = n := by simp; omega
  simp only [Option.toList_some]
  rw [List.set_append_right _ _ (by omega), this, Nat.sub_self]
  rfl

theorem Cursor.prev_r.wp_proof
    (hfirst : Cursor.first_r.spec (GF := GF) (hG := hG))
    (hlast : Cursor.last_r.spec (GF := GF) (hG := hG))
    (hkv : Cursor.keyValue_r.spec (GF := GF) (hG := hG)) :
    Cursor.prev_r.spec (GF := GF) (hG := hG) := by
  intro K tx src q T v b dq bv ibp pp c stk els pos hok hpos
  wp_start as ⟨Hk, Hb, Hc, Hs, Hcap⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  have hlen : els.length < 2 ^ 63 := by
    have h1 := Hsl.1; rw [show sint.nat stk.len = (sint.Z stk.len).toNat from rfl] at h1; word
  have hsl0 : sint.Z stk.len = (els.length : Int) := by
    have h1 := Hsl.1; have h2 := Hsl.2
    rw [show sint.nat stk.len = (sint.Z stk.len).toNat from rfl] at h1; omega
  have hpre : rPrevPre v bv pp els pos := by
    cases pos with
    | none => exact hpos
    | some j =>
      rcases hpos with ⟨s, h, -⟩ | h
      · exact Or.inl ⟨s, h⟩
      · exact Or.inr h
  wp_auto
  ihave IH : (∃ (stk1 : GoSlice) (kk : Nat),
      "i" ∷ i_ptr ↦ W64 ((kk : Int) - 1) ∗ "Hk" ∷ rdTxK K tx src q T v ∗
      "Hb" ∷ rBktP v tx b dq bv ibp pp ∗ "Hcc" ∷ c ↦ Cursor.mk b stk1 ∗
      "Hs" ∷ stk1 ↦* els.take kk ∗ "Hcap" ∷ ownSliceCap elemRef stk1 (DFrac.own 1) ∗
      "%Hu" ∷ ⌜kk ≤ els.length ∧ (kk = 0 → els = []) ∧
        ∀ e ∈ els.drop kk, sint.Z e.index' ≤ 0⌝ : IProp GF) $$ [i Hk Hb Hc Hs Hcap]
  · iexists stk, els.length
    simp only [named]
    rw [List.take_length]
    iframe
    isplitl
    · iExactEq i; congr 1; have := hsl0; word
    · ipureintro; exact ⟨Nat.le_refl _, List.eq_nil_of_length_eq_zero, by simp⟩
  wp_for IH
  obtain ⟨hkl, hk0, hz⟩ := Hu
  ihave %Hsl1 := ownSlice_len _ _ _ $$ Hs
  have hsl1 : sint.Z stk1.len = (kk : Int) := by
    have h1 := Hsl1.1; have h2 := Hsl1.2
    have h3 : (sint.Z stk1.len).toNat = kk := by
      rw [← show sint.nat stk1.len = (sint.Z stk1.len).toNat from rfl, ← h1]; simp; omega
    omega
  have hkz : kk ≤ els.length → sint.Z (W64 ((kk : Int) - 1)) = (kk : Int) - 1 := by
    intro _; word
  wp_if_destruct
  · -- the up-loop's body at element `kk - 1`
    have hk1 : 1 ≤ kk := by rw [hkz hkl] at Hif; simp at Hif; omega
    have hkl' : kk - 1 < els.length := by omega
    rw [if_pos ⟨by rw [hkz hkl]; omega, by rw [hkz hkl, hsl1]; omega⟩]
    have hget : (els.take kk)[(sint.Z (W64 ((kk : Int) - 1))).toNat]? = some els[kk - 1] := by
      rw [hkz hkl, show ((kk : Int) - 1).toNat = kk - 1 by omega, List.getElem?_take,
        if_pos (by omega)]
      exact List.getElem?_eq_getElem hkl'
    icases ownSlice_elem_acc (sint.Z (W64 ((kk : Int) - 1))) els[kk - 1] _ _ (els.take kk) (by omega)
      hget $$ Hs with ⟨He, Hsback⟩
    wp_auto
    by_cases hgt : 0 < sint.Z els[kk - 1].index'
    · rw [decide_eq_true (show sint.Z (W64 0) < sint.Z els[kk - 1].index' from hgt)]
      wp_auto
      ihave Hs := Hsback $$ He
      wp_for_post
      obtain ⟨e', he'⟩ : ∃ e' : elemRef, e' = { els[kk - 1] with index' := els[kk - 1].index' - W64 1 } :=
        ⟨_, rfl⟩
      have hset : (els.take kk).set (sint.Z (W64 ((kk : Int) - 1))).toNat
          { page' := els[kk - 1].page', node' := els[kk - 1].node',
            index' := els[kk - 1].index' - W64 1 } = els.take (kk - 1) ++ [e'] := by
        rw [hkz hkl, show ((kk : Int) - 1).toNat = kk - 1 by omega]
        have := take_set_last els (kk - 1) e' hkl'
        rw [Nat.sub_add_cancel hk1, he'] at this
        rw [he']; exact this
      rw [hset]
      obtain ⟨j, rfl⟩ : ∃ j, pos = some j := by
        cases pos with
        | none =>
          exfalso; have h : els = [] := hpre
          rw [h] at hkl'; simp at hkl'
        | some j => exact ⟨j, rfl⟩
      obtain ⟨m, pid, o, s', hp, hm, htl, hoj⟩ : ∃ m pid o s',
          rPreF v bv pp (rFuel v bv) (inBucketRoot bv) (els.take (kk - 1)) m pid o ∧ 0 < m ∧
          rTlF v bv pp m pid e' s' ∧ o + s' = j := by
        rcases hpre with ⟨s0, hp0⟩ | ⟨-, hemp⟩
        · rw [he']
          refine rPrev_found els j s0 (kk - 1) hp0 hkl' ?_ hgt
          rw [Nat.sub_add_cancel hk1]; exact hz
        · exfalso
          obtain ⟨-, e0, pg0, hel, -, -, -, -, hi0⟩ := hemp
          subst hel
          have : kk - 1 = 0 := by simp at hkl'; omega
          simp only [this, List.getElem_cons_zero] at hgt
          rcases hi0 with h | h <;> rw [h] at hgt <;> simp at hgt
      have hne : stk1.len ≠ W64 0 := by
        intro h; rw [h] at hsl1; simp at hsl1; omega
      try wp_auto
      rw [decide_eq_false hne]
      try wp_auto
      wp_apply hlast K tx src q T v b dq bv ibp pp c stk1 (els.take (kk - 1)) e' m pid o s' hok hp hm
        (Or.inl htl) $$ [Hk Hb Hcc Hs Hcap] as ⟨%stk2, %els2, Hk, Hb, Hcc, Hs, Hcap, %Hpost⟩
      · iframe
      obtain ⟨i, hi, hpos2, hland⟩ := Hpost.1 htl
      obtain ⟨e3, pid3, pg3, idx3, hl3, hlf3, -, hlwf3, h163⟩ := hland
      have hsp3 : els2.dropLast ++ [e3] = els2 := by
        obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hl3; simp
      have hsl3 := rPosAt_last _ _ _ hpos2 e3 pid3 pg3 idx3 hl3 hlf3
      have hil3 : idx3 < pageCount pg3 := by
        by_cases h : idx3 < pageCount pg3
        · exact h
        · rw [if_neg h] at hsl3; omega
      have hent3 := rPosAt_ent' _ _ _ hpos2 (by omega) e3 pid3 pg3 idx3 hl3 hlf3
      have hix3 : sint.Z e3.index' = (idx3 : Int) := by
        rw [hlf3.2.2.2.2]; have := hlf3.2.2.2.1; have := pageCount_lt pg3; word
      rw [← hsp3]
      try wp_auto
      wp_apply hkv K tx src q T v b dq bv ibp pp c stk2 els2.dropLast e3 pid3 pg3 hlf3.1 hlf3.2.1
        hlf3.2.2.1 hlwf3 h163 (by omega) $$ [Hk Hb Hcc Hs] as %k %vl %fl ⟨Hk, Hb, Hcc, Hs, Hkv⟩
      · iframe
      try wp_auto
      iapply HΦ
      iexists stk2, els2.dropLast ++ [e3]
      iframe
      obtain rfl : j = i + 1 := by omega
      unfold rPrevPost
      iexists pg3, idx3
      rw [hix3, Int.toNat_natCast]
      iframe
      ipureintro
      rw [hsp3]
      exact ⟨by rw [show i + 1 = o + s' by omega]; exact hpos2,
        ⟨e3, pid3, pg3, idx3, hl3, hlf3, Or.inr hil3, hlwf3, h163⟩, hent3⟩
    · rw [decide_eq_false (show ¬ sint.Z (W64 0) < sint.Z els[kk - 1].index' from hgt)]
      wp_auto
      ihave Hs := Hsback $$ He
      rw [show (els.take kk).set (sint.Z (W64 ((kk : Int) - 1))).toNat els[kk - 1] = els.take kk by
        rw [hkz hkl, show ((kk : Int) - 1).toNat = kk - 1 by omega]
        have h : (els.take kk)[kk - 1]'(by simp; omega) = els[kk - 1] := by simp
        rw [← h, List.set_getElem_self]]
      by_cases hk1' : kk = 1
      · -- at the root: `first`, nil
        subst hk1'
        have hl1 : stk1.len = W64 1 := by
          apply BitVec.eq_of_toInt_eq; rw [show (W64 1).toInt = 1 from rfl]; exact hsl1
        rw [decide_eq_true hl1]
        wp_auto
        wp_apply hfirst K tx src q T v b dq bv ibp pp c stk1 (els.take 1) hok
          $$ [Hk Hb Hcc Hs Hcap] as %k0 %vl0 %fl0 ⟨%stk2, %els2, %vl2, Hk, Hb, Hcc, Hs, Hcap, Hcur, -⟩
        · iframe
        ihave %Hp0 := rCurKV_first_pos v bv pp els2 k0 vl2 fl0 $$ Hcur
        try wp_auto
        wp_for_post
        iapply HΦ
        iexists stk2, els2
        iframe
        have hall : ∀ e ∈ els, sint.Z e.index' ≤ 0 := by
          intro e he
          have hsp : els = els.take 1 ++ els.drop 1 := (List.take_append_drop 1 els).symm
          rw [hsp, List.mem_append] at he
          rcases he with he | he
          · have : els.take 1 = [els[0]] := by
              rw [List.take_one]; simp [List.head?_eq_getElem?, List.getElem?_eq_getElem hkl']
            rw [this, List.mem_singleton] at he; subst he
            have := hgt; simp only [Nat.sub_self] at this; omega
          · exact hz e he
        cases pos with
        | none => exfalso; have h : els = [] := hpre; rw [h] at hkl'; simp at hkl'
        | some j =>
          cases j with
          | zero => unfold rPrevPost; ipureintro; exact ⟨rfl, rfl, rfl, Hp0⟩
          | succ j =>
            exfalso
            rcases hpre with ⟨s0, hp0⟩ | ⟨h, -⟩
            · have := rPosF_zero _ _ _ _ _ hp0 hall; omega
            · omega
      · -- truncate the stack
        have hl1 : stk1.len ≠ W64 1 := by
          intro h; rw [h] at hsl1; simp at hsl1; omega
        rw [decide_eq_false hl1]
        wp_auto
        ihave %Hcw := ownSliceCap_wf _ _ $$ Hcap
        rw [if_pos (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 ((kk : Int) - 1)) ∧
          sint.Z (W64 ((kk : Int) - 1)) ≤ sint.Z stk1.cap by rw [hkz hkl]; simp; omega)]
        icases ownSlice_slice_with_cap (V := elemRef) (W64 0) (W64 ((kk : Int) - 1)) stk1 _
          ⟨by decide, by rw [hkz hkl]; simp; omega, by rw [hkz hkl, hsl1]; omega⟩ $$ [Hs Hcap]
          with ⟨-, Hs, Hcap⟩
        · iframe
        have hsub : subslice (sint.nat (W64 0)) (sint.nat (W64 ((kk : Int) - 1))) (els.take kk) =
            els.take (kk - 1) := by
          have h1 : sint.nat (W64 ((kk : Int) - 1)) = kk - 1 := by
            unfold sint.nat; rw [show (W64 ((kk : Int) - 1)).toInt = (kk : Int) - 1 from hkz hkl]
            omega
          rw [h1, show sint.nat (W64 0) = 0 from rfl]
          unfold subslice; rw [List.drop_zero, List.take_take]; congr 1; omega
        rw [hsub]
        wp_auto
        wp_for_post
        iframe
        iexists _, kk - 1
        simp only [named]
        iframe
        isplitl
        · iExactEq i; congr 1; rw [show ((kk - 1 : Nat) : Int) = (kk : Int) - 1 by omega]; word
        · ipureintro
          refine ⟨by omega, fun h => by omega, ?_⟩
          intro e he
          rw [show kk - 1 = (kk - 1) by rfl, List.drop_eq_getElem_cons hkl', Nat.sub_add_cancel hk1] at he
          rcases List.mem_cons.mp he with rfl | he
          · omega
          · exact hz e he
  · -- the up-loop ran out: the empty stack, unpositioned
    have hk0' : kk = 0 := by rw [hkz hkl] at Hif; simp at Hif; omega
    subst hk0'
    have hel := hk0 rfl
    have hl0 : stk1.len = W64 0 := by
      apply BitVec.eq_of_toInt_eq; rw [show (W64 0).toInt = 0 from rfl]; exact hsl1
    rw [decide_eq_true hl0]
    wp_auto
    iapply HΦ
    iexists stk1, els.take 0
    iframe
    cases pos with
    | none => unfold rPrevPost; ipureintro; simp
    | some j =>
      exfalso
      rw [hel] at hpre
      rcases hpre with ⟨s0, hp0⟩ | ⟨-, hemp⟩
      · unfold rPosAt at hp0
        match rFuel v bv, hp0 with
        | 0, h => exact absurd h (by simp [rPosF])
        | _ + 1, h => exact absurd h (by simp [rPosF])
      · obtain ⟨-, e0, pg0, hel', -⟩ := hemp; cases hel'

end proof

end bbolt
end EtcdGrove
end Perennial
