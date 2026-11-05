/-
The proof of `Spec/go_etcd_io/bbolt/Cursor__next_w.lean` (U6z/U6aa, `notes/bbolt-proof-plan.md`,
"Writer reads at a fraction"): the outer loop's invariant is a writer stack (`wStk`) with the original
stack's target (`wNextTo`), either the original stack or an empty leaf at index `0` (restarted); the
upward scan's is `WNext.scanOK` (each level's `count()`: `WNext.wp_lvl_count`); the level found,
moved one further and truncated, is `goToFirstElementOnTheStack_w`'s prefix (`WNext.trunc_prefix`),
the descent's stack at the target (`WNext.found`, by `stackPos_nextR`); no level found, the stack is
at the end (`WNext.scan_none`). `next_we`: from `wEndAt` no level moves.
-/
module

public import Spec.go_etcd_io.bbolt.Cursor__next_w
public import Spec.go_etcd_io.bbolt.Cursor__goToFirstElementOnTheStack_w
public import Spec.go_etcd_io.bbolt.Cursor__keyValue_ws
public import Proof.go_etcd_io.bbolt.Read.WNextCnt

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

omit [GooseSemantics] [GooseInterp] go_gctx hos sem package_sem in
theorem idx_sint (x : w64) (c : Nat) (hc : c < 2 ^ 63) (h : x.toNat ≤ c) :
    sint.Z x = (x.toNat : Int) := by
  have : (x.toNat : Int) = uint.Z x := rfl
  rw [this]
  word

omit [GooseSemantics] [GooseInterp] go_gctx hos sem package_sem in
/-- At the end (`wEndAt`) no level can move. -/
theorem we_noMove (nl : Loc → Option (Loc × Nat)) (v : View) (b : Loc) (rt : Nat)
    (es : List BoltEnt) (pids : List Nat) (els : List elemRef) (hp : sPathR nl v b rt els pids)
    (hend : wEndAt v es pids els) (j : Nat) (hj : j < els.length) (x : elemRef)
    (hx : els[j]? = some x) (h63 : WNext.cntAt v es pids els j < 2 ^ 63) :
    ¬ sint.Z x.index' < (WNext.cntAt v es pids els j : Int) - 1 := by
  by_cases hj1 : j + 1 < els.length
  · obtain ⟨pid, pg, hpid, hpg, -, hlt⟩ := WNext.sPathR_br nl v b rt pids els hp j hj1 x hx
    rw [WNext.cntAt_br v es pids els j pid pg hj1 hpid hpg] at h63 ⊢
    have hl := hend.1 j pid x hpid hx hj1
    rw [Prev.pidKeys_length v pid pg hpg] at hl
    rw [idx_sint x.index' _ h63 (by omega)]
    omega
  · rw [WNext.cntAt_leaf v es pids els j (by omega)] at h63 ⊢
    obtain ⟨-, e, he, h⟩ := hend
    have hl : els.getLast? = some x := by
      rw [List.getLast?_eq_getElem?, show els.length - 1 = j by omega]; exact hx
    rw [hl] at he; cases he
    rcases h with h | ⟨h0, h⟩
    · rw [h]
      have : sint.Z (W64 (leafCnt v es pids els : Int)) = (leafCnt v es pids els : Int) := by word
      omega
    · rw [h, h0]; decide

theorem Cursor.next_we.wp_proofQ
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG)) :
    Cursor.next_we.specQ (GF := GF) (hG := hG) := by
  intro K tx r m q X n bl rt ipg nl c stk els pids hc hst
  wp_start as ⟨Hw, Hc, Hs, #Hown⟩
  icases wtxWQ_pkgInit K tx r m q X $$ Hw with ⟨Hw, #Hpkg⟩
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  wp_auto
  ihave IH : ("Hw" ∷ wtxWQ K tx r m q X ∗ "Hcc" ∷ c ↦ Cursor.mk bl stk ∗
      "Hs" ∷ stk ↦* els : IProp GF) $$ [Hw Hc Hs]
  · simp only [named]; iframe
  wp_for IH
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  ihave IH2 : (∃ (kk : Nat), "i" ∷ i_ptr ↦ W64 ((kk : Int) - 1) ∗ "Hs" ∷ stk ↦* els ∗
      "Hw" ∷ wtxWQ K tx r m q X ∗ "%Hu" ∷ ⌜kk ≤ els.length⌝ : IProp GF) $$ [i Hs Hw]
  · iexists els.length
    simp only [named]
    iframe
    isplitl
    · iExactEq i; congr 1; word
    · ipureintro; exact Nat.le_refl _
  have hlen : els.length < 2 ^ 63 := by
    have h1 := Hsl.1; rw [show sint.nat stk.len = (sint.Z stk.len).toNat from rfl] at h1; word
  wp_for IH2
  wp_if_destruct
  · have hkz : sint.Z (W64 ((kk : Int) - 1)) = (kk : Int) - 1 := by word
    have hk1 : 1 ≤ kk := by rw [hkz] at Hif; simp at Hif; omega
    have hkl : kk - 1 < els.length := by omega
    have hsl' : sint.Z stk.len = (els.length : Int) := by
      have h1 := Hsl.1; have h2 := Hsl.2
      rw [show sint.nat stk.len = (sint.Z stk.len).toNat from rfl] at h1; omega
    rw [if_pos ⟨by rw [hkz]; omega, by rw [hkz, hsl']; omega⟩]
    have hget : els[(sint.Z (W64 ((kk : Int) - 1))).toNat]? = some els[kk - 1] := by
      rw [hkz, show ((kk : Int) - 1).toNat = kk - 1 by omega]; simp
    rcases hst with h0 | ⟨hp, hlo, hend⟩
    · subst h0; simp at hkl
    icases ownSlice_elem_acc (sint.Z (W64 ((kk : Int) - 1))) els[kk - 1] _ _ els (by omega)
      hget $$ Hs with ⟨He, Hsback⟩
    wp_auto
    wp_apply WNext.wp_lvl_count hCnt K tx r m q X n bl rt ipg nl els pids hc hp hlo (kk - 1) hkl
      els[kk - 1] (by simp) _ $$ [Hw He] as ⟨Hw, He, %H63⟩
    · iframe; iframe #
    have hcm : sint.Z (W64 (WNext.cntAt X.v (wEs X n) pids els (kk - 1) : Int) - W64 1) =
        (WNext.cntAt X.v (wEs X n) pids els (kk - 1) : Int) - 1 := by word
    try wp_auto
    rw [hcm]
    rw [decide_eq_false (we_noMove nl X.v bl rt (wEs X n) pids els hp hend (kk - 1) hkl _ (by simp) H63)]
    wp_auto
    ihave Hs := Hsback $$ He
    rw [show els.set (sint.Z (W64 ((kk : Int) - 1))).toNat els[kk - 1] = els by
      rw [hkz, show ((kk : Int) - 1).toNat = kk - 1 by omega]; simp]
    wp_for_post
    iframe
    iexists kk - 1
    simp only [named]
    iframe
    isplitl
    · iExactEq i; congr 1
      rw [show ((kk - 1 : Nat) : Int) = (kk : Int) - 1 by omega]; word
    · ipureintro; omega
  · have hk0 : kk = 0 := by
      rcases Nat.eq_zero_or_pos kk with h | h
      · exact h
      · have hkz : sint.Z (W64 ((kk : Int) - 1)) = (kk : Int) - 1 := by word
        rw [hkz] at Hif; simp at Hif; omega
    subst hk0
    rw [decide_eq_true (by rfl)]
    wp_auto
    wp_for_post
    iapply HΦ
    iframe
    iexact Hown

theorem Cursor.next_w.wp_proofQ
    (hg : Cursor.goToFirstElementOnTheStack_w.specQ (GF := GF) (hG := hG))
    (hkv : Cursor.keyValue_ws.specQ (GF := GF) (hG := hG))
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG)) :
    Cursor.next_w.specQ (GF := GF) (hG := hG) := by
  sorry

end proof

end bbolt
end EtcdGrove
end Perennial
