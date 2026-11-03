/-
Lean-first (no Rocq counterpart). A reader's loans from the mapping's invariant (`mapLend`,
`DB.lean`): a Go load is not atomic (each byte is a `StartRead` and a `FinishRead`), so a reader
borrows a fraction of the cells it loads for the duration of its loads, and gives it back before
`RUnlock`.

- `meta_borrow`/`meta_return`: the meta cells, whole (their client halves), under `metalock`:
  the reader deposits half of `metaR`'s authority over the transactions and `metaDep` of `γm`.
- `page_borrow`/`page_return`: `s/4` of a committed page's cells, for a deposit `s` of `γm`.

Each keeps a sliver `q` of `γm` throughout, which rules out the closed invariant.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.MapInv

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.mit_pdos.etcd_grove.examples.bboltfs

/-- The meta cells' bytes in the meta pages' bytes `mp`. -/
def metasOf (mp : List w8) : List w8 := (mp.drop 16).take 64 ++ (mp.drop 4112).take 64

section loans
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

/-- The mapping's invariant, at its loan tokens `γl`. -/
abbrev mapInvL (γ : DBNames) (p : GoString) (base : Loc) (len : Nat) (γm γl : GName) : IProp GF :=
  inv mapN iprop(mapLend (GF := GF) γ p base len γm γl ∨ ghostVar γm 1 ())

/-- What a resource proves, keeping it. -/
theorem keep_pure {P : IProp GF} {φ : Prop} (h : P ⊢ ⌜φ⌝) : P ⊢ P ∗ ⌜φ⌝ := by
  iintro H
  icases (and_intro .rfl h : P ⊢ P ∧ ⌜φ⌝) $$ H with ⟨H, %hφ⟩
  iframe; ipureintro; exact hφ

theorem auth_gives (γ : GName) (q1 q2 : Qp) (m1 m2 : GMap Nat (Option w64)) :
    ghostMapAuth (GF := GF) γ q1 m1 ∗ ghostMapAuth γ q2 m2 ⊢
      (ghostMapAuth γ q1 m1 ∗ ghostMapAuth γ q2 m2) ∗ ⌜q1 + q2 ≤ 1 ∧ m1 = m2⌝ :=
  keep_pure (by iintro ⟨H1, H2⟩; iapply ghostMapAuth_valid_2 γ q1 q2 m1 m2 $$ H1 H2)

theorem elem_lookup (γl : GName) (K : GMap Nat (List w8)) (r : Nat) (dq : DFrac) (B : List w8) :
    ghostMapAuth (GF := GF) γl 1 K ∗ r ↪[γl]{dq} B ⊢
      (ghostMapAuth γl 1 K ∗ r ↪[γl]{dq} B) ∗ ⌜K.lookup r = some B⌝ :=
  keep_pure (by iintro ⟨H1, H2⟩; iapply ghost_map_lookup (V := List w8) $$ H1 H2)

theorem gv_false_one (γm : GName) (q : Qp) :
    ghostVar (GF := GF) γm q () ∗ ghostVar γm 1 () ⊢ False := by
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives % ⟨Hbad, _⟩
  exfalso
  simp only [Qp.le_iff, Qp.val_add, Qp.val_one] at Hbad
  have := q.2; grind

theorem range_set (L : List Nat) (i x : Nat) (h : L[i]? = some x) : L.set i x = L := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_set]
  split
  · subst_vars
    rw [h]; simp only [Option.map_some, ite_eq_left_iff]
    intro hn; exfalso; apply hn
    exact (List.getElem?_eq_some_iff.1 h).1
  · rfl

theorem range_get (r hwm : Nat) (h1 : 2 ≤ r) (h2 : r < hwm) :
    (List.range' 2 (hwm - 2))[r - 2]? = some r := by
  rw [List.getElem?_range' (by omega : r - 2 < hwm - 2)]
  congr 1; omega

/-- Committed page `r` of a `mapLend`, out of the others. -/
theorem pages_acc (P : Nat → IProp GF) (r hwm : Nat) (h1 : 2 ≤ r) (h2 : r < hwm) :
    ([∗list] r' ∈ List.range' 2 (hwm - 2), P r') ⊢
      P r ∗ (P r -∗ [∗list] r' ∈ List.range' 2 (hwm - 2), P r') := by
  iintro H
  have hg := range_get r hwm h1 h2
  ihave ⟨Hr, Hback⟩ := (BigSepL.bigSepL_lookup_acc (Φ := fun _ r' => P r') hg).1 $$ H
  iframe Hr
  iintro Hr
  ihave H := Hback $$ Hr
  rw [range_set _ _ _ hg]
  iexact H

theorem meta_borrow (γ : DBNames) (p : GoString) (base : Loc) (len : Nat) (γm γl : GName)
    (mp : List w8) (hwm : Nat) (T : GMap Nat (Option w64)) (q : Qp) :
    mapInvL (GF := GF) γ p base len γm γl ∗ ghostVar γm q () ∗
      ghostVar γ.cur (1 : Qp).half (mp, false, hwm) ∗ ghostVar γ.out (1 : Qp).half.half false ∗
      ghostMapAuth γ.txs 1 T ∗ ghostVar γm metaDep () ⊢
    |={⊤}=> ghostVar γm q () ∗ ghostVar γ.cur (1 : Qp).half (mp, false, hwm) ∗
      ghostMapAuth γ.txs (1 : Qp).half T ∗
      0 ↪[γl]{#(1 : Qp).half} (metasOf mp) ∗ metaBytes (GF := GF) base (DFrac.own (1 : Qp).half) (metasOf mp) := by
  iintro ⟨#Hinv, Hq, Hcur, Hout, Hauth, Hdep⟩
  imod inv_acc (by simp) $$ Hinv with ⟨Hi, Hclose⟩
  icases Hi with (>Hc | >Htok)
  · unfold mapLend
    icases Hc with ⟨%mp', %fl, %hwm', %K, Hcur', %Hl, Ha, %HK, Hpages, Hmeta⟩
    icombine Hcur Hcur' gives % ⟨_, Heq⟩
    cases Heq
    icases Hmeta with (⟨Hout', -⟩ | ⟨Hout', %mc, %Hmc, Hml⟩)
    · icombine Hout Hout' gives % ⟨_, Hbad⟩
      cases Hbad
    unfold metaLent
    icases Hml with (⟨Hk, Hb⟩ | ⟨-, ⟨%T', Ha'⟩, -, -⟩)
    · have hmc : mc = metasOf mp := Hmc.2 rfl
      subst hmc
      icases (ghostMapAuth_halves γ.txs T).1 $$ Hauth with ⟨Hauth, Hauth2⟩
      icases (ghostMapElem_halves γl 0 (metasOf mp)).1 $$ Hk with ⟨Hk, Hk2⟩
      imod Hclose $$ [Hcur' Ha Hpages Hout' Hout Hauth2 Hdep Hk2] with _
      · inext; ileft
        iexists mp, false, hwm, K
        iframe
        isplitr; · ipureintro; exact Hl
        isplitr; · ipureintro; exact HK
        iright; iframe
        iexists (metasOf mp)
        isplitr; · ipureintro; exact Hmc
        iright
        iframe Hout
        isplitl [Hauth2]; · iexists T; iexact Hauth2
        iframe
      imodintro
      iframe
    · icases auth_gives γ.txs _ _ T T' $$ [Hauth Ha'] with ⟨-, %Hbad⟩
      · iframe
      exfalso
      simp only [Qp.le_iff, Qp.val_add, Qp.val_one, Qp.val_half] at Hbad
      grind
  · iexfalso
    iapply gv_false_one γm q $$ [Hq Htok]
    iframe

theorem meta_return (γ : DBNames) (p : GoString) (base : Loc) (len : Nat) (γm γl : GName)
    (T : GMap Nat (Option w64)) (q : Qp) (mc : List w8) :
    mapInvL (GF := GF) γ p base len γm γl ∗ ghostVar γm q () ∗
      ghostMapAuth γ.txs (1 : Qp).half T ∗
      0 ↪[γl]{#(1 : Qp).half} mc ∗ metaBytes (GF := GF) base (DFrac.own (1 : Qp).half) mc ⊢
    |={⊤}=> ghostVar γm q () ∗ ghostVar γ.out (1 : Qp).half.half false ∗ ghostMapAuth γ.txs 1 T ∗
      ghostVar γm metaDep () := by
  iintro ⟨#Hinv, Hq, Hauth, Hk, Hb⟩
  imod inv_acc (by simp) $$ Hinv with ⟨Hi, Hclose⟩
  icases Hi with (>Hc | >Htok)
  · unfold mapLend
    icases Hc with ⟨%mp', %fl, %hwm', %K, Hcur', %Hl, Ha, %HK, Hpages, Hmeta⟩
    icases Hmeta with (⟨Hout', %mc', Hk'⟩ | ⟨Hout', %mc', %Hmc, Hml⟩)
    · icombine Hk Hk' gives % ⟨Hbad, _⟩
      exfalso
      have := DFrac.valid_op_own Hbad
      simp at this
    unfold metaLent
    icases Hml with (⟨Hk', -⟩ | ⟨Hout, ⟨%T', Ha'⟩, Hdep, Hk'⟩)
    · icombine Hk Hk' gives % ⟨Hbad, _⟩
      exfalso
      have := DFrac.valid_op_own Hbad
      simp at this
    · icombine Hk Hk' gives % ⟨_, Hmeq⟩
      subst Hmeq
      icases auth_gives γ.txs _ _ T T' $$ [Hauth Ha'] with ⟨⟨Hauth, Ha'⟩, %HT⟩
      · iframe
      obtain ⟨-, HT⟩ := HT
      subst HT
      ihave Hauth := (ghostMapAuth_halves γ.txs T).2 $$ [Hauth Ha']
      · iframe
      ihave Hk := (ghostMapElem_halves γl 0 mc).2 $$ [Hk Hk']
      · iframe
      imod Hclose $$ [Hcur' Ha Hpages Hout' Hk Hb] with _
      · inext; ileft
        iexists mp', fl, hwm', K
        iframe
        isplitr; · ipureintro; exact Hl
        isplitr; · ipureintro; exact HK
        iright; iframe
        iexists mc
        isplitr; · ipureintro; exact Hmc
        ileft; iframe
      imodintro
      iframe
  · iexfalso
    iapply gv_false_one γm q $$ [Hq Htok]
    iframe

theorem page_borrow (γ : DBNames) (p : GoString) (base : Loc) (len : Nat) (γm γl : GName)
    (mp : List w8) (hwm r : Nat) (q s : Qp) (h1 : 2 ≤ r) (h2 : r < hwm) :
    mapInvL (GF := GF) γ p base len γm γl ∗ ghostVar γm q () ∗
      ghostVar γ.cur (1 : Qp).half (mp, false, hwm) ∗ ghostVar γm s () ⊢
    |={⊤}=> ghostVar γm q () ∗ ghostVar γ.cur (1 : Qp).half (mp, false, hwm) ∗ ⌜4096 * hwm ≤ len⌝ ∗
      ∃ B, pageIs (GF := GF) p r B ∗ r ↪[γl]{#s.half.half} B ∗
        bytesPointsto (GF := GF) (base +ₗ ((4096 * r : Nat) : Int)) (DFrac.own s.half.half) B := by
  iintro ⟨#Hinv, Hq, Hcur, Hs⟩
  imod inv_acc (by simp) $$ Hinv with ⟨Hi, Hclose⟩
  icases Hi with (>Hc | >Htok)
  · unfold mapLend
    icases Hc with ⟨%mp', %fl, %hwm', %K, Hcur', %Hl, Ha, %HK, Hpages, Hmeta⟩
    icombine Hcur Hcur' gives % ⟨_, Heq⟩
    cases Heq
    icases pages_acc _ r hwm h1 h2 $$ Hpages with ⟨⟨%B, #HB, Hr⟩, Hback⟩
    icases lent_borrow γm γl r _ B s $$ [Hr Hs] with ⟨Hr, Hk, Hb⟩
    · iframe
    imod Hclose $$ [Hcur' Ha Hback Hr Hmeta] with _
    · inext; ileft
      iexists mp, false, hwm, K
      iframe
      isplitr; · ipureintro; exact Hl
      isplitr; · ipureintro; exact HK
      iapply Hback
      iexists B; iframe HB; iexact Hr
    imodintro
    iframe Hq Hcur
    isplitr; · ipureintro; exact Hl
    iexists B; iframe HB; iframe
  · iexfalso
    iapply gv_false_one γm q $$ [Hq Htok]
    iframe

/-- A committed page's contents, from the invariant. -/
theorem page_pageIs (γ : DBNames) (p : GoString) (base : Loc) (len : Nat) (γm γl : GName)
    (mp : List w8) (hwm r : Nat) (q : Qp) (h1 : 2 ≤ r) (h2 : r < hwm) :
    mapInvL (GF := GF) γ p base len γm γl ∗ ghostVar γm q () ∗
      ghostVar γ.cur (1 : Qp).half (mp, false, hwm) ⊢
    |={⊤}=> ghostVar γm q () ∗ ghostVar γ.cur (1 : Qp).half (mp, false, hwm) ∗
      ∃ B, pageIs (GF := GF) p r B := by
  iintro ⟨#Hinv, Hq, Hcur⟩
  imod inv_acc (by simp) $$ Hinv with ⟨Hi, Hclose⟩
  icases Hi with (>Hc | >Htok)
  · unfold mapLend
    icases Hc with ⟨%mp', %fl, %hwm', %K, Hcur', %Hl, Ha, %HK, Hpages, Hmeta⟩
    icombine Hcur Hcur' gives % ⟨_, Heq⟩
    cases Heq
    icases pages_acc _ r hwm h1 h2 $$ Hpages with ⟨⟨%B, #HB, Hr⟩, Hback⟩
    imod Hclose $$ [Hcur' Ha Hback Hr Hmeta] with _
    · inext; ileft
      iexists mp, false, hwm, K
      iframe
      isplitr; · ipureintro; exact Hl
      isplitr; · ipureintro; exact HK
      iapply Hback
      iexists B; iframe HB; iexact Hr
    imodintro
    iframe Hq Hcur
    iexists B; iexact HB
  · iexfalso
    iapply gv_false_one γm q $$ [Hq Htok]
    iframe

theorem page_return (γ : DBNames) (p : GoString) (base : Loc) (len : Nat) (γm γl : GName)
    (r : Nat) (q s : Qp) (B : List w8) (h1 : 2 ≤ r) :
    mapInvL (GF := GF) γ p base len γm γl ∗ ghostVar γm q () ∗ r ↪[γl]{#s.half.half} B ∗
      bytesPointsto (GF := GF) (base +ₗ ((4096 * r : Nat) : Int)) (DFrac.own s.half.half) B ⊢
    |={⊤}=> ghostVar γm q () ∗ ghostVar γm s () := by
  iintro ⟨#Hinv, Hq, Hk, Hb⟩
  imod inv_acc (by simp) $$ Hinv with ⟨Hi, Hclose⟩
  icases Hi with (>Hc | >Htok)
  · unfold mapLend
    icases Hc with ⟨%mp', %fl, %hwm', %K, Hcur', %Hl, Ha, %HK, Hpages, Hmeta⟩
    icases elem_lookup γl K r _ B $$ [Ha Hk] with ⟨⟨Ha, Hk⟩, %Hlk⟩
    · iframe
    have h2 : r < hwm' := by
      rcases Nat.lt_or_ge r hwm' with h | h
      · exact h
      · have := HK r (by omega) h
        rw [this] at Hlk; cases Hlk
    icases pages_acc _ r hwm' h1 h2 $$ Hpages with ⟨⟨%B', #HB, Hr⟩, Hback⟩
    icases lent_return γm γl r _ B' B s $$ [Hr Hk Hb] with ⟨Hr, Hs⟩
    · iframe
    imod Hclose $$ [Hcur' Ha Hback Hr Hmeta] with _
    · inext; ileft
      iexists mp', fl, hwm', K
      iframe
      isplitr; · ipureintro; exact Hl
      isplitr; · ipureintro; exact HK
      iapply Hback
      iexists B'; iframe HB; iexact Hr
    imodintro
    iframe
  · iexfalso
    iapply gv_false_one γm q $$ [Hq Htok]
    iframe

/-- The writer's view: whoever holds the whole of `metaR`'s authority over the transactions
(`metalock`) finds the meta cells unlent. -/
theorem metaLent_unlent (γ : DBNames) (γm γl : GName) (base : Loc) (mc : List w8)
    (T : GMap Nat (Option w64)) :
    metaLent (GF := GF) γ γm γl base mc ∗ ghostMapAuth γ.txs 1 T ⊢
      (0 ↪[γl] mc ∗ metaBytes (GF := GF) base (DFrac.own (1 : Qp).half) mc) ∗ ghostMapAuth γ.txs 1 T := by
  iintro ⟨Hml, Hauth⟩
  unfold metaLent
  icases Hml with (H | ⟨-, ⟨%T', Ha'⟩, -, -⟩)
  · iframe
  · icases auth_gives γ.txs _ _ T T' $$ [Hauth Ha'] with ⟨-, %Hbad⟩
    · iframe
    exfalso
    simp only [Qp.le_iff, Qp.val_add, Qp.val_one, Qp.val_half] at Hbad
    grind

theorem osBytes_disc_agree (p : GoString) :
    ∀ (xs ys : List (w8 × Bool)) (off : Nat), xs.length = ys.length →
    osBytes (GF := GF) p off DFrac.discard xs ∗ osBytes (GF := GF) p off DFrac.discard ys ⊢ ⌜xs = ys⌝
  | [], [], _, _ => by iintro -; ipureintro; rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | x :: xs, y :: ys, off, h => by
    iintro ⟨H1, H2⟩
    icases (osBytes_cons p off _ x xs).1 $$ H1 with ⟨Hx, H1⟩
    icases (osBytes_cons p off _ y ys).1 $$ H2 with ⟨Hy, H2⟩
    unfold osByte
    icases gElem_valid_2 _ _ _ _ _ x y $$ Hx Hy with %Hxy
    icases osBytes_disc_agree p xs ys (off + 1) (by simpa using h) $$ [H1 H2] with %Hr
    · iframe
    ipureintro
    rw [Hxy.2, Hr]

/-- Two views of a committed page agree. -/
theorem pageIs_agree (p : GoString) (r : Nat) (B B' : List w8) :
    pageIs (GF := GF) p r B ∗ pageIs (GF := GF) p r B' ⊢ ⌜B = B'⌝ := by
  unfold pageIs
  iintro ⟨⟨%Hl, H1⟩, ⟨%Hl', H2⟩⟩
  icases osBytes_disc_agree p (B.map (·, true)) (B'.map (·, true)) (4096 * r)
    (by simp only [List.length_map]; omega) $$ [H1 H2] with %H
  · iframe
  ipureintro
  have := congrArg (List.map Prod.fst) H
  simp only [List.map_map] at this
  have e : (Prod.fst ∘ fun x : w8 => (x, true)) = id := rfl
  rw [e, List.map_id, List.map_id] at this
  exact this

end loans

/-- `pickMeta` of the meta pages picks the current meta. -/
theorem pickMeta_cur [GooseExts] (mp : List w8) (m0 m1 : Loc)
    (h : metaValid (fileMeta mp 0) ∨ metaValid (fileMeta mp 1)) :
    (pickMetaRes m0 (fileMeta mp 0) m1 (fileMeta mp 1) = m0 ∧ curMeta mp = fileMeta mp 0) ∨
      (pickMetaRes m0 (fileMeta mp 0) m1 (fileMeta mp 1) = m1 ∧ curMeta mp = fileMeta mp 1) := by
  unfold pickMetaRes pickValid curMeta
  by_cases h1 : uint.Z (fileMeta mp 0).txid' < uint.Z (fileMeta mp 1).txid' <;>
    by_cases h2 : metaValid (fileMeta mp 0) <;> by_cases h3 : metaValid (fileMeta mp 1) <;>
    simp only [h1, h2, h3, if_true, if_false, true_and, and_true, true_or, or_true] <;> simp_all

/-- The meta cells' bytes as the two metas. -/
theorem metasOf_take [GooseExts] (mp : List w8) (h : mp.length = 8192) :
    (decode ((metasOf mp).take 64) : Meta) = fileMeta mp 0 ∧
      (decode ((metasOf mp).drop 64) : Meta) = fileMeta mp 1 := by
  unfold metasOf fileMeta pageMeta
  have h1 : ((mp.drop 16).take 64).length = 64 := by simp; omega
  constructor
  · rw [List.take_left' h1]; simp
  · rw [List.drop_left' h1, List.drop_drop]

theorem metasOf_length (mp : List w8) (h : mp.length = 8192) : (metasOf mp).length = 128 := by
  unfold metasOf; simp; omega

end github_com.mit_pdos.etcd_grove.examples.bboltfs

end Perennial
