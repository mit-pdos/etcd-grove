/-
`tx.recursivelyCheckPageKeyOrderInternal` of `tx_check.go` (U10h of `notes/bbolt-proof-plan.md`)
on a page of a reader's view whose tree has B+tree keys (`treeKeys`): nothing is sent; it returns
the subtree's last key (below the upper bound) when the page has an element. By induction on the
page's height (`pageHts`), as `forEachPageInternal` (`Tx__forEachPage_r.lean`).
-/
module

public import Proof.go_etcd_io.bbolt.Commit.CheckKeyOrderVerify
public import Spec.go_etcd_io.bbolt.Tx__page_r
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsBranchPage
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsLeafPage
public import Spec.go_etcd_io.bbolt.internal.common.Page__Count
public import Spec.go_etcd_io.bbolt.internal.common.Page__BranchPageElements
public import Spec.go_etcd_io.bbolt.internal.common.Page__BranchPageElement
public import Spec.go_etcd_io.bbolt.internal.common.Page__LeafPageElements
public import Spec.go_etcd_io.bbolt.internal.common.Page__LeafPageElement
public import Spec.go_etcd_io.bbolt.internal.common.branchPageElement__Pgid
public import Spec.go_etcd_io.bbolt.internal.common.branchPageElement__Key
public import Spec.go_etcd_io.bbolt.internal.common.leafPageElement__Key
public import Proof.go_etcd_io.bbolt.Read.Walk
public import Proof.go_etcd_io.bbolt.Read.BktOK
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

/-- A branch page's key, as `Key()` returns it, is bytes of the view. -/
theorem inViewAt_branchKey (v : View) (id : Nat) (pg : List w8) (h : v.pages !! id = some pg)
    (k : Nat) (hk : elemOff k + branchPos pg k + branchKsize pg k ≤ pg.length) :
    inViewAt v (slice.mk (pageLoc v id +ₗ ((elemOff k : Nat) : Int) +ₗ uint.Z (branchElem pg k).pos')
      (W64 (uint.Z (branchElem pg k).ksize')) (W64 (uint.Z (branchElem pg k).ksize')))
      (branchKey pg k) := by
  have hl := bytesAt_length pg (elemOff k + branchPos pg k) (branchKsize pg k) (by omega)
  have hks : branchKsize pg k < 2 ^ 32 := (branchElem pg k).ksize'.isLt
  have hz : uint.Z (branchElem pg k).ksize' = (branchKsize pg k : Int) := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := inViewLoc_page v id pg h (elemOff k + branchPos pg k) (branchKsize pg k) (by omega)
    have e : ((elemOff k : Nat) : Int) + uint.Z (branchElem pg k).pos' =
        ((elemOff k + branchPos pg k : Nat) : Int) := by push_cast; rfl
    rw [loc_add_assoc, e]; exact this
  · unfold branchKey; rw [hl]; exact hks
  · show W64 (uint.Z (branchElem pg k).ksize') = W64 ((branchKey pg k).length : Int)
    unfold branchKey; rw [hl, hz]
  · show W64 (uint.Z (branchElem pg k).ksize') = W64 ((branchKey pg k).length : Int)
    unfold branchKey; rw [hl, hz]

/-- A leaf page's key, as `Key()` returns it, is bytes of the view. -/
theorem inViewAt_leafKey (v : View) (id : Nat) (pg : List w8) (h : v.pages !! id = some pg)
    (k : Nat) (hk : elemOff k + leafPos pg k + leafKsize pg k ≤ pg.length) :
    inViewAt v (slice.mk (pageLoc v id +ₗ ((elemOff k : Nat) : Int) +ₗ uint.Z (leafElem pg k).pos')
      (W64 (uint.Z (leafElem pg k).ksize')) (W64 (uint.Z (leafElem pg k).ksize')))
      (leafKey pg k) := by
  have hl := bytesAt_length pg (elemOff k + leafPos pg k) (leafKsize pg k) (by omega)
  have hks : leafKsize pg k < 2 ^ 32 := (leafElem pg k).ksize'.isLt
  have hz : uint.Z (leafElem pg k).ksize' = (leafKsize pg k : Int) := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := inViewLoc_page v id pg h (elemOff k + leafPos pg k) (leafKsize pg k) (by omega)
    have e : ((elemOff k : Nat) : Int) + uint.Z (leafElem pg k).pos' =
        ((elemOff k + leafPos pg k : Nat) : Int) := by push_cast; rfl
    rw [loc_add_assoc, e]; exact this
  · unfold leafKey; rw [hl]; exact hks
  · show W64 (uint.Z (leafElem pg k).ksize') = W64 ((leafKey pg k).length : Int)
    unfold leafKey; rw [hl, hz]
  · show W64 (uint.Z (leafElem pg k).ksize') = W64 ((leafKey pg k).length : Int)
    unfold leafKey; rw [hl, hz]

end pure

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`tx.recursivelyCheckPageKeyOrderInternal(pgId, minKeyClosed, maxKeyOpen, pagesStack,
keyToString, ch)`** of a reader on page `pid` of its view, whose tree's keys are in `[lo, hi)`
(`treeKeys`), with `minKeyClosed` the lower bound `lo` or the page's first key and `maxKeyOpen`
the upper bound: nothing is sent; the result is a key of the view below `hi` when the page has an
element. -/
abbrev Tx.recursivelyCheckPageKeyOrderInternal_ok.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) (pid : w64)
    (pg : List w8) (hwm : Nat) (lo hi mn : Option (List w8)) (smn smx stk : GoSlice)
    (ids : List w64) (f : GoFunc) (ch : Loc),
  v.pages !! pid.toNat = some pg → treeWF v.pages hwm pid.toNat →
  treeKeys v.pages pid.toNat lo hi → keyOpt v smn mn →
  (mn = lo ∨ (0 < pageCount pg ∧ mn = some (pageKey pg 0))) → keyOpt v smx hi →
  {{ rdTxK (GF := GF) K tx src q T v ∗ stk ↦* ids ∗ ownSliceCap w64 stk (DFrac.own 1) }}
    (App (App (App (App (App (App (Val (tx @!! go.GoType.PointerType Tx.ty @!!
      go!"recursivelyCheckPageKeyOrderInternal")) (Val #pid)) (Val #smn)) (Val #smx)) (Val #stk))
      (Val #f)) (Val #ch))
  {{ (r : GoSlice), RET #r; rdTxK K tx src q T v ∗ stk ↦* ids ∗
      ownSliceCap w64 stk (DFrac.own 1) ∗
      ⌜0 < pageCount pg → ∃ k, inViewAt v r k ∧ keyLt k hi⌝ }}

set_option hygiene false in
/-- The end of an iteration of the branch loop: the recursive call on child `k` with the upper
bound `smk`, and the invariant at `j + 1`. -/
local macro "rk_tail" : tactic => `(tactic| (
  icases rdTxK_elem_acc (V := branchPageElement) K tx src q T v pid.toNat pg hpg k hel $$ Hk
    with ⟨%dqe3, Hel, Helb⟩
  rw [show (decode (bytesAt pg (elemOff k) 16) : branchPageElement) = branchElem pg k from rfl, hbe]
  wp_apply hBP (pageLoc v pid.toNat +ₗ ((elemOff k : Nat) : Int)) be dqe3 $$ [Hel]
    as Hel
  · iexact Hel
  try wp_auto
  wp_apply hBK (pageLoc v pid.toNat +ₗ ((elemOff k : Nat) : Int)) be dqe3 hlpos
    hlbnd $$ [Hel] as Hel
  · iexact Hel
  ihave Hk := Helb $$ Hel
  try wp_auto
  obtain ⟨cpg, hcpg, hcpos, hck0⟩ := hkids k hkc
  have hht := (hpht pid.toNat pg hpg).2 hbr k hkc
  wp_apply (ih m (by omega) K tx src q T v be.pgid' cpg hwm
    (childLo lo (branchKey pg) k) (childHi hi (branchKey pg) (pageCount pg) k)
    (some (branchKey pg k)) _ _ s1 (ids ++ [pid]) f ch hpht
    (by rw [hpgid]; omega) (by rw [hpgid]; exact hcpg) (by rw [hpgid]; exact hch k hkc)
    (by rw [hpgid]; exact hkch k hkc) hkey
    (Or.inr ⟨hcpos, by rw [hck0]⟩) hsmk) $$ [Hk Hs Hcap] as %r ⟨Hk, Hs, Hcap, %Hr⟩
  · iframe
  try wp_auto
  wp_for_post
  iframe
  iexists j + W64 1, j, r, r
  iframe
  ipureintro
  have hj1 : sint.Z (j + W64 1) = (k : Int) + 1 := by
    have := hkc; have := hcnt16; word
  refine ⟨by omega, by omega, fun h => absurd h (by omega), fun _ => ⟨rfl, ?_⟩⟩
  obtain ⟨kp, hin, hkl⟩ := Hr hcpos
  refine ⟨kp, hin, ?_⟩
  rw [hj1, show ((k : Int) + 1).toNat - 1 = k by omega]
  exact hkl))

/-- The internal check on a page of height below `n`. -/
theorem rcpkoInternal_rec
    (hpage : Tx.page_r.spec (GF := GF) (hG := hG))
    (hIB : internal.common.Page.IsBranchPage.spec (GF := GF) (hG := hG))
    (hIL : internal.common.Page.IsLeafPage.spec (GF := GF) (hG := hG))
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG))
    (hBEs : internal.common.Page.BranchPageElements.spec (GF := GF) (hG := hG))
    (hBE : internal.common.Page.BranchPageElement.spec (GF := GF) (hG := hG))
    (hLEs : internal.common.Page.LeafPageElements.spec (GF := GF) (hG := hG))
    (hLE : internal.common.Page.LeafPageElement.spec (GF := GF) (hG := hG))
    (hBP : internal.common.branchPageElement.Pgid.spec (GF := GF) (hG := hG))
    (hBK : internal.common.branchPageElement.Key.spec (GF := GF) (hG := hG))
    (hLK : internal.common.leafPageElement.Key.spec (GF := GF) (hG := hG))
    (wp_vko : verifyKeyOrder_ok.spec (GF := GF) (hG := hG))
    (pht : Nat → Nat) :
    ∀ (n : Nat) (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) (pid : w64)
      (pg : List w8) (hwm : Nat) (lo hi mn : Option (List w8)) (smn smx stk : GoSlice)
      (ids : List w64) (f : GoFunc) (ch : Loc),
    pageHts v.pages pht → pht pid.toNat < n →
    v.pages !! pid.toNat = some pg → treeWF v.pages hwm pid.toNat →
    treeKeys v.pages pid.toNat lo hi → keyOpt v smn mn →
    (mn = lo ∨ (0 < pageCount pg ∧ mn = some (pageKey pg 0))) → keyOpt v smx hi →
    {{ rdTxK (GF := GF) K tx src q T v ∗ stk ↦* ids ∗ ownSliceCap w64 stk (DFrac.own 1) }}
      (App (App (App (App (App (App (Val (tx @!! go.GoType.PointerType Tx.ty @!!
        go!"recursivelyCheckPageKeyOrderInternal")) (Val #pid)) (Val #smn)) (Val #smx)) (Val #stk))
        (Val #f)) (Val #ch))
    {{ (r : GoSlice), RET #r; rdTxK K tx src q T v ∗ stk ↦* ids ∗
        ownSliceCap w64 stk (DFrac.own 1) ∗
        ⌜0 < pageCount pg → ∃ k, inViewAt v r k ∧ keyLt k hi⌝ }} := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro K tx src q T v pid pg hwm lo hi mn smn smx stk ids f ch hpht hn hpg hwf hkeys hmn hmn' hmx
  wp_start as ⟨Hk, Hs, Hcap⟩
  ihave #Hpkg := rdTxK_pkgInit K tx src q T v $$ Hk
  ihave %Hb := rdTxK_base_pos K tx src q T v $$ Hk
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  wp_auto
  wp_apply hpage K tx src q T v pid pg hpg $$ [Hk] as Hk
  · iexact Hk
  try wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl1 ⟨Hsl1, -⟩
  wp_apply wp_slice_append_undo $$ [$Hs $Hcap $Hsl1] as %s1 ⟨Hs, Hcap, -, Hundo⟩
  try wp_auto
  obtain ⟨hplen, hpt⟩ : pg.length = (1 + pageOverflow pg) * 4096 ∧
      pageTreeWF v.pages hwm pg pg.length := by
    cases hwf with
    | page _ pg' _ _ hpg' _ hplen hpt =>
      rw [hpg] at hpg'; cases hpg'
      exact ⟨hplen, hpt⟩
  have h16 : 16 ≤ pg.length := by
    have := Nat.le_mul_of_pos_left 4096 (show 0 < 1 + pageOverflow pg by omega)
    omega
  icases rdTxK_page_bounds K tx src q T v pid.toNat pg hpg (by intro e; simp [e] at h16) $$ Hk
    with ⟨Hk, %Hlb⟩
  icases rdTxK_hdr_acc K tx src q T v pid.toNat pg hpg h16 $$ Hk with ⟨%dqh, Hh, Hhb⟩
  obtain ⟨hd, hH⟩ : ∃ hd, pageHdr pg = hd := ⟨_, rfl⟩
  have hfz : pageFlags pg = hd.flags'.toNat := by unfold pageFlags; rw [hH]
  have hcz : pageCount pg = hd.count'.toNat := by unfold pageCount; rw [hH]
  rw [hH]
  wp_apply hIB (pageLoc v pid.toNat) hd dqh $$ [Hh] as Hh
  · iexact Hh
  rcases hpt with ⟨_, _, hlf, hlwf, hbk⟩ | ⟨_, _, hbr, hbwf, hch⟩
  · -- a leaf
    have hf2 : hd.flags' = W16 2 := by
      apply BitVec.eq_of_toNat_eq; rw [← hfz, hlf]; rfl
    rw [hf2]
    wp_auto
    wp_apply hIL (pageLoc v pid.toNat) hd dqh $$ [Hh] as Hh
    · iexact Hh
    rw [hf2]
    wp_auto
    obtain ⟨-, hcnt, helems, hsorted⟩ := hlwf
    have hkin : ∀ i < pageCount pg, keyIn lo hi (leafKey pg i) := by
      cases hkeys with
      | leaf _ pg3 _ _ hpg3 _ hk1 _ =>
        rw [hpg] at hpg3; cases hpg3; exact hk1
      | branch _ pg3 _ _ kind hpg3 hf3 _ _ _ _ =>
        rw [hpg] at hpg3; cases hpg3; rw [hlf] at hf3; exact absurd hf3 (by decide)
    have hpk0 : pageKey pg 0 = leafKey pg 0 := by
      unfold pageKey; rw [ite_eq_left (by rw [hlf]; rfl)]
    have hcnt16 : pageCount pg < 2 ^ 16 := by rw [hcz]; exact BitVec.isLt _
    wp_apply hLEs (pageLoc v pid.toNat) hd dqh Hlb.1
      (by have := Hlb.2; unfold elemOff at hcnt; rw [show uint.Z hd.count' = (pageCount pg : Int) by
        rw [hcz]]; omega) $$ [Hh] as Hh
    · iexact Hh
    ihave Hk := Hhb $$ Hh
    obtain ⟨sl, hsl⟩ : ∃ sl : GoSlice, (if hd.count' = W16 0 then slice.nil
        else slice.mk (pageLoc v pid.toNat +ₗ 16) (W64 (uint.Z hd.count')) (W64 (uint.Z hd.count')))
        = sl := ⟨_, rfl⟩
    rw [hsl]
    have hcw : sint.Z (W64 (uint.Z hd.count')) = (pageCount pg : Int) := by
      rw [hcz]; have := hd.count'.isLt; word
    have hsll : sint.Z sl.len = (pageCount pg : Int) := by
      rw [← hsl]; split
      · rename_i h; rw [hcz, h]; rfl
      · exact hcw
    have hslm : 0 < pageCount pg → sl = slice.mk (pageLoc v pid.toNat +ₗ 16)
        (W64 (uint.Z hd.count')) (W64 (uint.Z hd.count')) := by
      intro hc; rw [← hsl, if_neg]; intro h
      have : (pageCount pg : Int) = 0 := by rw [hcz, h]; rfl
      omega
    rename_i iu_ptr
    irename : iu_ptr ↦ (zero_val w64) => Hiu
    ihave IH : (∃ (j uv : w64) (rm : GoSlice),
        "i" ∷ i_ptr ↦ j ∗ "Hiu" ∷ iu_ptr ↦ uv ∗ "runningMin" ∷ runningMin_ptr ↦ rm ∗
        "Hk" ∷ rdTxK K tx src q T v ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ (pageCount pg : Int) ∧
          (sint.Z j = 0 → rm = smn) ∧
          (0 < sint.Z j → inViewAt v rm (leafKey pg ((sint.Z j).toNat - 1)))⌝ : IProp GF)
      $$ [i Hiu runningMin Hk]
    · iexists W64 0, W64 0, smn
      simp only [named]
      iframe
      ipureintro
      refine ⟨by decide, by rw [show sint.Z (W64 0) = 0 from rfl]; omega, by simp, ?_⟩
      intro h; exact absurd h (by decide)
    wp_for IH
    rw [hsll]
    by_cases hjc : sint.Z j < (pageCount pg : Int)
    · rw [decide_eq_true hjc]
      simp only [_root_.decide_true, ↓reduceIte]
      wp_auto
      obtain ⟨k, hk⟩ : ∃ k : Nat, sint.Z j = (k : Int) := ⟨(sint.Z j).toNat, by omega⟩
      have hkc : k < pageCount pg := by omega
      have hk16 : uint.Z (W16 (sint.Z j)) = (k : Int) := by rw [hk]; word
      have hel : elemOff k + 16 ≤ pg.length := by unfold elemOff at hcnt ⊢; omega
      have hloc0 : sliceIndexRef leafPageElement (sint.Z j) sl =
          pageLoc v pid.toNat +ₗ ((elemOff k : Nat) : Int) := by
        rw [hslm (by omega)]
        rw [sliceIndexRef_plain leafPageElement.ty leafPageElement.layout _ j
          (by simp [Loc.add]; omega) Hj.1]
        simp only [sint.nat, hk, Int.toNat_natCast, loc_add_assoc, elemOff]
        congr 1; push_cast; omega
      rw [hsll, ite_eq_left ⟨Hj.1, by omega⟩, hloc0]
      icases rdTxK_elem_acc (V := leafPageElement) K tx src q T v pid.toNat pg hpg k hel $$ Hk
        with ⟨%dqe, Hel, Helb⟩
      rw [show (decode (bytesAt pg (elemOff k) 16) : leafPageElement) = leafElem pg k from rfl]
      wp_auto
      ihave Hk := Helb $$ Hel
      wp_apply hLE (pageLoc v pid.toNat) (W16 (sint.Z j)) Hlb.1
        (by rw [hk16]; unfold elemOff at hel; omega)
      have hloc : pageLoc v pid.toNat +ₗ (16 + 16 * uint.Z (W16 (sint.Z j))) =
          pageLoc v pid.toNat +ₗ ((elemOff k : Nat) : Int) := by
        rw [hk16]; unfold elemOff; push_cast; rfl
      rw [hloc]
      try wp_auto
      obtain ⟨hke1, -⟩ := helems k hkc
      have he1 : uint.Z (leafElem pg k).pos' = (leafPos pg k : Int) := rfl
      have he2 : uint.Z (leafElem pg k).ksize' = (leafKsize pg k : Int) := rfl
      have hlpos : 0 < (pageLoc v pid.toNat +ₗ ((elemOff k : Nat) : Int)).addr := by
        simp only [Loc.add]; omega
      have hlbnd : (pageLoc v pid.toNat +ₗ ((elemOff k : Nat) : Int)).addr +
          uint.Z (leafElem pg k).pos' + uint.Z (leafElem pg k).ksize' ≤ maxAddr := by
        rw [he1, he2]; have := Hlb.2; simp only [Loc.add]; omega
      have hkk : elemOff k + leafPos pg k + leafKsize pg k ≤ pg.length := by omega
      have hkey := inViewAt_leafKey v pid.toNat pg hpg k hkk
      obtain ⟨le, hle⟩ : ∃ le, leafElem pg k = le := ⟨_, rfl⟩
      rw [hle] at hlbnd hkey
      icases rdTxK_elem_acc (V := leafPageElement) K tx src q T v pid.toNat pg hpg k hel $$ Hk
        with ⟨%dqe2, Hel, Helb⟩
      rw [show (decode (bytesAt pg (elemOff k) 16) : leafPageElement) = leafElem pg k from rfl, hle]
      wp_apply hLK (pageLoc v pid.toNat +ₗ ((elemOff k : Nat) : Int)) le dqe2 hlpos
        hlbnd $$ [Hel] as Hel
      · iexact Hel
      ihave Hk := Helb $$ Hel
      try wp_auto

      obtain ⟨po, hpo, hpo0, hpo1⟩ : ∃ po, keyOpt v rm po ∧ (k = 0 → po = mn) ∧
          (0 < k → po = some (leafKey pg (k - 1))) := by
        by_cases hk0 : k = 0
        · refine ⟨mn, ?_, fun _ => rfl, fun h => absurd h (by omega)⟩
          rw [Hj.2.2.1 (by omega)]; exact hmn
        · refine ⟨some (leafKey pg (k - 1)), ?_, fun h => absurd h hk0, fun _ => rfl⟩
          have := Hj.2.2.2 (by omega)
          rw [hk] at this; show inViewAt v rm _; simpa using this
      have hjk : j = W64 0 ↔ k = 0 := by
        constructor
        · intro h; subst h; simp at hk; omega
        · intro h; subst h; apply BitVec.eq_of_toInt_eq; simpa using hk
      wp_apply wp_vko K tx src q T v _ _ j _ rm smx (leafKey pg k) po hi ch f s1 hkey hpo hmx
        (fun hj0 => by
          have hk0 := hjk.1 hj0
          subst hk0
          rw [hpo0 rfl]
          rcases hmn' with rfl | ⟨-, rfl⟩
          · exact (hkin 0 hkc).1
          · rw [hpk0]; intro l hl; cases hl; exact go.goStringLt_irrefl _)
        (fun hj0 => by
          have hk0 : 0 < k := by
            rcases Nat.eq_zero_or_pos k with h | h
            · exact absurd (hjk.2 h) hj0
            · exact h
          refine ⟨by omega, leafKey pg (k - 1), hpo1 hk0, hsorted _ _ (by omega) hkc⟩)
        (hkin k hkc).2 $$ [Hk] as Hk
      · iexact Hk
      try wp_auto
      icases rdTxK_elem_acc (V := leafPageElement) K tx src q T v pid.toNat pg hpg k hel $$ Hk
        with ⟨%dqe3, Hel, Helb⟩
      rw [show (decode (bytesAt pg (elemOff k) 16) : leafPageElement) = leafElem pg k from rfl, hle]
      wp_apply hLK (pageLoc v pid.toNat +ₗ ((elemOff k : Nat) : Int)) le dqe3 hlpos
        hlbnd $$ [Hel] as Hel
      · iexact Hel
      ihave Hk := Helb $$ Hel
      try wp_auto
      wp_for_post
      iframe
      iexists j + W64 1, j, _
      iframe
      ipureintro
      have hj1 : sint.Z (j + W64 1) = (k : Int) + 1 := by
        have := hkc; have := hcnt16; word
      refine ⟨by omega, by omega, fun h => absurd h (by omega), fun _ => ?_⟩
      rw [hj1, show ((k : Int) + 1).toNat - 1 = k by omega]
      exact hkey
    · rw [decide_eq_false hjc]
      have hne : (#false : val) ≠ #true := fun h => absurd (GoGlobalContext.intoVal_inj_bool h) (by decide)
      simp only [hne, decide_false, _root_.decide_true, Bool.false_eq_true, ↓reduceIte]
      wp_auto
      have hjn : (sint.Z j).toNat = pageCount pg := by omega
      icases rdTxK_hdr_acc K tx src q T v pid.toNat pg hpg h16 $$ Hk with ⟨%dqh2, Hh, Hhb⟩
      rw [hH]
      wp_apply hCnt (pageLoc v pid.toNat) hd dqh2 $$ [Hh] as Hh
      · iexact Hh
      ihave Hk := Hhb $$ Hh
      have hcu : uint.Z hd.count' = (pageCount pg : Int) := by rw [hcz]
      by_cases hc0 : pageCount pg = 0
      · rw [decide_eq_false (show ¬ uint.Z (W16 0) < uint.Z hd.count' by rw [hcu, hc0]; decide)]
        wp_auto
        ihave Hb := Hundo $$ [Hs Hcap]
        · iframe
        icases Hb with ⟨Hs, Hcap⟩
        iapply HΦ
        iframe
        ipureintro
        intro h; omega
      · rw [decide_eq_true (show uint.Z (W16 0) < uint.Z hd.count' by
          rw [hcu]; show (0 : Int) < _; omega)]
        wp_auto
        icases rdTxK_hdr_acc K tx src q T v pid.toNat pg hpg h16 $$ Hk with ⟨%dqh3, Hh, Hhb⟩
        rw [hH]
        wp_apply hCnt (pageLoc v pid.toNat) hd dqh3 $$ [Hh] as Hh
        · iexact Hh
        ihave Hk := Hhb $$ Hh
        try wp_auto
        obtain ⟨c, hc⟩ : ∃ c, pageCount pg = c + 1 := ⟨pageCount pg - 1, by omega⟩
        have hcm : uint.Z (hd.count' - W16 1) = (c : Int) := by
          have h1 : uint.Z hd.count' = (c : Int) + 1 := by rw [hcu, hc]; push_cast; rfl
          have := hcnt16; word
        have helc : elemOff c + 16 ≤ pg.length := by unfold elemOff at hcnt ⊢; omega
        wp_apply hLE (pageLoc v pid.toNat) (hd.count' - W16 1) Hlb.1
          (by rw [hcm]; unfold elemOff at helc; omega)
        have hlocc : pageLoc v pid.toNat +ₗ (16 + 16 * uint.Z (hd.count' - W16 1)) =
            pageLoc v pid.toNat +ₗ ((elemOff c : Nat) : Int) := by
          rw [hcm]; unfold elemOff; push_cast; rfl
        rw [hlocc]
        try wp_auto
        obtain ⟨hkc1, -⟩ := helems c (by omega)
        have hkkc : elemOff c + leafPos pg c + leafKsize pg c ≤ pg.length := by omega
        have hkeyc := inViewAt_leafKey v pid.toNat pg hpg c hkkc
        have hbc : (pageLoc v pid.toNat +ₗ ((elemOff c : Nat) : Int)).addr +
            uint.Z (leafElem pg c).pos' + uint.Z (leafElem pg c).ksize' ≤ maxAddr := by
          rw [show uint.Z (leafElem pg c).pos' = (leafPos pg c : Int) from rfl,
            show uint.Z (leafElem pg c).ksize' = (leafKsize pg c : Int) from rfl]
          have := Hlb.2; simp only [Loc.add]; omega
        obtain ⟨lc, hlc⟩ : ∃ le, leafElem pg c = le := ⟨_, rfl⟩
        rw [hlc] at hkeyc hbc
        icases rdTxK_elem_acc (V := leafPageElement) K tx src q T v pid.toNat pg hpg c helc $$ Hk
          with ⟨%dqe5, Hel, Helb⟩
        rw [show (decode (bytesAt pg (elemOff c) 16) : leafPageElement) = leafElem pg c from rfl, hlc]
        wp_apply hLK (pageLoc v pid.toNat +ₗ ((elemOff c : Nat) : Int)) lc dqe5
          (by simp only [Loc.add]; omega) hbc $$ [Hel] as Hel
        · iexact Hel
        ihave Hk := Helb $$ Hel
        try wp_auto
        ihave Hb := Hundo $$ [Hs Hcap]
        · iframe
        icases Hb with ⟨Hs, Hcap⟩
        iapply HΦ
        iframe
        ipureintro
        intro _
        exact ⟨_, hkeyc, (hkin c (by omega)).2⟩
  · -- a branch
    have hf1 : hd.flags' = W16 1 := by
      apply BitVec.eq_of_toNat_eq; rw [← hfz, hbr]; rfl
    rw [hf1]
    wp_auto
    obtain ⟨hc0, -, hcnt, helems, hsorted⟩ := hbwf
    obtain ⟨hkin, hkids, hkch⟩ : (∀ i < pageCount pg, keyIn lo hi (branchKey pg i)) ∧
        (∀ i < pageCount pg, ∃ cpg, v.pages !! branchPgid pg i = some cpg ∧ 0 < pageCount cpg ∧
          pageKey cpg 0 = branchKey pg i) ∧
        (∀ i < pageCount pg, treeKeys v.pages (branchPgid pg i) (childLo lo (branchKey pg) i)
          (childHi hi (branchKey pg) (pageCount pg) i)) := by
      cases hkeys with
      | leaf _ pg3 _ _ hpg3 hf3 _ _ =>
        rw [hpg] at hpg3; cases hpg3; rw [hbr] at hf3; exact absurd hf3 (by decide)
      | branch _ pg3 _ _ kind hpg3 _ _ hk1 hk2 hk3 =>
        rw [hpg] at hpg3; cases hpg3
        refine ⟨hk1, fun i hi => ?_, hk3⟩
        obtain ⟨c, a, b, -, d⟩ := hk2 i hi
        exact ⟨c, a, b, d⟩
    have hpk0 : pageKey pg 0 = branchKey pg 0 := by
      unfold pageKey; rw [ite_eq_right (by rw [hbr]; decide)]
    have hcnt16 : pageCount pg < 2 ^ 16 := by rw [hcz]; exact BitVec.isLt _
    wp_apply hBEs (pageLoc v pid.toNat) hd dqh Hlb.1
      (by have := Hlb.2; unfold elemOff at hcnt; rw [show uint.Z hd.count' = (pageCount pg : Int) by
        rw [hcz]]; omega) $$ [Hh] as Hh
    · iexact Hh
    have hcnz : hd.count' ≠ W16 0 := by
      intro h
      have : (pageCount pg : Int) = 0 := by rw [hcz, h]; rfl
      omega
    rw [if_neg hcnz]
    ihave Hk := Hhb $$ Hh
    rename_i iu_ptr
    irename : iu_ptr ↦ (zero_val w64) => Hiu
    have hcw : sint.Z (W64 (uint.Z hd.count')) = (pageCount pg : Int) := by
      rw [hcz]; have := hd.count'.isLt; word
    ihave IH : (∃ (j uv : w64) (rm mk : GoSlice),
        "i" ∷ i_ptr ↦ j ∗ "Hiu" ∷ iu_ptr ↦ uv ∗ "runningMin" ∷ runningMin_ptr ↦ rm ∗
        "maxKeyInSubtree" ∷ maxKeyInSubtree_ptr ↦ mk ∗ "Hk" ∷ rdTxK K tx src q T v ∗
        "Hs" ∷ s1 ↦* (ids ++ [pid]) ∗ "Hcap" ∷ ownSliceCap w64 s1 (DFrac.own 1) ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ (pageCount pg : Int) ∧
          (sint.Z j = 0 → rm = smn) ∧
          (0 < sint.Z j → rm = mk ∧ ∃ kp, inViewAt v mk kp ∧
            keyLt kp (childHi hi (branchKey pg) (pageCount pg) ((sint.Z j).toNat - 1)))⌝ : IProp GF)
      $$ [i Hiu runningMin maxKeyInSubtree Hk Hs Hcap]
    · iexists W64 0, W64 0, smn, zero_val GoSlice
      simp only [named]
      iframe
      ipureintro
      refine ⟨by decide, by rw [show sint.Z (W64 0) = 0 from rfl]; omega, by simp, ?_⟩
      intro h; exact absurd h (by decide)
    wp_for IH
    rw [hcw]
    by_cases hjc : sint.Z j < (pageCount pg : Int)
    · rw [decide_eq_true hjc]
      simp only [_root_.decide_true, ↓reduceIte]
      wp_auto
      obtain ⟨k, hk⟩ : ∃ k : Nat, sint.Z j = (k : Int) := ⟨(sint.Z j).toNat, by omega⟩
      have hkc : k < pageCount pg := by omega
      have hk16 : uint.Z (W16 (sint.Z j)) = (k : Int) := by rw [hk]; word
      have hel : elemOff k + 16 ≤ pg.length := by unfold elemOff at hcnt ⊢; omega
      have hloc0 : sliceIndexRef branchPageElement (sint.Z j)
          (slice.mk (pageLoc v pid.toNat +ₗ 16) (W64 (uint.Z hd.count')) (W64 (uint.Z hd.count'))) =
          pageLoc v pid.toNat +ₗ ((elemOff k : Nat) : Int) := by
        rw [sliceIndexRef_plain branchPageElement.ty branchPageElement.layout _ j
          (by simp [Loc.add]; omega) Hj.1]
        simp only [sint.nat, hk, Int.toNat_natCast, loc_add_assoc, elemOff]
        congr 1; push_cast; omega
      rw [hcw, ite_eq_left ⟨Hj.1, by omega⟩, hloc0]
      icases rdTxK_elem_acc (V := branchPageElement) K tx src q T v pid.toNat pg hpg k hel $$ Hk
        with ⟨%dqe, Hel, Helb⟩
      rw [show (decode (bytesAt pg (elemOff k) 16) : branchPageElement) = branchElem pg k from rfl]
      wp_auto
      ihave Hk := Helb $$ Hel
      wp_apply hBE (pageLoc v pid.toNat) (W16 (sint.Z j)) Hlb.1
        (by rw [hk16]; unfold elemOff at hel; omega)
      have hloc : pageLoc v pid.toNat +ₗ (16 + 16 * uint.Z (W16 (sint.Z j))) =
          pageLoc v pid.toNat +ₗ ((elemOff k : Nat) : Int) := by
        rw [hk16]; unfold elemOff; push_cast; rfl
      rw [hloc]
      try wp_auto
      obtain ⟨hke1, hke2, hkpg⟩ := helems k hkc
      have he1 : uint.Z (branchElem pg k).pos' = (branchPos pg k : Int) := rfl
      have he2 : uint.Z (branchElem pg k).ksize' = (branchKsize pg k : Int) := rfl
      have hlpos : 0 < (pageLoc v pid.toNat +ₗ ((elemOff k : Nat) : Int)).addr := by
        simp only [Loc.add]; omega
      have hlbnd : (pageLoc v pid.toNat +ₗ ((elemOff k : Nat) : Int)).addr +
          uint.Z (branchElem pg k).pos' + uint.Z (branchElem pg k).ksize' ≤ maxAddr := by
        rw [he1, he2]; have := Hlb.2; simp only [Loc.add]; omega
      have hkey := inViewAt_branchKey v pid.toNat pg hpg k hke1
      obtain ⟨be, hbe⟩ : ∃ be, branchElem pg k = be := ⟨_, rfl⟩
      have hpgid : be.pgid'.toNat = branchPgid pg k := by rw [← hbe]; rfl
      rw [hbe] at hlbnd hkey
      icases rdTxK_elem_acc (V := branchPageElement) K tx src q T v pid.toNat pg hpg k hel $$ Hk
        with ⟨%dqe2, Hel, Helb⟩
      rw [show (decode (bytesAt pg (elemOff k) 16) : branchPageElement) = branchElem pg k from rfl,
        hbe]
      wp_apply hBP (pageLoc v pid.toNat +ₗ ((elemOff k : Nat) : Int)) be dqe2 $$ [Hel]
        as Hel
      · iexact Hel
      try wp_auto
      wp_apply hBK (pageLoc v pid.toNat +ₗ ((elemOff k : Nat) : Int)) be dqe2 hlpos
        hlbnd $$ [Hel] as Hel
      · iexact Hel
      ihave Hk := Helb $$ Hel
      try wp_auto
      obtain ⟨po, hpo, hpo0, hpo1⟩ : ∃ po, keyOpt v rm po ∧ (k = 0 → po = mn) ∧
          (0 < k → ∃ kp, po = some kp ∧
            keyLt kp (childHi hi (branchKey pg) (pageCount pg) (k - 1))) := by
        by_cases hk0 : k = 0
        · refine ⟨mn, ?_, fun _ => rfl, fun h => absurd h (by omega)⟩
          rw [Hj.2.2.1 (by omega)]; exact hmn
        · obtain ⟨hrm, kp, hin, hkl⟩ := Hj.2.2.2 (by omega)
          refine ⟨some kp, by rw [hrm]; exact hin, fun h => absurd h hk0, fun _ => ⟨kp, rfl, ?_⟩⟩
          rw [hk] at hkl; simpa using hkl
      have hjk : j = W64 0 ↔ k = 0 := by
        constructor
        · intro h; subst h; simp at hk; omega
        · intro h; subst h; apply BitVec.eq_of_toInt_eq; simpa using hk
      wp_apply wp_vko K tx src q T v _ _ j _ rm smx (branchKey pg k) po hi ch f s1 hkey hpo hmx
        (fun hj0 => by
          have hk0 := hjk.1 hj0
          subst hk0
          rw [hpo0 rfl]
          rcases hmn' with rfl | ⟨-, rfl⟩
          · exact (hkin 0 hc0).1
          · rw [hpk0]; intro l hl; cases hl; exact go.goStringLt_irrefl _)
        (fun hj0 => by
          have hk0 : 0 < k := by
            rcases Nat.eq_zero_or_pos k with h | h
            · exact absurd (hjk.2 h) hj0
            · exact h
          refine ⟨by omega, ?_⟩
          obtain ⟨kp, hkp, hkl⟩ := hpo1 hk0
          refine ⟨kp, hkp, hkl _ ?_⟩
          unfold childHi; rw [ite_eq_left (by omega)]
          congr 2; omega)
        (hkin k hkc).2 $$ [Hk] as Hk
      · iexact Hk
      try wp_auto
      icases rdTxK_hdr_acc K tx src q T v pid.toNat pg hpg h16 $$ Hk with ⟨%dqh2, Hh, Hhb⟩
      rw [hH]
      wp_apply hBEs (pageLoc v pid.toNat) hd dqh2 Hlb.1
        (by have := Hlb.2; unfold elemOff at hcnt; rw [show uint.Z hd.count' = (pageCount pg : Int) by
          rw [hcz]]; omega) $$ [Hh] as Hh
      · iexact Hh
      rw [if_neg hcnz]
      ihave Hk := Hhb $$ Hh
      try wp_auto
      have hcw1 : sint.Z (W64 (uint.Z hd.count') - W64 1) = (pageCount pg : Int) - 1 := by
        have := hc0; have := hcnt16; rw [hcz] at *; word
      rw [hcw1]
      by_cases hlast : k + 1 < pageCount pg
      · rw [decide_eq_true (show sint.Z j < (pageCount pg : Int) - 1 by omega)]
        wp_auto
        have hk16' : uint.Z (W16 (sint.Z (j + W64 1))) = ((k + 1 : Nat) : Int) := by
          have := hkc; have := hcnt16; push_cast; rw [show sint.Z (j + W64 1) = (k : Int) + 1 by word]
          word
        have hel' : elemOff (k + 1) + 16 ≤ pg.length := by unfold elemOff at hcnt ⊢; omega
        wp_apply hBE (pageLoc v pid.toNat) (W16 (sint.Z (j + W64 1))) Hlb.1
          (by rw [hk16']; unfold elemOff at hel'; push_cast; omega)
        have hloc' : pageLoc v pid.toNat +ₗ (16 + 16 * uint.Z (W16 (sint.Z (j + W64 1)))) =
            pageLoc v pid.toNat +ₗ ((elemOff (k + 1) : Nat) : Int) := by
          rw [hk16']; unfold elemOff; push_cast; rfl
        rw [hloc']
        try wp_auto
        obtain ⟨hke1', hke2', -⟩ := helems (k + 1) hlast
        have he1' : uint.Z (branchElem pg (k + 1)).pos' = (branchPos pg (k + 1) : Int) := rfl
        have he2' : uint.Z (branchElem pg (k + 1)).ksize' = (branchKsize pg (k + 1) : Int) := rfl
        have hsmk := inViewAt_branchKey v pid.toNat pg hpg (k + 1) hke1'
        have hb2 : (pageLoc v pid.toNat +ₗ ((elemOff (k + 1) : Nat) : Int)).addr +
            uint.Z (branchElem pg (k + 1)).pos' + uint.Z (branchElem pg (k + 1)).ksize' ≤ maxAddr := by
          rw [he1', he2']; have := Hlb.2; simp only [Loc.add]; omega
        obtain ⟨be1, hbe1⟩ : ∃ be, branchElem pg (k + 1) = be := ⟨_, rfl⟩
        rw [hbe1] at hsmk hb2
        icases rdTxK_elem_acc (V := branchPageElement) K tx src q T v pid.toNat pg hpg (k + 1) hel'
          $$ Hk with ⟨%dqe4, Hel, Helb⟩
        rw [show (decode (bytesAt pg (elemOff (k + 1)) 16) : branchPageElement) =
          branchElem pg (k + 1) from rfl, hbe1]
        wp_apply hBK (pageLoc v pid.toNat +ₗ ((elemOff (k + 1) : Nat) : Int)) be1
          dqe4 (by simp only [Loc.add]; omega) hb2 $$ [Hel] as Hel
        · iexact Hel
        ihave Hk := Helb $$ Hel
        try wp_auto
        rw [show inViewAt v _ (branchKey pg (k + 1)) = keyOpt v _
          (childHi hi (branchKey pg) (pageCount pg) k) by unfold childHi; rw [ite_eq_left hlast]; rfl]
          at hsmk
        rk_tail
      · rw [decide_eq_false (show ¬ sint.Z j < (pageCount pg : Int) - 1 by omega)]
        wp_auto
        have hsmk : keyOpt v smx (childHi hi (branchKey pg) (pageCount pg) k) := by
          unfold childHi; rw [ite_eq_right hlast]; exact hmx
        rk_tail
    · rw [decide_eq_false hjc]
      have hne : (#false : val) ≠ #true := fun h => absurd (GoGlobalContext.intoVal_inj_bool h) (by decide)
      simp only [hne, decide_false, _root_.decide_true, Bool.false_eq_true, ↓reduceIte]
      wp_auto
      have hjn : (sint.Z j).toNat = pageCount pg := by omega
      ihave Hb := Hundo $$ [Hs Hcap]
      · iframe
      icases Hb with ⟨Hs, Hcap⟩
      iapply HΦ
      iframe
      ipureintro
      intro hc
      obtain ⟨-, kp, hin, hlt⟩ := Hj.2.2.2 (by omega)
      refine ⟨kp, hin, ?_⟩
      rw [hjn] at hlt
      unfold childHi at hlt
      rw [ite_eq_right (by omega)] at hlt
      exact hlt

theorem Tx.recursivelyCheckPageKeyOrderInternal_ok.wp_proof
    (hpage : Tx.page_r.spec (GF := GF) (hG := hG))
    (hIB : internal.common.Page.IsBranchPage.spec (GF := GF) (hG := hG))
    (hIL : internal.common.Page.IsLeafPage.spec (GF := GF) (hG := hG))
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG))
    (hBEs : internal.common.Page.BranchPageElements.spec (GF := GF) (hG := hG))
    (hBE : internal.common.Page.BranchPageElement.spec (GF := GF) (hG := hG))
    (hLEs : internal.common.Page.LeafPageElements.spec (GF := GF) (hG := hG))
    (hLE : internal.common.Page.LeafPageElement.spec (GF := GF) (hG := hG))
    (hBP : internal.common.branchPageElement.Pgid.spec (GF := GF) (hG := hG))
    (hBK : internal.common.branchPageElement.Key.spec (GF := GF) (hG := hG))
    (hLK : internal.common.leafPageElement.Key.spec (GF := GF) (hG := hG))
    (wp_vko : verifyKeyOrder_ok.spec (GF := GF) (hG := hG)) :
    Tx.recursivelyCheckPageKeyOrderInternal_ok.spec (GF := GF) (hG := hG) := by
  intro K tx src q T v pid pg hwm lo hi mn smn smx stk ids f ch hpg hwf hkeys hmn hmn' hmx
  iintro %Φ ⟨Hk, Hs, Hcap⟩ HΦ
  icases (persistent_entails_left (rdTxK_view K tx src q T v)) $$ Hk with ⟨Hk, %Hvw⟩
  obtain ⟨-, C, hok, hvC⟩ := Hvw
  have hpv : v.pages = C.pages := by rw [← hvC]; rfl
  obtain ⟨-, -, -, pht, hpht⟩ := hok.1
  rw [← hpv] at hpht
  iapply (rcpkoInternal_rec hpage hIB hIL hCnt hBEs hBE hLEs hLE hBP hBK hLK wp_vko pht
    (v.pages.size + 1) K tx src q T v pid pg hwm lo hi mn smn smx stk ids f ch hpht
    (pht_lt_size v.pages hwm pht hpht _ hwf) hpg hwf hkeys hmn hmn' hmx) $$ [Hk Hs Hcap] HΦ
  iframe

end spec

end bbolt
end EtcdGrove
end Perennial
