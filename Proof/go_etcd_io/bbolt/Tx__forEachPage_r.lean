/-
The proof of `Spec/go_etcd_io/bbolt/Tx__forEachPage_r.lean` (U6, `notes/bbolt-proof-plan.md`):
`forEachPageInternal` by induction on the fuel of the walk (above the page's height `pht`, from
`pageHts` of the view), over the segment `pageWalkF P n ids` of the whole walk that it visits;
the stack slice is owned with its capacity, which `append` extends and its undo gives back.
-/
module

public import Spec.go_etcd_io.bbolt.Tx__forEachPage_r
public import Spec.go_etcd_io.bbolt.Tx__page_r
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsBranchPage
public import Spec.go_etcd_io.bbolt.internal.common.Page__Count
public import Spec.go_etcd_io.bbolt.internal.common.Page__BranchPageElement
public import Spec.go_etcd_io.bbolt.internal.common.branchPageElement__Pgid
public import Proof.go_etcd_io.bbolt.Read.Walk
public import Proof.go_etcd_io.bbolt.Read.Open
public import Proof.go_etcd_io.bbolt.Read.BktOK

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

/-- `fn`'s triple of `Tx.forEachPage_r.spec`. -/
def fepFn (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) (root : w64)
    (fn : GoFunc) (I : Nat → IProp GF) : IProp GF :=
  iprop(∀ (i id : Nat) (ids : List Nat) (stk : GoSlice) (dq : DFrac),
    {{ rdTxK K tx src q T v ∗ I i ∗ stk ↦*{dq} (ids.map fun x : Nat => W64 (x : Int)) ∗
        ⌜(pageWalk v.pages root.toNat)[i]? = some (id, ids)⌝ }}
      (App (App (App (Val #fn) (Val #(pageLoc v id)))
        (Val #(W64 ((ids.length - 1 : Nat) : Int)))) (Val #stk))
    {{ RET #(); rdTxK K tx src q T v ∗ I (i + 1) ∗
        stk ↦*{dq} (ids.map fun x : Nat => W64 (x : Int)) }})

/-- `forEachPageInternal` over the segment `pageWalkF P n ids` of the walk, at offset
`pre.length`. -/
theorem fepInternal_rec
    (hpage : Tx.page_r.spec (GF := GF) (hG := hG))
    (hIB : internal.common.Page.IsBranchPage.spec (GF := GF) (hG := hG))
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG))
    (hBPE : internal.common.Page.BranchPageElement.spec (GF := GF) (hG := hG))
    (hBP : internal.common.branchPageElement.Pgid.spec (GF := GF) (hG := hG))
    (pht : Nat → Nat) :
    ∀ (n : Nat) (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) (root : w64)
      (fn : GoFunc) (I : Nat → IProp GF) (hwm : Nat) (pre post : List (Nat × List Nat))
      (ids : List Nat) (id : Nat) (sl : GoSlice),
    pageHts v.pages pht → treeWF v.pages hwm id → pht id < n →
    ids.getLast? = some id → id < 2 ^ 64 →
    pageWalk v.pages root.toNat = pre ++ pageWalkF v.pages n ids ++ post →
    {{ rdTxK (GF := GF) K tx src q T v ∗ I pre.length ∗
        sl ↦* (ids.map fun x : Nat => W64 (x : Int)) ∗ ownSliceCap w64 sl (DFrac.own 1) ∗
        □ fepFn K tx src q T v root fn I }}
      (App (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"forEachPageInternal"))
        (Val #sl)) (Val #fn))
    {{ RET #(); rdTxK K tx src q T v ∗ I (pre.length + (pageWalkF v.pages n ids).length) ∗
        sl ↦* (ids.map fun x : Nat => W64 (x : Int)) ∗ ownSliceCap w64 sl (DFrac.own 1) }} := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro K tx src q T v root fn I hwm pre post ids id sl hpht hwf hn hlast hid hW
  simp only [fepFn]
  wp_start as ⟨Hk, HI, Hs, Hcap, #Hfn⟩
  ihave #Hpkg := rdTxK_pkgInit K tx src q T v $$ Hk
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  simp only [List.length_map] at Hsl
  have hne : ids ≠ [] := by intro e; subst e; simp at hlast
  have hl1 : 1 ≤ ids.length := List.length_pos_iff.mpr hne
  have hslz : sint.Z sl.len = (ids.length : Int) := by
    have h1 := Hsl.1; have h2 := Hsl.2
    rw [show sint.nat sl.len = (sint.Z sl.len).toNat from rfl] at h1; omega
  have hidx : sint.Z (sl.len - W64 1) = ((ids.length - 1 : Nat) : Int) := by word
  have hlk : (ids.map fun x : Nat => W64 (x : Int))[(sint.Z (sl.len - W64 1)).toNat]? =
      some (W64 (id : Int)) := by
    rw [hidx, Int.toNat_natCast, List.getElem?_map, ← List.getLast?_eq_getElem?, hlast]; rfl
  rcases hwf with ⟨_, pg, h2, hlt, hpg, hpid, hplen, hpt⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  wp_auto
  rw [ite_eq_left ⟨by rw [hidx]; omega, by rw [hidx]; omega⟩]
  icases ownSlice_elem_acc (sint.Z (sl.len - W64 1)) _ _ _ _ (by rw [hidx]; omega) hlk $$ Hs
    with ⟨He, Hsback⟩
  wp_auto
  ihave Hs := Hsback $$ He
  rw [list_set_lookup_self _ _ _ hlk]
  have hidn : (W64 (id : Int)).toNat = id := toNat_W64_of_lt id hid
  wp_apply hpage K tx src q T v (W64 (id : Int)) pg (by rw [hidn]; exact hpg) $$ [Hk] as Hk
  · iexact Hk
  rw [hidn]
  try wp_auto
  have hlw : sl.len - W64 1 = W64 (((ids.length - 1 : Nat)) : Int) := by
    apply BitVec.eq_of_toInt_eq; rw [show BitVec.toInt (sl.len - W64 1) = sint.Z (sl.len - W64 1)
      from rfl, hidx]; word
  rw [hlw]
  have hW0 : (pageWalk v.pages root.toNat)[pre.length]? = some (id, ids) := by
    rw [hW, pageWalkF_succ v.pages m ids id pg hlast hpg]; simp
  ihave #Hf := Hfn $$ %pre.length %id %ids %sl %(DFrac.own 1)
  wp_apply Hf $$ [Hk HI Hs] as ⟨Hk, HI, Hs⟩
  · iframe; ipureintro; exact hW0
  try wp_auto
  have h16 : 16 ≤ pg.length := by
    have := Nat.le_mul_of_pos_left 4096 (show 0 < 1 + pageOverflow pg by omega)
    omega
  icases rdTxK_hdr_acc K tx src q T v id pg hpg h16 $$ Hk with ⟨%dqh, Hh, Hhb⟩
  obtain ⟨hd, hH⟩ : ∃ hd, pageHdr pg = hd := ⟨_, rfl⟩
  have hfz : pageFlags pg = hd.flags'.toNat := by unfold pageFlags; rw [hH]
  have hcz : pageCount pg = hd.count'.toNat := by unfold pageCount; rw [hH]
  rw [hH]
  wp_apply hIB (pageLoc v id) hd dqh $$ [Hh] as Hh
  · iexact Hh
  rcases hpt with ⟨_, _, hlf, hlwf, hbk⟩ | ⟨_, _, hbr, hbwf, hch⟩
  · -- a leaf
    have hf2 : hd.flags' = W16 2 := by
      apply BitVec.eq_of_toNat_eq; rw [← hfz, hlf]; rfl
    rw [hf2]
    wp_auto
    ihave Hk := Hhb $$ Hh
    iapply HΦ
    rw [pageWalkF_succ v.pages m ids id pg hlast hpg, ite_eq_right (by rw [hlf]; decide)]
    iframe
  · -- a branch
    have hf1 : hd.flags' = W16 1 := by
      apply BitVec.eq_of_toNat_eq; rw [← hfz, hbr]; rfl
    rw [hf1]
    wp_auto
    ihave Hk := Hhb $$ Hh
    obtain ⟨hc0, -, hcnt, helems, -⟩ := hbwf
    have hcnt16 : pageCount pg < 2 ^ 16 := by rw [hcz]; exact BitVec.isLt _
    obtain ⟨f, hf⟩ : ∃ f : Nat → List (Nat × List Nat),
        f = fun j => pageWalkF v.pages m (ids ++ [branchPgid pg j]) := ⟨_, rfl⟩
    have hfk : ∀ j, f j = pageWalkF v.pages m (ids ++ [branchPgid pg j]) := by intro j; rw [hf]
    ihave IH : (∃ (j : w64),
        "i" ∷ i_ptr ↦ j ∗ "Hk" ∷ rdTxK K tx src q T v ∗
        "HI" ∷ I (pre.length + 1 + ((List.range (sint.nat j)).flatMap f).length) ∗
        "Hs" ∷ sl ↦* (ids.map fun x : Nat => W64 (x : Int)) ∗
        "Hcap" ∷ ownSliceCap w64 sl (DFrac.own 1) ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ (pageCount pg : Int)⌝ : IProp GF) $$ [i Hk HI Hs Hcap]
    · iexists W64 0
      simp only [named]
      rw [show sint.nat (W64 0) = 0 from rfl]
      simp only [List.range_zero, List.flatMap_nil, List.length_nil, Nat.add_zero]
      iframe
      ipureintro; constructor <;> word
    wp_for IH
    icases rdTxK_hdr_acc K tx src q T v id pg hpg h16 $$ Hk with ⟨%dqh2, Hh, Hhb⟩
    rw [hH]
    wp_apply hCnt (pageLoc v id) hd dqh2 $$ [Hh] as Hh
    · iexact Hh
    ihave Hk := Hhb $$ Hh
    have hcw : sint.Z (W64 (uint.Z hd.count')) = (pageCount pg : Int) := by
      rw [hcz]; have := hd.count'.isLt; word
    rw [hcw]
    by_cases hjc : sint.Z j < (pageCount pg : Int)
    · rw [decide_eq_true hjc]
      simp only [_root_.decide_true, ↓reduceIte]
      wp_auto
      obtain ⟨k, hk⟩ : ∃ k : Nat, sint.Z j = (k : Int) := ⟨(sint.Z j).toNat, by omega⟩
      have hkc : k < pageCount pg := by omega
      have hjk : sint.nat j = k := by
        rw [show sint.nat j = (sint.Z j).toNat from rfl, hk]; simp
      have hk16 : uint.Z (W16 (sint.Z j)) = (k : Int) := by rw [hk]; word
      icases rdTxK_page_bounds K tx src q T v id pg hpg (by intro e; simp [e] at h16) $$ Hk
        with ⟨Hk, %Hlb⟩
      have hel : elemOff k + 16 ≤ pg.length := by unfold elemOff at hcnt ⊢; omega
      wp_apply hBPE (pageLoc v id) (W16 (sint.Z j)) Hlb.1
        (by rw [hk16]; unfold elemOff at hel; omega)
      have hloc : pageLoc v id +ₗ (16 + 16 * uint.Z (W16 (sint.Z j))) =
          pageLoc v id +ₗ ((elemOff k : Nat) : Int) := by
        rw [hk16]; unfold elemOff; push_cast; rfl
      rw [hloc]
      try wp_auto
      icases rdTxK_elem_acc (V := branchPageElement) K tx src q T v id pg hpg k hel $$ Hk
        with ⟨%dqe, Hel, Helb⟩
      rw [show (decode (bytesAt pg (elemOff k) 16) : branchPageElement) = branchElem pg k from rfl]
      obtain ⟨be, hbe⟩ : ∃ be, branchElem pg k = be := ⟨_, rfl⟩
      rw [hbe]
      wp_apply hBP (pageLoc v id +ₗ ((elemOff k : Nat) : Int)) be dqe $$ [Hel] as Hel
      · iexact Hel
      ihave Hk := Helb $$ Hel
      have hchild : be.pgid'.toNat = branchPgid pg k := by unfold branchPgid; rw [hbe]
      try wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Hsl1, -⟩
      wp_apply wp_slice_append_undo $$ [$Hs $Hcap $Hsl1] as %s1 ⟨Hs, Hcap, -, Hundo⟩
      try wp_auto
      have hcl : branchPgid pg k < 2 ^ 64 := by rw [← hchild]; exact BitVec.isLt _
      have hmap : (ids.map fun x : Nat => W64 (x : Int)) ++ [be.pgid'] =
          ((ids ++ [branchPgid pg k]).map fun x : Nat => W64 (x : Int)) := by
        rw [List.map_append]; simp only [List.map_cons, List.map_nil]
        congr 2
        apply BitVec.eq_of_toNat_eq; rw [toNat_W64_of_lt _ hcl, hchild]
      rw [hmap]
      have hht := (hpht id pg hpg).2 hbr k hkc
      have hW' : pageWalk v.pages root.toNat =
          (pre ++ (id, ids) :: (List.range k).flatMap f) ++
            pageWalkF v.pages m (ids ++ [branchPgid pg k]) ++
            (((List.range (pageCount pg)).drop (k + 1)).flatMap f ++ post) := by
        rw [hW, pageWalkF_succ v.pages m ids id pg hlast hpg, ite_eq_left hbr, ← hf,
          flatMap_range_split f _ k hkc, hfk k]
        simp only [List.append_assoc, List.cons_append]
      wp_apply (ih m (by omega) K tx src q T v root fn I hwm _ _ (ids ++ [branchPgid pg k])
        (branchPgid pg k) s1 hpht (hch k hkc) (by omega) (by simp) hcl hW')
        $$ [Hk HI Hs Hcap] as ⟨Hk, HI, Hs, Hcap⟩
      · rw [show (pre ++ (id, ids) :: List.flatMap f (List.range k)).length =
            pre.length + 1 + (List.flatMap f (List.range (sint.nat j))).length by
          rw [hjk]; simp only [List.length_append, List.length_cons]; omega]
        iframe
        simp only [fepFn]
        imodintro
        iexact Hfn
      ihave Hb := Hundo $$ [Hs Hcap]
      · rw [← hmap]; iframe
      icases Hb with ⟨Hs, Hcap⟩
      wp_for_post
      iframe
      iexists j + W64 1
      iframe
      have hj1 : sint.nat (j + W64 1) = k + 1 := by
        rw [show sint.nat (j + W64 1) = (sint.Z (j + W64 1)).toNat from rfl]; word
      rw [hj1]
      isplitl
      · iExactEq HI
        congr 1
        simp only [List.length_append, List.length_cons, List.range_succ, List.flatMap_append,
          List.flatMap_singleton, hfk]
        omega
      · ipureintro; constructor <;> word
    · rw [decide_eq_false hjc]
      have hne : (#false : val) ≠ #true := fun h => absurd (GoGlobalContext.intoVal_inj_bool h) (by decide)
      simp only [hne, decide_false, _root_.decide_true, Bool.false_eq_true, ↓reduceIte]
      wp_auto
      have hjn : sint.nat j = pageCount pg := by
        rw [show sint.nat j = (sint.Z j).toNat from rfl]; omega
      iapply HΦ
      rw [pageWalkF_succ v.pages m ids id pg hlast hpg, ite_eq_left hbr, ← hf]
      rw [hjn] at *
      iframe
      iExactEq HI
      congr 1
      simp only [List.length_cons]
      omega

theorem Tx.forEachPage_r.wp_proof
    (hpage : Tx.page_r.spec (GF := GF) (hG := hG))
    (hIB : internal.common.Page.IsBranchPage.spec (GF := GF) (hG := hG))
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG))
    (hBPE : internal.common.Page.BranchPageElement.spec (GF := GF) (hG := hG))
    (hBP : internal.common.branchPageElement.Pgid.spec (GF := GF) (hG := hG)) :
    Tx.forEachPage_r.spec (GF := GF) (hG := hG) := by
  intro K tx src q T v root fn I hwf
  obtain ⟨hwm, hwf⟩ := hwf
  wp_start as ⟨Hk, HI, #Hfn⟩
  ihave #Hpkg := rdTxK_pkgInit K tx src q T v $$ Hk
  icases (persistent_entails_left (rdTxK_view K tx src q T v)) $$ Hk with ⟨Hk, %Hvw⟩
  obtain ⟨-, C, hok, hvC⟩ := Hvw
  have hpv : v.pages = C.pages := by rw [← hvC]; rfl
  obtain ⟨-, -, -, pht, hpht⟩ := hok.1
  rw [← hpv] at hpht
  wp_auto
  wp_apply wp_slice_make2 (V := w64) (W64 10) as %stk ⟨Hs, Hcap⟩
  · ipureintro; decide
  try wp_auto
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  ihave %Hcw := ownSliceCap_wf _ _ $$ Hcap
  simp only [List.length_replicate] at Hsl
  have hl10 : sint.Z stk.len = 10 := by
    have h1 := Hsl.1; have h2 := Hsl.2
    rw [show sint.nat stk.len = (sint.Z stk.len).toNat from rfl] at h1
    omega
  rw [ite_eq_left ⟨by decide, by rw [hl10]; decide⟩]
  icases ownSlice_elem_acc (sint.Z (W64 0)) (zero_val w64) _ _ _ (by decide) (by simp) $$ Hs
    with ⟨He, Hsback⟩
  wp_auto
  ihave Hs := Hsback $$ He
  try wp_auto
  rw [ite_eq_left ⟨by decide, by decide, by have := Hcw; word⟩]
  icases ownSlice_slice_with_cap (W64 0) (W64 1) stk _ ⟨by decide, by decide, by rw [hl10]; decide⟩
    $$ [Hs Hcap] with ⟨-, Hs, Hcap⟩
  · iframe
  have hsub : subslice (sint.nat (W64 0)) (sint.nat (W64 1))
      ((List.replicate 10 (zero_val w64)).set (sint.Z (W64 0)).toNat root) =
      ([root.toNat].map fun x : Nat => W64 (x : Int)) := by
    simp only [List.map_cons, List.map_nil, show W64 (root.toNat : Int) = root by simp]
    rfl
  rw [hsub]
  try wp_auto
  wp_apply (fepInternal_rec hpage hIB hCnt hBPE hBP pht (v.pages.size + 1) K tx src q T v root fn I
    hwm [] [] [root.toNat] root.toNat _ hpht hwf (pht_lt_size v.pages hwm pht hpht _ hwf) rfl
    root.isLt (by simp [pageWalk])) $$ [Hk HI Hs Hcap] as ⟨Hk, HI, -, -⟩
  · iframe
    simp only [fepFn]
    imodintro
    iexact Hfn
  try wp_auto
  iapply HΦ
  iframe
  iExactEq HI
  simp [pageWalk]

end proof

end bbolt
end EtcdGrove
end Perennial
