module
public import Spec.go_etcd_io.bbolt.internal.common.Page__BranchPageElements
public import Spec.go_etcd_io.bbolt.internal.common.Page__Count
public import Spec.go_etcd_io.bbolt.internal.common.branchPageElement__Key
public import Spec.go_etcd_io.bbolt.internal.common.branchPageElement__Pgid
public import Proof.go_etcd_io.bbolt.internal.common.Bytes
public import Batteries.Tactic.PermuteGoals
public import Proof.go_etcd_io.bbolt.CursorModel
public import Proof.go_etcd_io.bbolt.PageView
public import Spec.go_etcd_io.bbolt.Cursor__search
public import Spec.go_etcd_io.bbolt.Cursor__searchPage
public import Spec.go_etcd_io.bbolt.Bucket__pageNode
public import Spec.go_etcd_io.bbolt.Cursor__nsearch
public import Spec.go_etcd_io.bbolt.elemRef__isLeaf
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsBranchPage
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsLeafPage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `bytes.Compare` returns 0 only for equal keys. -/
theorem compareResult_eq_zero (a b : List w8) (h : bytes.compareResult a b = W64 0) : a = b := by
  unfold bytes.compareResult at h
  split at h
  · exact absurd h (by decide)
  · split at h
    · assumption
    · exact absurd h (by decide)

theorem goStringLt_irrefl (a : List w8) : ¬ go.GoStringLt a a := by
  unfold go.GoStringLt
  induction a with
  | nil => intro h; cases h
  | cons x xs ih =>
    intro h
    cases h with
    | rel h => exact Int.lt_irrefl _ h
    | cons h => exact ih h

theorem branchGE_of_eq (pg kb : List w8) (h : Nat) (he : branchKey pg h = kb) :
    branchGE pg kb (h : Int) = true := by
  simp only [branchGE, Int.toNat_natCast, he, decide_eq_true_eq, ne_eq, compareResult_eq_neg1]
  exact goStringLt_irrefl kb

theorem set_last_append {α : Type} (es : List α) (e x : α) :
    (es ++ [e]).set ((es ++ [e]).length - 1) x = es ++ [x] := by
  simp [List.set_append_right]

/-- `Cursor.search.spec`, as an Iris proposition (for the Löb induction tying `search` and
`searchPage`, which call each other). -/
def searchI : IProp GF :=
  iprop(∀ (cl : Loc) (cv : Cursor) (es : List elemRef) (V : BktView) (q : Qp) (pid : w64)
    (key : GoSlice) (kb : List w8) (dk : DFrac),
  ⌜V.ok ∧ V.wfAt pid⌝ →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ cl ↦ cv ∗ cv.stack' ↦* es ∗
      ownSliceCap elemRef cv.stack' (DFrac.own 1) ∗ bktCtx cv.bucket' V ∗ bktPages V q ∗
      key ↦*{dk} kb }}
    (App (App (Val (cl @!! go.GoType.PointerType Cursor.ty @!! go!"search")) (Val #key)) (Val #pid))
  {{ (cv' : Cursor) (path : List elemRef) (pg : List w8) (idx : w64), RET #();
      ⌜cv'.bucket' = cv.bucket' ∧ stackOK V pid path ∧ stackLeaf V pid path pg idx ∧ leafOK pg ∧
        leafSeekAt pg kb idx⌝ ∗
      cl ↦ cv' ∗ cv'.stack' ↦* (es ++ path) ∗ ownSliceCap elemRef cv'.stack' (DFrac.own 1) ∗
      bktCtx cv.bucket' V ∗ bktPages V q ∗ key ↦*{dk} kb }})

/-- `Cursor.searchPage.spec`, as an Iris proposition. -/
def searchPageI : IProp GF :=
  iprop(∀ (cl : Loc) (cv : Cursor) (es : List elemRef) (rv : elemRef) (V : BktView) (q : Qp)
    (pid : w64) (pg : List w8) (key : GoSlice) (kb : List w8) (dk : DFrac),
  ⌜V.ok ∧ es.getLast? = some rv ∧ rv.node' = null ∧ V.pageAt pid = some (rv.page', pg) ∧
    pageFlags pg = branchPageFlag ∧ branchWF pg pg.length V.hwm ∧ 16 ≤ pg.length ∧
    (∀ i < pageCount pg, V.wfAt (W64 (branchPgid pg i)))⌝ →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ cl ↦ cv ∗ cv.stack' ↦* es ∗
      ownSliceCap elemRef cv.stack' (DFrac.own 1) ∗ bktCtx cv.bucket' V ∗ bktPages V q ∗
      key ↦*{dk} kb }}
    (App (App (Val (cl @!! go.GoType.PointerType Cursor.ty @!! go!"searchPage")) (Val #key))
      (Val #rv.page'))
  {{ (cv' : Cursor) (i : w64) (path : List elemRef) (lpg : List w8) (idx : w64), RET #();
      ⌜cv'.bucket' = cv.bucket' ∧ 0 ≤ sint.Z i ∧ sint.Z i < pageCount pg ∧
        stackOK V (W64 (branchPgid pg (sint.Z i).toNat)) path ∧
        stackLeaf V (W64 (branchPgid pg (sint.Z i).toNat)) path lpg idx ∧ leafOK lpg ∧
        leafSeekAt lpg kb idx⌝ ∗
      cl ↦ cv' ∗ cv'.stack' ↦* (es.set (es.length - 1) { rv with index' := i } ++ path) ∗
      ownSliceCap elemRef cv'.stack' (DFrac.own 1) ∗
      bktCtx cv.bucket' V ∗ bktPages V q ∗ key ↦*{dk} kb }})

set_option maxHeartbeats 400000 in
/-- `searchPage`, given `search` for the children. -/
theorem searchPage_of_search
    (hBPEs : Page.BranchPageElements.spec (GF := GF) (hG := hG))
    (hCount : Page.Count.spec (GF := GF) (hG := hG))
    (hKey : branchPageElement.Key.spec (GF := GF) (hG := hG))
    (hPgid : branchPageElement.Pgid.spec (GF := GF) (hG := hG)) :
    □ searchI (GF := GF) ⊢ searchPageI := by
  unfold searchI searchPageI
  iintro #IH %cl %cv %es %rv %V %q %pid %pg %key %kb %dk %Hpre
  obtain ⟨Hok, Hlast, Hnode, Hpa, Hbr, Hwf, Hlen, Hkids⟩ := Hpre
  wp_start as ⟨Hcl, Hs, Hcap, Hctx, Hpgs, Hk⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  have Hne : es ≠ [] := by intro h; subst h; simp at Hlast
  have Hpos : 0 < es.length := List.length_pos_iff.2 Hne
  have Hli : es[es.length - 1]? = some rv := by
    rw [List.getLast?_eq_getElem?] at Hlast; exact Hlast
  have Hix : (sint.Z (cv.stack'.len - W64 1)).toNat = es.length - 1 := by word
  have Hc := pageAt_car V pid rv.page' pg Hok Hpa
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  ihave #Hsort : isPkgInit (PROP := IProp GF) pkg_id.sort $$ []
  · iPkgInit
  ihave #Hbytes : isPkgInit (PROP := IProp GF) pkg_id.bytes $$ []
  · iPkgInit
  icases bktPages_acc V q pid rv.page' pg Hok Hpa $$ Hpgs with ⟨Hpg, Hpgsback⟩
  wp_auto
  icases (page_header_bytes (hG := hG) _ _ pg Hlen Hc).1 $$ Hpg with ⟨Hhd, Hrest⟩
  wp_apply hBPEs _ (pageOf pg) _ Hc $$ [Hhd] as Hhd
  · iframe
  try wp_auto
  wp_apply hCount _ (pageOf pg) _ $$ [Hhd] as Hhd
  · iframe
  try wp_auto
  obtain ⟨Hcnt0, Hle, Helems, Hkvs, Hsorted⟩ := Hwf
  have Hcnt : pageCount pg < 65536 := by have := leAt_lt pg 10 2; unfold pageCount; omega
  have Hu16 : uint.Z (W16 ((pageCount pg : Nat) : Int)) = ((pageCount pg : Nat) : Int) := by word
  have Hs64 : sint.Z (W64 ((pageCount pg : Nat) : Int)) = ((pageCount pg : Nat) : Int) := by word
  have Hcne : W16 ((pageCount pg : Nat) : Int) ≠ W16 0 := by
    intro h; have := congrArg BitVec.toNat h; simp at this; omega
  rw [Hu16]
  simp only [pageOf]
  rw [ite_eq_right_of_eq_false _ _ (eq_false Hcne)]
  ihave Hpg := (page_header_bytes (hG := hG) _ _ pg Hlen Hc).2 $$ [Hhd Hrest]
  · simp only [pageOf]; iframe
  wp_apply sort.wp_Search (W64 ((pageCount pg : Nat) : Int)) _ (branchGE pg kb)
    iprop(inodes_ptr ↦ slice.mk (rv.page' +ₗ 16) (W64 (uint.Z (W16 ((pageCount pg : Nat) : Int))))
        (W64 (uint.Z (W16 ((pageCount pg : Nat) : Int)))) ∗
      key_ptr ↦ key ∗ key ↦*{dk} kb ∗ bytesPointsto rv.page' (DFrac.own q) pg ∗
      ∃ (e : Bool), exact_ptr ↦ e ∗ ⌜e = true → ∃ h, h < pageCount pg ∧ branchKey pg h = kb⌝)
    $$ [inodes key Hk Hpg exact]
  · rw [Hu16] at *
    iframe
    isplitl []
    · ipureintro; word
    isplitl []
    · unfold sort.predImplements
      iintro %i
      wp_start as ⟨⟨Hin, Hkp, Hk, Hpg, %e, Hex, %He⟩, %Hb⟩
      rw [Hs64] at Hb
      wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hb.1, by word⟩)]
      have Hit : (sint.Z i).toNat < pageCount pg := by omega
      have Hidx : sliceIndexRef internal.common.branchPageElement (sint.Z i)
          (slice.mk (rv.page' +ₗ 16) (W64 ((pageCount pg : Nat) : Int)) (W64 ((pageCount pg : Nat) : Int))) =
          rv.page' +ₗ ((elemOff (sint.Z i).toNat : Nat) : Int) := by
        unfold sliceIndexRef arrayIndexRef
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by simpa [Loc.add] using Hc)),
          typeSize_branchPageElement (hG := hG), loc_add_assoc]
        unfold elemOff; congr 1; omega
      rw [Hidx]
      try wp_auto
      have Hin' : elemOff (sint.Z i).toNat + 16 ≤ pg.length := by
        have := Helems; unfold elemOff at *; omega
      icases (branchElem_in_page (hG := hG) rv.page' _ pg _ Hin' Hc).1 $$ Hpg with ⟨Hpre, He, Hpost⟩
      obtain ⟨Hk1, Hk2, Hk3⟩ := Hkvs _ Hit
      have Hec : (rv.page' +ₗ ((elemOff (sint.Z i).toNat : Nat) : Int)).locCar ≠ 0 := by
        simpa [Loc.add] using Hc
      have HpL : branchPos pg (sint.Z i).toNat < 2 ^ 32 := leAt_lt _ _ 4
      have HkL : branchKsize pg (sint.Z i).toNat < 2 ^ 32 := leAt_lt _ _ 4
      have Hpu : uint.Z (W32 ((branchPos pg (sint.Z i).toNat : Nat) : Int)) =
          (branchPos pg (sint.Z i).toNat : Int) := by word
      have Hku : uint.Z (W32 ((branchKsize pg (sint.Z i).toNat : Nat) : Int)) =
          (branchKsize pg (sint.Z i).toNat : Int) := by word
      have HkOk : uint.Z (branchElemOf pg (sint.Z i).toNat).pos' +
          uint.Z (branchElemOf pg (sint.Z i).toNat).ksize' ≤ 2147483647 := by
        simp only [branchElemOf]; rw [Hpu, Hku]; omega
      wp_apply hKey _ (branchElemOf pg _) _ Hec HkOk $$ [He] as He
      · iframe
      ihave Hpg := (branchElem_in_page (hG := hG) rv.page' _ pg _ Hin' Hc).2 $$ [$Hpre $He $Hpost]
      simp only [Hpu, Hku, loc_add_assoc]
      have Hks : elemOff (sint.Z i).toNat + branchPos pg (sint.Z i).toNat +
          branchKsize pg (sint.Z i).toNat ≤ pg.length := by omega
      icases bytes_slice_acc (hG := hG) rv.page' _ pg _ _ Hks HkL Hc $$ Hpg with ⟨Hks, Hpgback⟩
      unfold sliceAt
      rw [show (((elemOff (sint.Z i).toNat + branchPos pg (sint.Z i).toNat : Nat) : Int)) =
        ((elemOff (sint.Z i).toNat : Nat) : Int) + (branchPos pg (sint.Z i).toNat : Int) by omega]
      try wp_auto
      wp_apply bytes.wp_Compare _ key _ dk _ kb $$ [Hks Hk] as ⟨Hks, Hk⟩
      · iframe
      try wp_auto
      ispecialize Hpgback $$ Hks
      wp_if_destruct
      · try wp_auto
        iapply HΦ
        iframe
        ipureintro
        refine ⟨fun _ => ⟨_, Hit, (compareResult_eq_zero _ _ Hif).symm ▸ ?_⟩, ?_⟩
        · simp only [branchKey]
        · simp only [branchGE, branchKey, ne_eq, ← decide_not]
          exact decide_eq_decide.mpr Iff.rfl
      · try wp_auto
        iapply HΦ
        iframe
        ipureintro
        refine ⟨He, ?_⟩
        simp only [branchGE, branchKey, ne_eq, ← decide_not]
        exact decide_eq_decide.mpr Iff.rfl
    ipureintro; rw [Hs64]; exact ⟨fun h => absurd h (by decide), branchGE_mono pg kb Hsorted⟩
  iintro %idx ⟨⟨Hin, Hkp, Hk, Hpg, %e, Hex, %He⟩, %H0, %Hfound, %Hoob, %Hgt⟩
  rw [Hs64] at Hfound Hoob
  have Hle' : sint.Z idx ≤ (pageCount pg : Int) := by
    refine Classical.byContradiction fun hcn => ?_
    have := Hoob (fun j hj => Hgt j ⟨hj.1, by omega⟩)
    omega
  rw [Hu16]
  try wp_auto
  have Hlt : ∀ k, k < pageCount pg → branchGE pg kb (k : Int) = true → sint.Z idx ≤ k := by
    intro k hk hg
    refine Classical.byContradiction fun hcn => ?_
    rw [Hgt k ⟨by omega, by omega⟩] at hg; cases hg
  cases e
  on_goal 1 =>
    try wp_auto
    wp_if_destruct
    on_goal 1 =>
      try wp_auto
      have Hi : 0 ≤ sint.Z (idx - W64 1) ∧ sint.Z (idx - W64 1) < (pageCount pg : Int) := by word
      generalize idx - W64 1 = i at Hi ⊢
    on_goal 2 =>
      try wp_auto
      have Hi : 0 ≤ sint.Z idx ∧ sint.Z idx < (pageCount pg : Int) := by word
      generalize idx = i at Hi ⊢
  on_goal 3 =>
    try wp_auto
    obtain ⟨h, hh, hk⟩ := He rfl
    have := Hlt h hh (branchGE_of_eq pg kb h hk)
    have Hi : 0 ≤ sint.Z idx ∧ sint.Z idx < (pageCount pg : Int) := by omega
    generalize idx = i at Hi ⊢
  all_goals
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
    icases ownSlice_elem_acc (sint.Z (cv.stack'.len - W64 1)) rv _ _ es (by word)
      (by rw [Hix]; exact Hli) $$ Hs with ⟨Hr, Hsback⟩
    try wp_auto
    ispecialize Hsback $$ %({ rv with index' := i } : elemRef) Hr
    rw [Hix]
    have Hit : (sint.Z i).toNat < pageCount pg := by omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi.1, by word⟩)]
    have Hidx : sliceIndexRef internal.common.branchPageElement (sint.Z i)
        (slice.mk (rv.page' +ₗ 16) (W64 ((pageCount pg : Nat) : Int)) (W64 ((pageCount pg : Nat) : Int))) =
        rv.page' +ₗ ((elemOff (sint.Z i).toNat : Nat) : Int) := by
      unfold sliceIndexRef arrayIndexRef
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by simpa [Loc.add] using Hc)),
        typeSize_branchPageElement (hG := hG), loc_add_assoc]
      unfold elemOff; congr 1; omega
    rw [Hidx]
    try wp_auto
    have Hin' : elemOff (sint.Z i).toNat + 16 ≤ pg.length := by
      have := Helems; unfold elemOff at *; omega
    icases (branchElem_in_page (hG := hG) rv.page' _ pg _ Hin' Hc).1 $$ Hpg with ⟨Hpre, He, Hpost⟩
    wp_apply hPgid _ (branchElemOf pg _) _ $$ [He] as He
    · iframe
    ihave Hpg := (branchElem_in_page (hG := hG) rv.page' _ pg _ Hin' Hc).2 $$ [$Hpre $He $Hpost]
    ispecialize Hpgsback $$ Hpg
    try simp only [branchElemOf]
    try wp_auto
    wp_apply IH $$ %cl %cv %(es.set (es.length - 1) { rv with index' := i }) %V %q
        %(W64 (branchPgid pg (sint.Z i).toNat)) %key %kb %dk [] [Hcl Hsback Hcap Hctx Hpgsback Hk]
      as %cv' %path %lpg %idx' ⟨%Hp, Hcl, Hs, Hcap, Hctx, Hpgs, Hk⟩
    · ipureintro; exact ⟨Hok, Hkids _ Hit⟩
    · iframe
    try wp_auto
    iapply HΦ
    rw [Hp.1]
    iframe
    ipureintro
    exact ⟨rfl, Hi.1, Hi.2, Hp.2⟩

set_option maxHeartbeats 400000 in
/-- `search`, by Löb induction: its recursive calls are through `searchPage`. -/
theorem search_loeb
    (hpageNode : Bucket.pageNode.spec (GF := GF) (hG := hG))
    (hIsBranch : Page.IsBranchPage.spec (GF := GF) (hG := hG))
    (hIsLeaf : Page.IsLeafPage.spec (GF := GF) (hG := hG))
    (hisLeaf : elemRef.isLeaf.spec (GF := GF) (hG := hG))
    (hnsearch : Cursor.nsearch.spec (GF := GF) (hG := hG))
    (hBPEs : Page.BranchPageElements.spec (GF := GF) (hG := hG))
    (hCount : Page.Count.spec (GF := GF) (hG := hG))
    (hKey : branchPageElement.Key.spec (GF := GF) (hG := hG))
    (hPgid : branchPageElement.Pgid.spec (GF := GF) (hG := hG)) :
    ⊢ searchI (GF := GF) := by
  iloeb as IH
  ihave #HSP := searchPage_of_search hBPEs hCount hKey hPgid
  unfold searchI
  iintro %cl %cv %es %V %q %pid %key %kb %dk %Hpre
  obtain ⟨Hok, Hwf⟩ := Hpre
  wp_start as ⟨Hcl, Hs, Hcap, Hctx, Hpgs, Hk⟩
  ihave #HSP' := HSP $$ [#]
  · iexact IH
  iclear HSP
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  obtain ⟨p, pg, Hpa, Hlen, Hinl, Hfile, Hkind⟩ := wfAt_page V pid Hok Hwf
  have Hc := pageAt_car V pid p pg Hok Hpa
  have Hpn : p ≠ null := fun h => Hc (by rw [h]; rfl)
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  unfold bktCtx
  icases Hctx with ⟨%bv, %ib, %t, %dbl, %d1, %d2, %d3, %d4, Hb, Hib, Ht, Hdata, Hps, %Hcx⟩
  obtain ⟨Hibr, Hnodes, Hrn, Htdb, Htp, Hbp, Hdn⟩ := Hcx
  icases bktPages_acc V q pid p pg Hok Hpa $$ Hpgs with ⟨Hpg, Hpgsback⟩
  -- what `pageNode` reads besides the bucket, and what it leaves out
  ihave ⟨Hin, Hout⟩ : (if ib.root' = W64 0 then True else
        bv.tx' ↦{d3} t ∗ structFieldRef DB go!"data" dbl ↦{d4} V.data ∗
        structFieldRef DB go!"pageSize" dbl ↦{d4} V.ps ∗
        bytesPointsto (V.data +ₗ uint.Z (pid * V.ps)) (DFrac.own q) pg) ∗
      (if ib.root' = W64 0 then bv.tx' ↦{d3} t ∗ structFieldRef DB go!"data" dbl ↦{d4} V.data ∗
        structFieldRef DB go!"pageSize" dbl ↦{d4} V.ps ∗ bytesPointsto p (DFrac.own q) pg
       else True) $$ [Ht Hdata Hps Hpg]
  · by_cases Hr : ib.root' = W64 0
    · rw [ite_eq_left_of_eq_true _ _ (eq_true Hr), ite_eq_left_of_eq_true _ _ (eq_true Hr)]
      iframe
    · rw [ite_eq_right_of_eq_false _ _ (eq_false Hr), ite_eq_right_of_eq_false _ _ (eq_false Hr)]
      rw [Hibr] at Hr
      rw [← (Hfile Hr).1]
      iframe
  have Hp : (if ib.root' = W64 0 then bv.page' else V.data +ₗ uint.Z (pid * V.ps)) = p := by
    by_cases Hr : ib.root' = W64 0
    · rw [ite_eq_left_of_eq_true _ _ (eq_true Hr)]
      rw [Hibr] at Hr; rw [Hbp Hr, (Hinl Hr).2]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false Hr)]
      rw [Hibr] at Hr; rw [(Hfile Hr).1]
  wp_auto
  wp_apply hpageNode cv.bucket' bv d1 ib d2 pid bv.tx' t d3 dbl V.data V.ps d4 (DFrac.own q) pg
      rfl Hnodes Hrn (fun h => (Hinl (Hibr ▸ h)).1)
      (fun h => ⟨Htdb, Htp, Hok.1, (Hfile (Hibr ▸ h)).2.2, Hlen, (Hfile (Hibr ▸ h)).2.1, by
        rcases Hkind with ⟨Hfl, _⟩ | ⟨Hfl, _⟩ <;> rw [Hfl] <;> unfold validPageFlags <;> decide⟩)
      $$ [Hb Hib Hin] as ⟨Hb, Hib, Hin⟩
  · iframe
  rw [Hp]
  ihave ⟨Ht, Hdata, Hps, Hpg⟩ : bv.tx' ↦{d3} t ∗ structFieldRef DB go!"data" dbl ↦{d4} V.data ∗
      structFieldRef DB go!"pageSize" dbl ↦{d4} V.ps ∗ bytesPointsto p (DFrac.own q) pg $$ [Hin Hout]
  · by_cases Hr : ib.root' = W64 0
    · rw [ite_eq_left_of_eq_true _ _ (eq_true Hr), ite_eq_left_of_eq_true _ _ (eq_true Hr)]
      icases Hout with ⟨Ht, Hdata, Hps, Hpg⟩
      iframe
    · rw [ite_eq_right_of_eq_false _ _ (eq_false Hr), ite_eq_right_of_eq_false _ _ (eq_false Hr)]
      rw [Hibr] at Hr
      rw [← (Hfile Hr).1]
      icases Hin with ⟨Ht, Hdata, Hps, Hpg⟩
      iframe
  ihave Hctx : bktCtx cv.bucket' V $$ [Hb Hib Ht Hdata Hps]
  · unfold bktCtx
    iexists bv, ib, t, dbl, d1, d2, d3, d4
    iframe
    ipureintro; exact ⟨Hibr, Hnodes, Hrn, Htdb, Htp, Hbp, Hdn⟩
  try wp_auto
  rw [decide_eq_false Hpn]
  icases (page_header_bytes (hG := hG) _ _ pg Hlen Hc).1 $$ Hpg with ⟨Hhd, Hrest⟩
  try wp_auto
  wp_apply hIsBranch _ (pageOf pg) _ $$ [Hhd] as Hhd
  · iframe
  have Hfl1 : (pageOf pg).flags' = W16 ((pageFlags pg : Nat) : Int) := rfl
  try rw [Hfl1]
  rcases Hkind with ⟨Hfl, Hlw⟩ | ⟨Hfl, Hbw, Hkids⟩
  · rw [Hfl, decide_eq_false (by unfold leafPageFlag; decide)]
    try wp_auto
    wp_apply hIsLeaf _ (pageOf pg) _ $$ [Hhd] as Hhd
    · iframe
    try rw [Hfl1]
    rw [Hfl, decide_eq_true (by unfold leafPageFlag; decide)]
    try wp_auto
    ihave Hpg := (page_header_bytes (hG := hG) _ _ pg Hlen Hc).2 $$ [$Hhd $Hrest]
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_slice_append $$ [$Hs $Hcap $Hsl] as %s' ⟨Hs, Hcap, -⟩
    try wp_auto
    wp_apply hisLeaf e_ptr { page' := p, node' := null, index' := 0 } (DFrac.own 1) (DFrac.own q) pg rfl Hc Hlen $$ [e Hpg] as ⟨e, Hpg⟩
    · iframe
    simp only [Hfl]
    rw [decide_eq_true (by unfold leafPageFlag; decide)]
    try wp_auto
    have Hns := hnsearch cl { cv with stack' := s' } (DFrac.own 1)
      (es ++ [{ page' := p, node' := null, index' := 0 }]) { page' := p, node' := null, index' := 0 }
      (DFrac.own q) pg key kb dk (by simp) rfl Hc Hlen Hfl Hlw
    wp_apply Hns $$ [Hcl Hs Hpg Hk] as %idx ⟨%Hseek, Hcl, Hs, Hpg, Hk⟩
    · iframe
    try wp_auto
    ispecialize Hpgsback $$ Hpg
    rw [set_last_append]
    unfold bktCtx
    iapply HΦ
    iframe
    ipureintro
    refine ⟨rfl, ?_, ⟨Hpa, rfl⟩, ⟨Hfl, Hlw, Hlen⟩, Hseek⟩
    exact ⟨rfl, pg, Hpa, Or.inr ⟨Hfl, rfl, by show -1 ≤ sint.Z idx; omega, Hseek.2.1⟩⟩
  · rw [Hfl, decide_eq_true (by unfold branchPageFlag; decide)]
    try wp_auto
    ihave Hpg := (page_header_bytes (hG := hG) _ _ pg Hlen Hc).2 $$ [$Hhd $Hrest]
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_slice_append $$ [$Hs $Hcap $Hsl] as %s' ⟨Hs, Hcap, -⟩
    try wp_auto
    wp_apply hisLeaf e_ptr { page' := p, node' := null, index' := 0 } (DFrac.own 1) (DFrac.own q) pg rfl Hc Hlen $$ [e Hpg] as ⟨e, Hpg⟩
    · iframe
    simp only [Hfl]
    rw [decide_eq_false (by unfold branchPageFlag; decide)]
    try wp_auto
    ispecialize Hpgsback $$ Hpg
    unfold searchPageI
    wp_apply HSP' $$ %cl %{ cv with stack' := s' } %(es ++ [{ page' := p, node' := null, index' := 0 }])
        %{ page' := p, node' := null, index' := 0 } %V %q %pid %pg %key %kb %dk []
        [Hcl Hs Hcap Hctx Hpgsback Hk]
      as %cv' %i %path %lpg %idx ⟨%Hsp, Hcl, Hs, Hcap, Hctx, Hpgs, Hk⟩
    · ipureintro; exact ⟨Hok, by simp, rfl, Hpa, Hfl, Hbw, Hlen, Hkids⟩
    · iframe
    try wp_auto
    rw [set_last_append, List.append_assoc, List.singleton_append]
    obtain ⟨Hb', Hi0, Hil, Hsok, Hslf, Hlok, Hseek⟩ := Hsp
    unfold bktCtx
    ispecialize HΦ $$ %cv' %({ page' := p, node' := null, index' := i } :: path) %lpg %idx
    iapply HΦ
    iframe
    ipureintro
    refine ⟨Hb', ⟨rfl, pg, Hpa, Or.inl ⟨Hfl, Hi0, Hil, Hsok⟩⟩, ?_, Hlok, Hseek⟩
    cases path with
    | nil => exact absurd Hsok (by simp [stackOK])
    | cons r rs => exact ⟨pg, Hpa, Hslf⟩

end proof

end bbolt
end EtcdGrove
end Perennial
