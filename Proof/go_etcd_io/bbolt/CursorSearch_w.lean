/-
A writer's cursor's search (`Cursor.search`, `searchPage`, `searchNode`, which call each
other), as Iris propositions for the Löb induction: from a position of a clean bucket down to a
leaf, through nodes and pages (`WriteCursor.lean`'s `wpath`).
-/
module
public import Spec.go_etcd_io.bbolt.internal.common.Page__BranchPageElements
public import Spec.go_etcd_io.bbolt.internal.common.Page__Count
public import Spec.go_etcd_io.bbolt.internal.common.Page__Id
public import Spec.go_etcd_io.bbolt.internal.common.branchPageElement__Key
public import Spec.go_etcd_io.bbolt.internal.common.branchPageElement__Pgid
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Key
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Pgid
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsBranchPage
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsLeafPage
public import Proof.go_etcd_io.bbolt.internal.common.Bytes
public import Proof.go_etcd_io.bbolt.CursorSearch
public import Proof.go_etcd_io.bbolt.WriteCursorLemmas
public import Spec.go_etcd_io.bbolt.Bucket__pageNode_w
public import Spec.go_etcd_io.bbolt.elemRef__isLeaf_w
public import Spec.go_etcd_io.bbolt.Cursor__nsearch_w

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

/-- `Cursor.search.wspec`, as an Iris proposition. -/
def searchIw : IProp GF :=
  iprop(∀ (cl : Loc) (cv : Cursor) (es : List elemRef) (W : WView) (hwm : Nat) (bl : Loc)
    (B : BRec) (txl : Loc) (pmap : GoMap) (pm : GMap w64 Loc) (dqp : DFrac) (pid : w64)
    (key : GoSlice) (kb : List w8) (dk : DFrac),
  ⌜cv.bucket' = bl ∧ wctxOK W hwm bl B txl pm ∧ posOK W hwm B pid⌝ →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ cl ↦ cv ∗ cv.stack' ↦* es ∗
      ownSliceCap elemRef cv.stack' (DFrac.own 1) ∗ wctx W bl B txl pmap pm dqp ∗ key ↦*{dk} kb }}
    (App (App (Val (cl @!! go.GoType.PointerType Cursor.ty @!! go!"search")) (Val #key)) (Val #pid))
  {{ (cv' : Cursor) (path : List elemRef), RET #();
      ⌜cv'.bucket' = bl ∧ wpath W B pid path⌝ ∗
      cl ↦ cv' ∗ cv'.stack' ↦* (es ++ path) ∗ ownSliceCap elemRef cv'.stack' (DFrac.own 1) ∗
      wctx W bl B txl pmap pm dqp ∗ key ↦*{dk} kb }})

/-- `Cursor.searchPage.wspec`, as an Iris proposition. -/
def searchPageIw : IProp GF :=
  iprop(∀ (cl : Loc) (cv : Cursor) (es : List elemRef) (rv : elemRef) (W : WView) (hwm : Nat)
    (bl : Loc) (B : BRec) (txl : Loc) (pmap : GoMap) (pm : GMap w64 Loc) (dqp : DFrac)
    (pid : w64) (pg : List w8) (key : GoSlice) (kb : List w8) (dk : DFrac),
  ⌜cv.bucket' = bl ∧ wctxOK W hwm bl B txl pm ∧ es.getLast? = some rv ∧ rv.node' = null ∧
    B.ib.root' ≠ W64 0 ∧ W.pages !! uint.nat pid = some pg ∧
    rv.page' = W.data +ₗ ((uint.nat pid * W.ps : Nat) : Int) ∧
    pageFlags pg = branchPageFlag ∧ branchWF pg pg.length hwm ∧ 16 ≤ pg.length ∧
    (∀ i < pageCount pg, posOK W hwm B (W64 (branchPgid pg i : Int)))⌝ →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ cl ↦ cv ∗ cv.stack' ↦* es ∗
      ownSliceCap elemRef cv.stack' (DFrac.own 1) ∗ wctx W bl B txl pmap pm dqp ∗ key ↦*{dk} kb }}
    (App (App (Val (cl @!! go.GoType.PointerType Cursor.ty @!! go!"searchPage")) (Val #key))
      (Val #rv.page'))
  {{ (cv' : Cursor) (i : w64) (path : List elemRef), RET #();
      ⌜cv'.bucket' = bl ∧ 0 ≤ sint.Z i ∧ sint.Z i < pageCount pg ∧
        wpath W B (W64 (branchPgid pg (sint.Z i).toNat : Int)) path⌝ ∗
      cl ↦ cv' ∗ cv'.stack' ↦* (es.set (es.length - 1) { rv with index' := i } ++ path) ∗
      ownSliceCap elemRef cv'.stack' (DFrac.own 1) ∗ wctx W bl B txl pmap pm dqp ∗ key ↦*{dk} kb }})

/-- `Cursor.searchNode.spec`, as an Iris proposition. -/
def searchNodeIw : IProp GF :=
  iprop(∀ (cl : Loc) (cv : Cursor) (es : List elemRef) (rv : elemRef) (W : WView) (hwm : Nat)
    (bl : Loc) (B : BRec) (txl : Loc) (pmap : GoMap) (pm : GMap w64 Loc) (dqp : DFrac)
    (nl : Loc) (r : NRec) (key : GoSlice) (kb : List w8) (dk : DFrac),
  ⌜cv.bucket' = bl ∧ wctxOK W hwm bl B txl pm ∧ es.getLast? = some rv ∧ rv.node' = nl ∧
    B.ns !! nl = some r ∧ r.nv.isLeaf' = false⌝ →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ cl ↦ cv ∗ cv.stack' ↦* es ∗
      ownSliceCap elemRef cv.stack' (DFrac.own 1) ∗ wctx W bl B txl pmap pm dqp ∗ key ↦*{dk} kb }}
    (App (App (Val (cl @!! go.GoType.PointerType Cursor.ty @!! go!"searchNode")) (Val #key))
      (Val #nl))
  {{ (cv' : Cursor) (i : w64) (path : List elemRef) (w : WEntry), RET #();
      ⌜cv'.bucket' = bl ∧ 0 ≤ sint.Z i ∧ r.ws[(sint.Z i).toNat]? = some w ∧
        wpath W B w.pgid path⌝ ∗
      cl ↦ cv' ∗ cv'.stack' ↦* (es.set (es.length - 1) { rv with index' := i } ++ path) ∗
      ownSliceCap elemRef cv'.stack' (DFrac.own 1) ∗ wctx W bl B txl pmap pm dqp ∗ key ↦*{dk} kb }})

theorem entryGE_of_eq (es : List NodeEntry) (kb : List w8) (h : Nat) (he : entryKey es h = kb) :
    entryGE es kb (h : Int) = true := by
  simp only [entryGE, Int.toNat_natCast, he, decide_eq_true_eq, ne_eq, compareResult_eq_neg1]
  exact goStringLt_irrefl kb

set_option maxHeartbeats 400000 in
/-- `searchNode`, given `search` for the children. -/
theorem searchNode_of_search_w (hK : Inode.Key.spec (GF := GF) (hG := hG))
    (hPgid : Inode.Pgid.spec (GF := GF) (hG := hG)) :
    □ searchIw (GF := GF) ⊢ searchNodeIw := by
  unfold searchIw searchNodeIw
  iintro #IH %cl %cv %es %rv %W %hwm %bl %B %txl %pmap %pm %dqp %nl %r %key %kb %dk %Hpre
  obtain ⟨Hbl, HOK, Hlast, Hnode, Hr, Hbr⟩ := Hpre
  have HN := HOK.2.1.2.2.2.2.2.2.2.1 nl r Hr
  obtain ⟨-, Hilen, Hsort, -, Hlive, -⟩ := id HN
  obtain ⟨Hne0, -, -⟩ := HN.2.2.2.2.2.2.2.2.2.2.2.1 Hbr
  wp_start as ⟨Hcl, Hs, Hcap, Hctx, Hk⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  have Hne : es ≠ [] := by intro h; subst h; simp at Hlast
  have Hpos : 0 < es.length := List.length_pos_iff.2 Hne
  have Hli : es[es.length - 1]? = some rv := by
    rw [List.getLast?_eq_getElem?] at Hlast; exact Hlast
  have Hix : (sint.Z (cv.stack'.len - W64 1)).toNat = es.length - 1 := by word
  ihave #Hsort' : isPkgInit (PROP := IProp GF) pkg_id.sort $$ []
  · iPkgInit
  ihave #Hbytes : isPkgInit (PROP := IProp GF) pkg_id.bytes $$ []
  · iPkgInit
  isimp only [wctx] at Hctx
  icases Hctx with ⟨Hb, Hv, Hpf, Hpm, Hdb⟩
  isimp only [wView] at Hv
  icases Hv with ⟨Hdata, #Hps, #Hlg, Hfli, #Hdl, %Hlgv, Hpv⟩
  icases bktOwn_node_acc W bl B nl r Hr $$ Hb with ⟨Hn, Hback⟩
  isimp only [nodeOwn] at Hn
  icases Hn with ⟨Hn, Hins, Hicap, Hents, Hch, Hchcap, Hkey⟩
  icases nodeBorrow W HOK.1.1 r.ws r.ins W.q Hlive $$ [Hpv Hents] with ⟨%ens, %Hm, Ho, Hpback⟩
  · iframe
  have Hsorted : entriesSorted ens := (wMatch_sorted _ _ Hm).2 Hsort
  ihave %Hisl := ownSlice_len _ _ _ $$ Hins
  ihave %Hol := inodesOwn_length _ _ $$ Ho
  wp_auto
  have Hlen : sint.Z r.nv.inodes'.len = (ens.length : Int) := by word
  wp_apply sort.wp_Search r.nv.inodes'.len _ (entryGE ens kb)
    iprop(n_ptr ↦ nl ∗ key_ptr ↦ key ∗ nl ↦ r.nv ∗ r.nv.inodes' ↦* r.ins ∗ inodesOwn r.ins ens ∗
      key ↦*{dk} kb ∗
      ∃ (e : Bool), exact_ptr ↦ e ∗ ⌜e = true → ∃ h, h < ens.length ∧ entryKey ens h = kb⌝)
    $$ [n key Hn Hins Ho Hk exact]
  · iframe
    isplitl []
    · ipureintro; word
    isplitl []
    · unfold sort.predImplements
      iintro %i
      wp_start as ⟨⟨Hnp, Hkp, Hn, Hins, Ho, Hk, %e, Hex, %He⟩, %Hb⟩
      wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hb.1, by word⟩)]
      list_elem r.ins (sint.Z i).toNat as it
      list_elem ens (sint.Z i).toNat as e'
      icases ownSlice_elem_acc (sint.Z i) it _ _ r.ins Hb.1 Hit_lookup $$ Hins with ⟨Hit, Hsback⟩
      wp_apply hK $$ [$Hit] as Hit
      try wp_auto
      icases inodesOwn_key_acc _ _ _ it e' Hit_lookup He'_lookup $$ Ho with ⟨Hkk, Hoback⟩
      wp_apply bytes.wp_Compare _ _ _ _ _ _ $$ [Hkk Hk] as ⟨Hkk, Hk⟩
      · iframe
      try wp_auto
      ispecialize Hoback $$ Hkk
      ihave Hins := Hsback $$ Hit
      rw [list_set_lookup_self _ _ _ Hit_lookup]
      have Hek : entryKey ens (sint.Z i).toNat = e'.key := by
        unfold entryKey; rw [He'_lookup]; rfl
      have Hit' : (sint.Z i).toNat < ens.length := (List.getElem?_eq_some_iff.1 He'_lookup).1
      wp_if_destruct
      · try wp_auto
        iapply HΦ
        iframe
        ipureintro
        refine ⟨fun _ => ⟨_, Hit', Hek.trans (compareResult_eq_zero _ _ Hif)⟩, ?_⟩
        simp only [entryGE, Hek, ne_eq, ← decide_not]
      · try wp_auto
        iapply HΦ
        iframe
        ipureintro
        refine ⟨He, ?_⟩
        simp only [entryGE, Hek, ne_eq, ← decide_not]
    ipureintro; rw [Hlen]; exact ⟨fun h => absurd h (by decide), entryGE_mono ens kb Hsorted⟩
  iintro %idx ⟨⟨Hnp, Hkp, Hn, Hins, Ho, Hk, %e, Hex, %He⟩, %H0, %Hfound, %Hoob, %Hgt⟩
  rw [Hlen] at Hfound Hoob
  have Hle' : sint.Z idx ≤ (ens.length : Int) := by
    refine Classical.byContradiction fun hcn => ?_
    have := Hoob (fun j hj => Hgt j ⟨hj.1, by omega⟩)
    omega
  have Hlt : ∀ k, k < ens.length → entryGE ens kb (k : Int) = true → sint.Z idx ≤ k := by
    intro k hk hg
    refine Classical.byContradiction fun hcn => ?_
    rw [Hgt k ⟨by omega, by omega⟩] at hg; cases hg
  have Hwl : ens.length = r.ws.length := (wMatch_length Hm).symm
  ihave Hpb := Hpback $$ Ho
  icases Hpb with ⟨Hpv, Hents⟩
  try wp_auto
  cases e
  on_goal 1 =>
    try wp_auto
    wp_if_destruct
    on_goal 1 =>
      try wp_auto
      have Hi : 0 ≤ sint.Z (idx - W64 1) ∧ sint.Z (idx - W64 1) < (ens.length : Int) := by word
      generalize idx - W64 1 = i at Hi ⊢
    on_goal 2 =>
      try wp_auto
      have Hi : 0 ≤ sint.Z idx ∧ sint.Z idx < (ens.length : Int) := by
        have : 0 < ens.length := by rw [Hwl]; exact Hne0
        word
      generalize idx = i at Hi ⊢
  on_goal 3 =>
    try wp_auto
    obtain ⟨h, hh, hk⟩ := He rfl
    have := Hlt h hh (entryGE_of_eq ens kb h hk)
    have Hi : 0 ≤ sint.Z idx ∧ sint.Z idx < (ens.length : Int) := by omega
    generalize idx = i at Hi ⊢
  all_goals
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (cv.stack'.len - W64 1) ∧
      sint.Z (cv.stack'.len - W64 1) < sint.Z cv.stack'.len from ⟨by word, by word⟩))]
    icases ownSlice_elem_acc (sint.Z (cv.stack'.len - W64 1)) rv _ _ es (by word)
      (by rw [Hix]; exact Hli) $$ Hs with ⟨Hr', Hsback⟩
    try wp_auto
    ispecialize Hsback $$ %({ rv with index' := i } : elemRef) Hr'
    rw [Hix]
    have Hit : (sint.Z i).toNat < r.ins.length := by rw [Hilen, ← Hwl]; omega
    obtain ⟨it, Hit_lookup⟩ : ∃ it, r.ins[(sint.Z i).toNat]? = some it :=
      ⟨_, List.getElem?_eq_getElem Hit⟩
    obtain ⟨w, Hw⟩ : ∃ w, r.ws[(sint.Z i).toNat]? = some w :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hilen]; exact Hit)⟩
    icases wOwn_at W r.ins r.ws _ it w Hit_lookup Hw $$ Hents with ⟨%Hfp, Hents⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z r.nv.inodes'.len
      from ⟨Hi.1, by word⟩))]
    icases ownSlice_elem_acc (sint.Z i) it r.nv.inodes' _ _ Hi.1 Hit_lookup $$ Hins with ⟨Hit', Hiback⟩
    wp_apply hPgid $$ [$Hit'] as Hit'
    ihave Hins := Hiback $$ Hit'
    rw [list_set_lookup_self _ _ _ Hit_lookup, Hfp.2]
    ihave Hb := Hback $$ %r [Hn Hins Hicap Hents Hch Hchcap Hkey]
    · unfold nodeOwn; iframe
    rw [bktOwn_insert_same W bl B nl r Hr]
    ihave Hctx : wctx W bl B txl pmap pm dqp $$ [Hb Hdata Hfli Hpv Hpf Hpm Hdb]
    · unfold wctx wView; iframe; iframe #; ipureintro; exact Hlgv
    try wp_auto
    wp_apply IH $$ %cl %cv %(es.set (es.length - 1) { rv with index' := i }) %W %hwm %bl %B %txl
        %pmap %pm %dqp %w.pgid %key %kb %dk [] [Hcl Hsback Hcap Hctx Hk]
      as %cv' %path ⟨%Hp, Hcl, Hs, Hcap, Hctx, Hk⟩
    · ipureintro; exact ⟨Hbl, HOK, posOK_node_child W hwm bl B nl r HOK.2.1 Hr Hbr _ w Hw⟩
    · iframe
    try wp_auto
    iapply HΦ
    iframe
    ipureintro
    exact ⟨Hp.1, Hi.1, Hw, Hp.2⟩

set_option maxHeartbeats 400000 in
theorem searchPage_of_search_w
    (hBPEs : Page.BranchPageElements.spec (GF := GF) (hG := hG))
    (hCount : Page.Count.spec (GF := GF) (hG := hG))
    (hKey : branchPageElement.Key.spec (GF := GF) (hG := hG))
    (hPgid : branchPageElement.Pgid.spec (GF := GF) (hG := hG)) :
    □ searchIw (GF := GF) ⊢ searchPageIw := by
  unfold searchIw searchPageIw
  iintro #IH %cl %cv %es %rv %W %hwm %bl %B %txl %pmap %pm %dqp %pid %pg %key %kb %dk %Hpre
  obtain ⟨Hbl, HOK, Hlast, Hnode, Hroot, Hpgm, Hpa, Hbr, Hwf, Hlen, Hkids⟩ := Hpre
  wp_start as ⟨Hcl, Hs, Hcap, Hctx, Hk⟩
  isimp only [wctx] at Hctx
  icases Hctx with ⟨Hb, Hv, Hpf, Hpm, Hdb⟩
  isimp only [wView] at Hv
  icases Hv with ⟨Hdata, #Hps, #Hlg, Hfli, #Hdl, %Hlgv, Hpgs⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  have Hne : es ≠ [] := by intro h; subst h; simp at Hlast
  have Hpos : 0 < es.length := List.length_pos_iff.2 Hne
  have Hli : es[es.length - 1]? = some rv := by
    rw [List.getLast?_eq_getElem?] at Hlast; exact Hlast
  have Hix : (sint.Z (cv.stack'.len - W64 1)).toNat = es.length - 1 := by word
  have Hc : rv.page'.locCar ≠ 0 := by rw [Hpa]; simpa [Loc.add] using HOK.1.1
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  ihave #Hsort : isPkgInit (PROP := IProp GF) pkg_id.sort $$ []
  · iPkgInit
  ihave #Hbytes : isPkgInit (PROP := IProp GF) pkg_id.bytes $$ []
  · iPkgInit
  icases viewLoc_acc (GF := GF) W rv.page' pg (Hpa ▸ inViewLoc_page W _ pg Hpgm) $$ Hpgs
    with ⟨Hpg, Hpgsback⟩
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
      key_ptr ↦ key ∗ key ↦*{dk} kb ∗ bytesPointsto rv.page' (DFrac.own W.q) pg ∗
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
    ihave Hctx : wctx W bl B txl pmap pm dqp $$ [Hb Hdata Hfli Hpgsback Hpf Hpm Hdb]
    · unfold wctx wView; iframe; iframe #; ipureintro; exact Hlgv
    wp_apply IH $$ %cl %cv %(es.set (es.length - 1) { rv with index' := i }) %W %hwm %bl %B %txl
        %pmap %pm %dqp %(W64 (branchPgid pg (sint.Z i).toNat)) %key %kb %dk [] [Hcl Hsback Hcap Hctx Hk]
      as %cv' %path ⟨%Hp, Hcl, Hs, Hcap, Hctx, Hk⟩
    · ipureintro; exact ⟨Hbl, HOK, Hkids _ Hit⟩
    · iframe
    try wp_auto
    iapply HΦ
    iframe
    ipureintro
    exact ⟨Hp.1, Hi.1, Hi.2, Hp.2⟩

set_option maxHeartbeats 800000 in
/-- `search`, by Löb induction: its recursive calls are through `searchPage` and `searchNode`. -/
theorem search_loeb_w
    (hpageNode : Bucket.pageNode.wspec (GF := GF) (hG := hG))
    (hIsBranch : Page.IsBranchPage.spec (GF := GF) (hG := hG))
    (hIsLeaf : Page.IsLeafPage.spec (GF := GF) (hG := hG))
    (hisLeaf : elemRef.isLeaf.wspec (GF := GF) (hG := hG))
    (hnsearch : Cursor.nsearch.wspec (GF := GF) (hG := hG))
    (hBPEs : Page.BranchPageElements.spec (GF := GF) (hG := hG))
    (hCount : Page.Count.spec (GF := GF) (hG := hG))
    (hKey : branchPageElement.Key.spec (GF := GF) (hG := hG))
    (hPgid : branchPageElement.Pgid.spec (GF := GF) (hG := hG))
    (hK : Inode.Key.spec (GF := GF) (hG := hG))
    (hIPgid : Inode.Pgid.spec (GF := GF) (hG := hG)) :
    ⊢ searchIw (GF := GF) := by
  iloeb as IH
  ihave #HSP := searchPage_of_search_w hBPEs hCount hKey hPgid
  ihave #HSN := searchNode_of_search_w hK hIPgid
  unfold searchIw
  iintro %cl %cv %es %W %hwm %bl %B %txl %pmap %pm %dqp %pid %key %kb %dk %Hpre
  obtain ⟨Hbl, HOK, Hpos⟩ := Hpre
  obtain ⟨HvOK, Hclean, Htx, Hpmv⟩ := HOK
  wp_start as ⟨Hcl, Hs, Hcap, Hctx, Hk⟩
  ihave #HSP' := HSP $$ [#]
  · iexact IH
  ihave #HSN' := HSN $$ [#]
  · iexact IH
  iclear HSP HSN
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  isimp only [wctx] at Hctx
  icases Hctx with ⟨Hb, Hv, Hpf, Hpm, Hdb⟩
  isimp only [bktOwn] at Hb
  icases Hb with ⟨Hbv, Hib, Hnm, Hbm, Hpo, Hns⟩
  have Hnn : ∀ c l, B.nm !! c = some l → l ≠ null := fun c l h => (Hclean.2.2.2.2.1 c l h).1
  have Hfile : B.ib.root' ≠ W64 0 → resolve B pid = none → pm !! pid = none ∧ ∃ pg,
      W.pages !! uint.nat pid = some pg ∧ 16 ≤ pg.length ∧ W64 (pageId pg) = pid ∧
      validPageFlags (W16 (pageFlags pg)) ∧ uint.nat pid * W.ps < 281474976710655 := by
    intro hr hres
    obtain ⟨pg, hpg, -, hwf, -⟩ := posOK_page W hwm B pid hr hres Hpos
    obtain ⟨hl, hid, -, hk⟩ := treeWF_page _ _ _ pg hwf hpg
    refine ⟨Hpmv pid (by rw [hpg]; rfl), pg, hpg, hl, ?_, ?_, (HvOK.2.2.2.1 _ pg hpg)⟩
    · rw [hid]; unfold uint.nat; word
    · exact validPageFlags_of pg (by rcases hk with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h])
  wp_auto
  rw [Hbl]
  wp_apply hpageNode W bl B.bv B (DFrac.own 1) txl pmap pm dqp pid rfl Htx Hnn Hpos.1 Hfile
    HvOK.1 HvOK.2.2.1 $$ [Hbv Hib Hnm Hv Hpf Hpm Hdb] as %p %n ⟨%Hpn, Hbv, Hib, Hnm, Hv, Hpf, Hpm, Hdb⟩
  · iframe
  rcases Hpn with ⟨Hres, rfl⟩ | ⟨Hres, rfl, pg, Hpa⟩
  · obtain ⟨r, Hr⟩ : ∃ r, B.ns !! n = some r := by
      rcases Hpos.2 with ⟨l, r, h1, h2⟩ | ⟨h1, -⟩
      · rw [Hres] at h1; cases h1; exact ⟨r, h2⟩
      · rw [Hres] at h1; cases h1
    have Hnnull : n ≠ null := by
      unfold resolve at Hres
      split at Hres
      · split at Hres
        · cases Hres
        · cases Hres; assumption
      · exact Hnn _ _ Hres
    try wp_auto
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_slice_append $$ [$Hs $Hcap $Hsl] as %s' ⟨Hs, Hcap, -⟩
    try wp_auto
    icases (BigSepM.bigSepM_lookup_acc (M := GMap Loc) (Φ := fun l r => nodeOwn (GF := GF) W l r)
      (show Std.get? B.ns n = some r from Hr)).1 $$ Hns with ⟨Hnd, Hnsback⟩
    isimp only [nodeOwn] at Hnd
    icases Hnd with ⟨Hn0, Hins, Hicap, Hents, Hch, Hchcap, Hkey⟩
    wp_apply hisLeaf e_ptr { page' := null, node' := n, index' := 0 } (DFrac.own 1) r.nv (DFrac.own 1)
      (DFrac.own 1) [] (fun h => absurd h Hnnull) $$ [e Hn0] as ⟨e, Hn0⟩
    · simp only [Hnnull, ↓reduceIte]; iframe
    simp only [Hnnull, ↓reduceIte]
    have HN := Hclean.2.2.2.2.2.2.2.1 n r Hr
    obtain ⟨-, Hilen, Hsort, -, Hlive, -⟩ := id HN
    cases Hleaf : r.nv.isLeaf'
    · -- a branch node
      try wp_auto
      rw [decide_eq_false Hnnull, Bool.not_false]
      try wp_auto
      ihave Hb : bktOwn W bl B $$ [Hbv Hib Hnm Hbm Hpo Hnsback Hn0 Hins Hicap Hents Hch Hchcap Hkey]
      · unfold bktOwn; iframe
        iapply Hnsback
        unfold nodeOwn; iframe
      ihave Hctx : wctx W bl B txl pmap pm dqp $$ [Hb Hv Hpf Hpm Hdb]
      · unfold wctx; iframe
      unfold searchNodeIw
      wp_apply HSN' $$ %cl %{ cv with stack' := s' } %(es ++ [{ page' := null, node' := n, index' := 0 }])
          %{ page' := null, node' := n, index' := 0 } %W %hwm %bl %B %txl %pmap %pm %dqp %n %r
          %key %kb %dk [] [Hcl Hs Hcap Hctx Hk]
        as %cv' %i %path %w ⟨%Hsn, Hcl, Hs, Hcap, Hctx, Hk⟩
      · ipureintro; exact ⟨Hbl, ⟨HvOK, Hclean, Htx, Hpmv⟩, by simp, rfl, Hr, Hleaf⟩
      · iframe
      try wp_auto
      rw [set_last_append, List.append_assoc, List.singleton_append]
      obtain ⟨Hb', Hi0, Hw, Hpath⟩ := Hsn
      ispecialize HΦ $$ %cv' %({ page' := null, node' := n, index' := i } :: path)
      iapply HΦ
      iframe
      ipureintro
      refine ⟨Hb', ?_⟩
      cases path with
      | nil => exact absurd Hpath (by simp [wpath])
      | cons r2 rs =>
        refine ⟨Or.inl ⟨n, Hres, rfl, rfl⟩, Hi0, r.ws.map WEntry.pgid, w.pgid, ?_, ?_, Hpath⟩
        · unfold kidsAt; rw [Hres]; simp [Hr, Hleaf]
        · rw [List.getElem?_map, Hw]; rfl
    · -- a leaf node
      try wp_auto
      isimp only [wView] at Hv
      icases Hv with ⟨Hdata, #Hps, #Hlg, Hfli, #Hdl, %Hlgv, Hpv⟩
      icases nodeBorrow W HvOK.1 r.ws r.ins W.q Hlive $$ [Hpv Hents] with ⟨%ens, %Hm, Ho, Hpback⟩
      · iframe
      have Hsorted : entriesSorted ens := (wMatch_sorted _ _ Hm).2 Hsort
      wp_apply hnsearch cl { cv with stack' := s' } (DFrac.own 1) (es ++ [{ page' := null, node' := n, index' := 0 }])
          { page' := null, node' := n, index' := 0 } (DFrac.own 1) [] r.nv (DFrac.own 1) r.ins (DFrac.own 1)
          ens key kb dk (by simp) (fun h => absurd h Hnnull) (fun _ => Hsorted)
        $$ [Hcl Hs Hn0 Hins Ho Hk] as %idx ⟨%Hidx, Hcl, Hs, Hres', Hk⟩
      · unfold leafRes; simp only [Hnnull, ↓reduceIte]; iframe
      unfold leafRes
      simp only [Hnnull, ↓reduceIte]
      icases Hres' with ⟨Hn0, Hins, Ho⟩
      ihave Hpb := Hpback $$ Ho
      icases Hpb with ⟨Hpv, Hents⟩
      try wp_auto
      ihave Hb : bktOwn W bl B $$ [Hbv Hib Hnm Hbm Hpo Hnsback Hn0 Hins Hicap Hents Hch Hchcap Hkey]
      · unfold bktOwn; iframe
        iapply Hnsback
        unfold nodeOwn; iframe
      rw [set_last_append]
      ispecialize HΦ $$ %{ cv with stack' := s' } %([{ page' := null, node' := n, index' := idx }] : List elemRef)
      iapply HΦ
      isplitr
      · ipureintro
        refine ⟨Hbl, Or.inl ⟨n, Hres, rfl, rfl⟩, Hidx.1, r.ws.map WEntry.pgid, ?_⟩
        unfold kidsAt; rw [Hres]; simp [Hr, Hleaf]
      iframe
      unfold wctx wView; iframe; iframe #; ipureintro; exact Hlgv
  · -- a page
    have Hinl : B.ib.root' = W64 0 → B.bv.page' ≠ null ∧ B.isrc ≠ Src.stale := by
      intro h0
      rcases Hpos.2 with ⟨l, r, h1, -⟩ | ⟨-, ⟨-, -, h2, h3, -⟩ | ⟨h4, -⟩⟩
      · rw [Hres] at h1; cases h1
      · exact ⟨h2, h3⟩
      · exact absurd h0 h4
    obtain ⟨Hlen, Hkind⟩ : 16 ≤ pg.length ∧
        ((pageFlags pg = leafPageFlag ∧ leafWF pg pg.length) ∨
         (pageFlags pg = branchPageFlag ∧ branchWF pg pg.length hwm ∧ B.ib.root' ≠ W64 0 ∧
           W.pages !! uint.nat pid = some pg ∧ p = W.data +ₗ ((uint.nat pid * W.ps : Nat) : Int) ∧
           ∀ i < pageCount pg, posOK W hwm B (W64 (branchPgid pg i : Int)))) := by
      by_cases hr : B.ib.root' = W64 0
      · rcases Hpos.2 with ⟨l, r, h1, -⟩ | ⟨-, ⟨-, h0, -, -, hg⟩ | ⟨h4, -⟩⟩
        · rw [Hres] at h1; cases h1
        · unfold wpageAt at Hpa; rw [if_pos hr, if_pos h0] at Hpa; cases Hpa
          obtain ⟨-, hfl, hwf, hl, -⟩ := hg
          exact ⟨hl, Or.inl ⟨hfl, hwf⟩⟩
        · exact absurd hr h4
      · obtain ⟨pg', hpg, hpa', hwf, hfree⟩ := posOK_page W hwm B pid hr Hres Hpos
        rw [Hpa] at hpa'; cases hpa'
        obtain ⟨hl, -, -, hk⟩ := treeWF_page _ _ _ _ hwf hpg
        refine ⟨hl, ?_⟩
        rcases hk with ⟨hfl, hw, -⟩ | ⟨hfl, hw, hkids⟩
        · exact Or.inl ⟨hfl, hw⟩
        · exact Or.inr ⟨hfl, hw, hr, hpg, rfl, fun i hi =>
            posOK_page_child W hwm B pid pg hr hpg hfl hkids hfree i hi⟩
    isimp only [wView] at Hv
    icases Hv with ⟨Hdata, #Hps, #Hlg, Hfli, #Hdl, %Hlgv, Hpv⟩
    have Hne : pg ≠ [] := by intro h; rw [h] at Hlen; simp at Hlen
    icases wpageAt_acc W B pid p pg HvOK.1 Hpa Hinl Hne $$ [Hpv Hpo] with ⟨%dq, %Hc, Hpg, Hpgback⟩
    · iframe
    have Hpn : p ≠ null := fun h => Hc (by rw [h]; rfl)
    try wp_auto
    rw [decide_eq_false Hpn]
    icases (page_header_bytes (hG := hG) _ _ pg Hlen Hc).1 $$ Hpg with ⟨Hhd, Hrest⟩
    try wp_auto
    wp_apply hIsBranch _ (pageOf pg) _ $$ [Hhd] as Hhd
    · iframe
    have Hfl1 : (pageOf pg).flags' = W16 ((pageFlags pg : Nat) : Int) := rfl
    try rw [Hfl1]
    rcases Hkind with ⟨Hfl, Hlw⟩ | ⟨Hfl, Hbw, Hr0, Hpgm, Hpeq, Hkids⟩
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
      wp_apply hisLeaf e_ptr { page' := p, node' := null, index' := 0 } (DFrac.own 1) (zero_val node)
        (DFrac.own 1) dq pg (fun _ => ⟨Hc, Hlen⟩) $$ [e Hpg] as ⟨e, Hpg⟩
      · simp only [↓reduceIte]; iframe
      simp only [↓reduceIte, Hfl]
      rw [decide_eq_true (by unfold leafPageFlag; decide)]
      try wp_auto
      wp_apply hnsearch cl { cv with stack' := s' } (DFrac.own 1) (es ++ [{ page' := p, node' := null, index' := 0 }])
          { page' := p, node' := null, index' := 0 } dq pg (zero_val node) (DFrac.own 1) [] (DFrac.own 1)
          [] key kb dk (by simp) (fun _ => ⟨Hc, Hlen, Hfl, Hlw⟩) (fun h => absurd rfl h)
        $$ [Hcl Hs Hpg Hk] as %idx ⟨%Hidx, Hcl, Hs, Hpg, Hk⟩
      · unfold leafRes; simp only [↓reduceIte]; iframe
      unfold leafRes
      simp only [↓reduceIte]
      try wp_auto
      ispecialize Hpgback $$ Hpg
      icases Hpgback with ⟨Hpv, Hpo⟩
      rw [set_last_append]
      ispecialize HΦ $$ %{ cv with stack' := s' } %([{ page' := p, node' := null, index' := idx }] : List elemRef)
      iapply HΦ
      isplitr
      · ipureintro
        refine ⟨Hbl, Or.inr ⟨Hres, rfl, pg, Hpa⟩, Hidx.1, (List.range (pageCount pg)).map fun i => W64 (branchPgid pg i : Int), ?_⟩
        unfold kidsAt; rw [Hres, Hpa]; simp [Hfl]
      iframe
      unfold wctx wView bktOwn; iframe; iframe #; ipureintro; exact Hlgv
    · rw [Hfl, decide_eq_true (by unfold branchPageFlag; decide)]
      try wp_auto
      ihave Hpg := (page_header_bytes (hG := hG) _ _ pg Hlen Hc).2 $$ [$Hhd $Hrest]
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_apply wp_slice_append $$ [$Hs $Hcap $Hsl] as %s' ⟨Hs, Hcap, -⟩
      try wp_auto
      wp_apply hisLeaf e_ptr { page' := p, node' := null, index' := 0 } (DFrac.own 1) (zero_val node)
        (DFrac.own 1) dq pg (fun _ => ⟨Hc, Hlen⟩) $$ [e Hpg] as ⟨e, Hpg⟩
      · simp only [↓reduceIte]; iframe
      simp only [↓reduceIte, Hfl]
      rw [decide_eq_false (by unfold branchPageFlag; decide)]
      try wp_auto
      ispecialize Hpgback $$ Hpg
      icases Hpgback with ⟨Hpv, Hpo⟩
      ihave Hctx : wctx W bl B txl pmap pm dqp $$ [Hbv Hib Hnm Hbm Hpo Hns Hdata Hpv Hfli Hpf Hpm Hdb]
      · unfold wctx wView bktOwn; iframe; iframe #; ipureintro; exact Hlgv
      unfold searchPageIw
      wp_apply HSP' $$ %cl %{ cv with stack' := s' } %(es ++ [{ page' := p, node' := null, index' := 0 }])
          %{ page' := p, node' := null, index' := 0 } %W %hwm %bl %B %txl %pmap %pm %dqp %pid %pg
          %key %kb %dk [] [Hcl Hs Hcap Hctx Hk]
        as %cv' %i %path ⟨%Hsp, Hcl, Hs, Hcap, Hctx, Hk⟩
      · ipureintro; exact ⟨Hbl, ⟨HvOK, Hclean, Htx, Hpmv⟩, by simp, rfl, Hr0, Hpgm, Hpeq, Hfl, Hbw, Hlen, Hkids⟩
      · iframe
      try wp_auto
      rw [set_last_append, List.append_assoc, List.singleton_append]
      obtain ⟨Hb', Hi0, Hil, Hpath⟩ := Hsp
      ispecialize HΦ $$ %cv' %({ page' := p, node' := null, index' := i } :: path)
      iapply HΦ
      iframe
      ipureintro
      refine ⟨Hb', ?_⟩
      cases path with
      | nil => exact absurd Hpath (by simp [wpath])
      | cons r2 rs =>
        refine ⟨Or.inr ⟨Hres, rfl, pg, Hpa⟩, Hi0, (List.range (pageCount pg)).map fun i => W64 (branchPgid pg i : Int), _, ?_, ?_, Hpath⟩
        · unfold kidsAt; rw [Hres, Hpa]; simp [Hfl]; unfold branchPageFlag leafPageFlag; decide
        · simp only [List.getElem?_map, List.getElem?_range (show (sint.Z i).toNat < pageCount pg by omega)]
          rfl


end proof

end bbolt
end EtcdGrove
end Perennial
