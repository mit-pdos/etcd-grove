module
public import Spec.go_etcd_io.bbolt.Bucket__node
public import Spec.go_etcd_io.bbolt.Tx__page_w
public import Spec.go_etcd_io.bbolt.node__read
public import Spec.go_etcd_io.bbolt.TxStats__IncNodeCount
public import Spec.go_etcd_io.bbolt.internal.common.Assert
public import Spec.go_etcd_io.bbolt.internal.common.Verify

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The inline page's source after a node is read from it. -/
def isrcAfter (B : BRec) : Src :=
  match B.isrc with
  | .own _ => if B.bv.page' = null then B.isrc else Src.own DFrac.discard
  | s => s

/-- The bytes a new node reads, lent out of the view or the inline page, and the entries it
reads from them. -/
theorem nodeSrc_acc (W : WView) (B : BRec) (pm : GMap w64 Loc) (pgid : w64) (p : Loc)
    (pg : List w8) (src : Src) (h : nodeSrcOK W B pm pgid p pg src) :
    pagesView (GF := GF) W.data W.ps W.q W.pages ∗ pageOwn W B ⊢ |==> ∃ (dqr : DFrac) (src' : Src),
      ⌜(src = Src.view → src' = Src.view) ∧ (src ≠ Src.view → src' = Src.own DFrac.discard)⌝ ∗
      bytesPointsto p dqr pg ∗
      (bytesPointsto p dqr pg -∗ pagesView W.data W.ps W.q W.pages ∗
        pageOwn W { B with isrc := isrcAfter B }) ∗
      ([∗list] it;w ∈ inodesOf p pg;pageWs pg src', wOwn W it w) ∗
      (if pageCount pg = 0 then iprop(True)
       else srcOwn W (inodeOf p pg 0).key' src' (wKey (pageWs pg src') 0)) := by
  obtain ⟨Hr, Hc, Hinl, Hfile⟩ := h
  iintro ⟨Hpv, Hpo⟩
  by_cases hpn : B.bv.page' = null
  · obtain ⟨-, rfl, Hpg, rfl, -, -, -⟩ := Hfile hpn
    have Hin := inViewLoc_page W (uint.nat pgid) pg Hpg
    icases viewLoc_acc (GF := GF) W _ pg Hin $$ Hpv with ⟨Hb, Hback⟩
    imodintro
    iexists DFrac.own W.q, Src.view
    isplitr
    · ipureintro; exact ⟨fun _ => rfl, fun h => absurd rfl h⟩
    iframe Hb
    isplitl [Hback Hpo]
    · iintro Hb
      ihave Hpv := Hback $$ Hb
      iframe Hpv
      unfold pageOwn
      simp only [hpn, ↓reduceIte]
      itrivial
    isplitl []
    · iapply pageWs_view W _ pg Hin Hr
    split
    · itrivial
    · rename_i hcnt
      obtain ⟨-, -, Hk, -⟩ := inodeOf_inView W _ pg Hin Hr 0 (by omega)
      unfold srcOwn
      ipureintro
      rw [wKey_pageWs _ _ (by omega)]
      exact Hk
  · obtain ⟨-, rfl, rfl, rfl, Hsrc, -⟩ := Hinl hpn
    rcases Hsrc with Hv | Hd
    · unfold pageOwn
      simp only [hpn, ↓reduceIte, Hv]
      icases Hpo with %Hin
      icases viewLoc_acc (GF := GF) W _ B.ipg Hin $$ Hpv with ⟨Hb, Hback⟩
      imodintro
      iexists DFrac.own W.q, Src.view
      isplitr
      · ipureintro; exact ⟨fun _ => rfl, fun h => absurd rfl h⟩
      iframe Hb
      isplitl [Hback]
      · iintro Hb
        ihave Hpv := Hback $$ Hb
        iframe Hpv
        unfold isrcAfter
        simp only [Hv, hpn, ↓reduceIte]
        ipureintro; exact Hin
      isplitl []
      · iapply pageWs_view W _ B.ipg Hin Hr
      split
      · itrivial
      · rename_i hcnt
        obtain ⟨-, -, Hk, -⟩ := inodeOf_inView W _ B.ipg Hin Hr 0 (by omega)
        unfold srcOwn
        ipureintro
        rw [wKey_pageWs _ _ (by omega)]
        exact Hk
    · unfold pageOwn
      simp only [hpn, ↓reduceIte, Hd]
      haveI := (bytesPointsto_dfractional (GF := GF) B.bv.page' B.ipg).dfractional_persistent
      icases Hpo with #Hb
      imodintro
      iexists DFrac.discard, Src.own DFrac.discard
      isplitr
      · ipureintro; exact ⟨fun h => Src.noConfusion h, fun _ => rfl⟩
      iframe Hb
      isplitl [Hpv]
      · iintro -
        iframe Hpv
        unfold isrcAfter
        simp only [Hd, hpn, ↓reduceIte]
        iexact Hb
      isplitl []
      · iapply pageWs_disc W _ B.ipg Hr Hc $$ Hb
      split
      · itrivial
      · rename_i hcnt
        have hb := inode_key_bound B.ipg Hr 0 (by omega)
        rw [wKey_pageWs _ _ (by omega)]
        unfold srcOwn
        by_cases hf : pageFlags B.ipg = leafPageFlag
        · simp only [pageW, inodeOf, hf, ↓reduceIte]
          icases bytes_slice_acc (hG := hG) B.bv.page' DFrac.discard B.ipg (elemOff 0 + leafPos B.ipg 0)
            (leafKsize B.ipg 0) (by have := hb.1 hf; omega) (leAt_lt _ _ 4) Hc $$ Hb with ⟨Hk, -⟩
          unfold sliceAt leafKey
          iexact Hk
        · simp only [pageW, inodeOf, hf, ↓reduceIte]
          icases bytes_slice_acc (hG := hG) B.bv.page' DFrac.discard B.ipg (elemOff 0 + branchPos B.ipg 0)
            (branchKsize B.ipg 0) (by have := hb.2 hf; omega) (leAt_lt _ _ 4) Hc $$ Hb with ⟨Hk, -⟩
          unfold sliceAt branchKey
          iexact Hk

theorem uZ_pid_ps (pgid : w64) (ps : Nat) (hps : ps < 2 ^ 32)
    (h : uint.nat pgid * ps < 281474976710655) :
    uint.Z (pgid * W64 (ps : Int)) = ((uint.nat pgid * ps : Nat) : Int) := by
  have hu : uint.Z (pgid * W64 (ps : Int)) = (uint.Z pgid * uint.Z (W64 (ps : Int))) % 2 ^ 64 := by
    unfold uint.Z; rw [BitVec.toNat_mul, Int.natCast_emod, Int.natCast_mul, Int.natCast_pow]; rfl
  have e1 : uint.Z pgid = ((uint.nat pgid : Nat) : Int) := by unfold uint.nat uint.Z; simp
  have e2 : uint.Z (W64 (ps : Int)) = (ps : Int) := by word
  rw [hu, e1, e2, ← Int.natCast_mul]
  exact Int.emod_eq_of_lt (by omega) (by omega)

theorem Bucket.node.wp_proof (hA : Assert.spec (GF := GF) (hG := hG))
    (hVerify : Verify.spec (GF := GF) (hG := hG))
    (hpage : Tx.page.wspec (GF := GF) (hG := hG))
    (hread : node.read.spec (GF := GF) (hG := hG))
    (hInc : TxStats.IncNodeCount.spec (GF := GF) (hG := hG)) :
    Bucket.node.spec (GF := GF) (hG := hG) := by
  intro W bl B txl st pmap pm dqp pgid parent p pg src HvOK Htx Hnn Hsrc
  wp_start as ⟨Hb, Hv, Hst, Hpf, Hpm, Hdb⟩
  unfold bktOwn
  icases Hb with ⟨Hbv, Hib, Hnm, Hbm, Hpg, Hns⟩
  ihave %Hnmnn := ownMap_not_nil _ _ _ $$ Hnm
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  wp_auto
  rw [decide_eq_false Hnmnn, Bool.not_false]
  wp_apply hA
  try wp_auto
  wp_apply wp_map_lookup1 $$ Hnm as Hnm
  try wp_auto
  cases hk : B.nm !! pgid with
  | some l =>
    have Hl := Hnn l hk
    simp only [Option.getD_some]
    rw [decide_eq_false Hl]
    try wp_auto
    iapply HΦ
    iframe
    ipureintro
    unfold nodeRes
    exact Or.inl ⟨hk, rfl, rfl⟩
  | none =>
    obtain ⟨⟨Hrd, Hpc, Hinl, Hfile⟩, Hpar⟩ := Hsrc hk
    simp only [Option.getD_none]
    rw [decide_eq_true (show zero_val Loc = null from rfl)]
    try wp_auto
    unfold wView
    icases Hv with ⟨Hdata, #Hps, #Hlg, Hfli, #Hdl, %Hlgv, Hpv⟩
    ihave Hsrc := nodeSrc_acc (GF := GF) W B pm pgid p pg src ⟨Hrd, Hpc, Hinl, Hfile⟩ $$ [Hpv Hpg]
    · iframe
    imod Hsrc with ⟨%dqr, %src', %Hsrc', Hbytes, Hback, Hents, Hkey⟩
    wp_if_destruct
    · try wp_auto
      wp_if_destruct
      · obtain ⟨Hpm0, -, Hpgs, Hpeq, Hid, Hfl, Hlt⟩ := Hfile ‹_›
        try wp_auto
        rw [Htx]
        wp_apply hpage txl pmap pm dqp dqp W.dbl W.data (W64 (W.ps : Int)) (DFrac.own W.q) DFrac.discard pgid p dqr pg
          (Or.inr ⟨Hpm0, by rw [Hpeq, uZ_pid_ps _ _ HvOK.2.2.1 Hlt], HvOK.1,
            by rw [uZ_pid_ps _ _ HvOK.2.2.1 Hlt]; omega⟩) Hpc Hrd.1 Hid Hfl
          $$ [Hpf Hpm Hdb Hdata Hbytes] as ⟨Hpf, Hpm, Hdb, Hdata, -, Hbytes⟩
        · iframe
          iframe #
        try wp_auto
        wp_apply hread _ _ _ dqr pg Hpc Hrd $$ [$«$r0» Hbytes] as %s ⟨Hn, Hs, Hcap, Hbytes⟩
        · iframe
        try wp_auto
        wp_apply wp_mapInsert $$ Hnm as Hnm
        try wp_auto
        try simp only
        try rw [Htx]
        wp_apply hInc $$ [Hst] as %st' ⟨%Hst', Hst⟩
        · iframe
        try wp_auto
        icases ns_fresh W B.ns _ _ $$ Hns Hn with ⟨Hns, Hn, %Hfresh⟩
        ihave Hback := Hback $$ Hbytes
        icases Hback with ⟨Hpv, Hpg⟩
        icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn'⟩
        ispecialize HΦ $$ %«$r0_ptr» %(nodeAdded B pgid null «$r0_ptr» (readNRec bl null p pg s src') slice.nil) %st'
        iapply HΦ
        isplitl [Hbv Hib Hnm Hbm Hpg Hns Hn Hs Hcap Hents Hkey]
        · simp only [nodeAdded, parentAdd, ↓reduceIte]
          try rw [Htx]
          iframe Hbv Hib Hnm Hbm
          isplitl [Hpg]
          · iapply pageOwn_congr_wand W _ _ (by rfl) (by rfl) (by rfl) $$ Hpg
          iapply (BigSepM.bigSepM_insert (M := GMap Loc) (Φ := fun l r => nodeOwn (GF := GF) W l r)
            (show Std.get? B.ns «$r0_ptr» = none from Hfresh)).2
          iframe Hns
          unfold nodeOwn readNRec readNodeV
          simp only
          iframe Hn Hs Hcap Hents
          isplitl []
          · iapply ownSlice_nil
          isplitl []
          · iapply ownSliceCap_nil
          by_cases hc : pageCount pg = 0
          · simp only [hc, ↓reduceIte]
            itrivial
          · isimp only [hc, ↓reduceIte] at Hkey
            simp only [hc, ↓reduceIte]
            split
            · itrivial
            · iexact Hkey
        iframe
        iframe #
        isplitr
        · ipureintro; exact Hlgv
        ipureintro
        unfold nodeRes
        right
        exact ⟨hk, Hfresh, Hnn', by rw [Hst'], s, slice.nil, src', Hsrc'.1, Hsrc'.2, rfl⟩
      · obtain ⟨Hz, rfl, rfl, rfl, -, -⟩ := Hinl ‹_›
        subst Hz
        try wp_auto
        wp_apply hVerify _ iprop(pgId_ptr ↦ W64 0) $$ [pgId] as pgId
        · isplit
          · wp_auto
            iexact pgId
          · iexact pgId
        try wp_auto
        wp_apply hread _ _ _ dqr B.ipg Hpc Hrd $$ [$«$r0» Hbytes] as %s ⟨Hn, Hs, Hcap, Hbytes⟩
        · iframe
        try wp_auto
        wp_apply wp_mapInsert $$ Hnm as Hnm
        try wp_auto
        try simp only
        try rw [Htx]
        wp_apply hInc $$ [Hst] as %st' ⟨%Hst', Hst⟩
        · iframe
        try wp_auto
        icases ns_fresh W B.ns _ _ $$ Hns Hn with ⟨Hns, Hn, %Hfresh⟩
        ihave Hback := Hback $$ Hbytes
        icases Hback with ⟨Hpv, Hpg⟩
        icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn'⟩
        ispecialize HΦ $$ %«$r0_ptr» %(nodeAdded B (W64 0) null «$r0_ptr» (readNRec bl null B.bv.page' B.ipg s src') slice.nil) %st'
        iapply HΦ
        isplitl [Hbv Hib Hnm Hbm Hpg Hns Hn Hs Hcap Hents Hkey]
        · simp only [nodeAdded, parentAdd, ↓reduceIte]
          try rw [Htx]
          iframe Hbv Hib Hnm Hbm
          isplitl [Hpg]
          · iapply pageOwn_congr_wand W _ _ (by rfl) (by rfl) (by rfl) $$ Hpg
          iapply (BigSepM.bigSepM_insert (M := GMap Loc) (Φ := fun l r => nodeOwn (GF := GF) W l r)
            (show Std.get? B.ns «$r0_ptr» = none from Hfresh)).2
          iframe Hns
          unfold nodeOwn readNRec readNodeV
          simp only
          iframe Hn Hs Hcap Hents
          isplitl []
          · iapply ownSlice_nil
          isplitl []
          · iapply ownSliceCap_nil
          by_cases hc : pageCount B.ipg = 0
          · simp only [hc, ↓reduceIte]
            itrivial
          · isimp only [hc, ↓reduceIte] at Hkey
            simp only [hc, ↓reduceIte]
            split
            · itrivial
            · iexact Hkey
        iframe
        iframe #
        isplitr
        · ipureintro; exact Hlgv
        ipureintro
        unfold nodeRes
        right
        exact ⟨hk, Hfresh, Hnn', by rw [Hst'], s, slice.nil, src', Hsrc'.1, Hsrc'.2, rfl⟩
    · obtain ⟨rp, Hrp⟩ : ∃ rp, B.ns !! parent = some rp := by
        rcases Hpar with h | h
        · exact absurd h ‹_›
        · exact Option.isSome_iff_exists.1 h
      icases (BigSepM.bigSepM_insert_acc (M := GMap Loc) (Φ := fun l r => nodeOwn (GF := GF) W l r)
        (show Std.get? B.ns parent = some rp from Hrp)) $$ Hns with ⟨Hp, Hnsback⟩
      isimp only [nodeOwn] at Hp
      icases Hp with ⟨Hpn, Hpins, Hpcap, Hpents, Hpch, Hpchcap, Hpkey⟩
      try wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_apply wp_slice_append $$ [$Hpch $Hpchcap $Hsl] as %s' ⟨Hpch, Hpchcap, -⟩
      try wp_auto
      ispecialize Hnsback $$ %({ rp with nv := { rp.nv with children' := s' }, cs := rp.cs ++ [«$r0_ptr»] })
      ihave Hns := Hnsback $$ [Hpn Hpins Hpcap Hpents Hpch Hpchcap Hpkey]
      · unfold nodeOwn
        simp only
        iframe
      wp_if_destruct
      · obtain ⟨Hpm0, -, Hpgs, Hpeq, Hid, Hfl, Hlt⟩ := Hfile ‹_›
        try wp_auto
        rw [Htx]
        wp_apply hpage txl pmap pm dqp dqp W.dbl W.data (W64 (W.ps : Int)) (DFrac.own W.q) DFrac.discard pgid p dqr pg
          (Or.inr ⟨Hpm0, by rw [Hpeq, uZ_pid_ps _ _ HvOK.2.2.1 Hlt], HvOK.1,
            by rw [uZ_pid_ps _ _ HvOK.2.2.1 Hlt]; omega⟩) Hpc Hrd.1 Hid Hfl
          $$ [Hpf Hpm Hdb Hdata Hbytes] as ⟨Hpf, Hpm, Hdb, Hdata, -, Hbytes⟩
        · iframe
          iframe #
        try wp_auto
        wp_apply hread _ _ _ dqr pg Hpc Hrd $$ [$«$r0» Hbytes] as %s ⟨Hn, Hs, Hcap, Hbytes⟩
        · iframe
        try wp_auto
        wp_apply wp_mapInsert $$ Hnm as Hnm
        try wp_auto
        try simp only
        try rw [Htx]
        wp_apply hInc $$ [Hst] as %st' ⟨%Hst', Hst⟩
        · iframe
        try wp_auto
        icases ns_fresh W _ _ _ $$ Hns Hn with ⟨Hns, Hn, %Hfresh⟩
        have Hfresh0 : B.ns !! «$r0_ptr» = none := by
          by_cases he : parent = «$r0_ptr»
          · rw [he] at Hfresh; exact absurd Hfresh (by simp [Std.insert])
          · exact (GMap.lookup_insert_ne B.ns _ he).symm.trans Hfresh
        ihave Hback := Hback $$ Hbytes
        icases Hback with ⟨Hpv, Hpg⟩
        icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn'⟩
        ispecialize HΦ $$ %«$r0_ptr» %(nodeAdded B pgid parent «$r0_ptr» (readNRec bl parent p pg s src') s') %st'
        iapply HΦ
        isplitl [Hbv Hib Hnm Hbm Hpg Hns Hn Hs Hcap Hents Hkey]
        · simp only [nodeAdded, parentAdd, ‹¬parent = null›, Hrp, ↓reduceIte]
          try rw [Htx]
          iframe Hbv Hib Hnm Hbm
          isplitl [Hpg]
          · iapply pageOwn_congr_wand W _ _ (by rfl) (by rfl) (by rfl) $$ Hpg
          iapply (BigSepM.bigSepM_insert (M := GMap Loc) (Φ := fun l r => nodeOwn (GF := GF) W l r)
            (show Std.get? _ «$r0_ptr» = none from Hfresh)).2
          iframe Hns
          unfold nodeOwn readNRec readNodeV
          simp only
          iframe Hn Hs Hcap Hents
          isplitl []
          · iapply ownSlice_nil
          isplitl []
          · iapply ownSliceCap_nil
          by_cases hc : pageCount pg = 0
          · simp only [hc, ↓reduceIte]
            itrivial
          · isimp only [hc, ↓reduceIte] at Hkey
            simp only [hc, ↓reduceIte]
            split
            · itrivial
            · iexact Hkey
        iframe
        iframe #
        isplitr
        · ipureintro; exact Hlgv
        ipureintro
        unfold nodeRes
        right
        exact ⟨hk, Hfresh0, Hnn', by rw [Hst'], s, s', src', Hsrc'.1, Hsrc'.2, rfl⟩
      · obtain ⟨Hz, rfl, rfl, rfl, -, -⟩ := Hinl ‹_›
        subst Hz
        try wp_auto
        wp_apply hVerify _ iprop(pgId_ptr ↦ W64 0) $$ [pgId] as pgId
        · isplit
          · wp_auto
            iexact pgId
          · iexact pgId
        try wp_auto
        wp_apply hread _ _ _ dqr B.ipg Hpc Hrd $$ [$«$r0» Hbytes] as %s ⟨Hn, Hs, Hcap, Hbytes⟩
        · iframe
        try wp_auto
        wp_apply wp_mapInsert $$ Hnm as Hnm
        try wp_auto
        try simp only
        try rw [Htx]
        wp_apply hInc $$ [Hst] as %st' ⟨%Hst', Hst⟩
        · iframe
        try wp_auto
        icases ns_fresh W _ _ _ $$ Hns Hn with ⟨Hns, Hn, %Hfresh⟩
        have Hfresh0 : B.ns !! «$r0_ptr» = none := by
          by_cases he : parent = «$r0_ptr»
          · rw [he] at Hfresh; exact absurd Hfresh (by simp [Std.insert])
          · exact (GMap.lookup_insert_ne B.ns _ he).symm.trans Hfresh
        ihave Hback := Hback $$ Hbytes
        icases Hback with ⟨Hpv, Hpg⟩
        icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn'⟩
        ispecialize HΦ $$ %«$r0_ptr» %(nodeAdded B (W64 0) parent «$r0_ptr» (readNRec bl parent B.bv.page' B.ipg s src') s') %st'
        iapply HΦ
        isplitl [Hbv Hib Hnm Hbm Hpg Hns Hn Hs Hcap Hents Hkey]
        · simp only [nodeAdded, parentAdd, ‹¬parent = null›, Hrp, ↓reduceIte]
          try rw [Htx]
          iframe Hbv Hib Hnm Hbm
          isplitl [Hpg]
          · iapply pageOwn_congr_wand W _ _ (by rfl) (by rfl) (by rfl) $$ Hpg
          iapply (BigSepM.bigSepM_insert (M := GMap Loc) (Φ := fun l r => nodeOwn (GF := GF) W l r)
            (show Std.get? _ «$r0_ptr» = none from Hfresh)).2
          iframe Hns
          unfold nodeOwn readNRec readNodeV
          simp only
          iframe Hn Hs Hcap Hents
          isplitl []
          · iapply ownSlice_nil
          isplitl []
          · iapply ownSliceCap_nil
          by_cases hc : pageCount B.ipg = 0
          · simp only [hc, ↓reduceIte]
            itrivial
          · isimp only [hc, ↓reduceIte] at Hkey
            simp only [hc, ↓reduceIte]
            split
            · itrivial
            · iexact Hkey
        iframe
        iframe #
        isplitr
        · ipureintro; exact Hlgv
        ipureintro
        unfold nodeRes
        right
        exact ⟨hk, Hfresh0, Hnn', by rw [Hst'], s, s', src', Hsrc'.1, Hsrc'.2, rfl⟩

end proof

end bbolt
end EtcdGrove
end Perennial
