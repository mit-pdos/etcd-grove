/-
The proof of `Spec/go_etcd_io/bbolt/Cursor__keyValue_ws.lean` (U6z/U6aa, `notes/bbolt-proof-plan.md`,
"Writer reads at a fraction"): as `Cursor.keyValue_w`'s proof (its callees: `Page.Count`,
`LeafPageElement`, the leaf element's and inode's `Key`/`Value`/`Flags`), but the top reference is
read through the cursor relation: a node reference is the bucket's current leaf node of its
position (`WBridge.wStk_top`, by the registry fragments' agreement `wtxWQ_nodeLoc_agree`), a page
reference (possibly stale) reads `sLeafOK`'s page at `pageLoc` (a view page) or the inline root
page (`wInlOwn`, the stack then the root alone: `WKVs.sPathR_pid0`); the entry at the leaf index is
the bucket's at the stack's position (`WKVs.stackPos_get`).
-/
module

public import Spec.go_etcd_io.bbolt.Cursor__keyValue_ws
public import Spec.go_etcd_io.bbolt.internal.common.Page__Count
public import Spec.go_etcd_io.bbolt.internal.common.Page__LeafPageElement
public import Spec.go_etcd_io.bbolt.internal.common.leafPageElement__Key
public import Spec.go_etcd_io.bbolt.internal.common.leafPageElement__Value
public import Spec.go_etcd_io.bbolt.internal.common.leafPageElement__Flags
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Key
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Value
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Flags
public import Proof.go_etcd_io.bbolt.Read.WStkTop
public import Proof.go_etcd_io.bbolt.Read.WKVsPure
public import Proof.go_etcd_io.bbolt.Read.WSearch
public import Proof.go_etcd_io.bbolt.Read.WQ
public import Proof.go_etcd_io.bbolt.Read.Open
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout

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

theorem Cursor.keyValue_ws.wp_proofQ
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG))
    (hLPE : internal.common.Page.LeafPageElement.spec (GF := GF) (hG := hG))
    (hK : internal.common.leafPageElement.Key.spec (GF := GF) (hG := hG))
    (hV : internal.common.leafPageElement.Value.spec (GF := GF) (hG := hG))
    (hF : internal.common.leafPageElement.Flags.spec (GF := GF) (hG := hG))
    (hIK : internal.common.Inode.Key.spec (GF := GF) (hG := hG))
    (hIV : internal.common.Inode.Value.spec (GF := GF) (hG := hG))
    (hIF : internal.common.Inode.Flags.spec (GF := GF) (hG := hG)) :
    Cursor.keyValue_ws.specQ (GF := GF) (hG := hG) := by
  intro K tx r m q X n bl rt ipg nl c stk els pids hc hp hlo hix
  have hok := hc.1
  have hvw : viewWF X.v := hok.2.2.2.2.2.2.2
  obtain ⟨B, hB⟩ := PubW.bktLoc_rec X hok n bl hc.2.1
  obtain ⟨els0, e, rfl⟩ : ∃ els0 e, els = els0 ++ [e] := by
    rcases List.eq_nil_or_concat els with h | ⟨L, b, h⟩
    · exact absurd h hp.1
    · exact ⟨L, b, by simpa using h⟩
  have hpl : pids.length = els0.length + 1 := by have := hp.2.1; simpa using this
  obtain ⟨pid, hpid⟩ : ∃ pid, pids.getLast? = some pid := by
    cases h : pids.getLast? with
    | none => rw [List.getLast?_eq_none_iff] at h; subst h; simp at hpl
    | some p => exact ⟨p, rfl⟩
  have he : (els0 ++ [e]).getLast? = some e := by simp
  have hix' : e.index'.toNat ≤ leafCnt X.v (wEs X n) pids (els0 ++ [e]) ∨
      e.index' = W64 (leafCnt X.v (wEs X n) pids (els0 ++ [e]) : Int) ∨
      (leafCnt X.v (wEs X n) pids (els0 ++ [e]) = 0 ∧ e.index' = W64 (-1)) := by
    rcases hix with h | h | ⟨h0, e', he', h1⟩
    · exact WKVs.leafIdx_cases X.v (wEs X n) pids els0 e (Or.inl h)
    · exact WKVs.leafIdx_cases X.v (wEs X n) pids els0 e (Or.inr h)
    · simp at he'; subst he'; exact Or.inr (Or.inr ⟨h0, h1⟩)
  obtain ⟨idx, hidx⟩ : ∃ idx, idx = (if leafIdx (els0 ++ [e]) < leafCnt X.v (wEs X n) pids (els0 ++ [e])
      then stackPos X.v (wEs X n) pids (els0 ++ [e]) else (wEs X n).length) := ⟨_, rfl⟩
  rw [← hidx]
  have hget : ∀ i, e.index'.toNat = i → i < leafCnt X.v (wEs X n) pids (els0 ++ [e]) →
      (wEs X n)[idx]? = (entsIn (wEs X n) (pathBnd X.v pids (els0 ++ [e])))[i]? := by
    intro i hi hlt
    rw [hidx, if_pos (by rw [WKVs.leafIdx_append]; omega)]
    unfold wEs
    rw [WKVs.stackPos_get _ _ _ _ (by rw [WKVs.leafIdx_append]; unfold wEs at hlt; omega),
      WKVs.leafIdx_append, hi]
  have hnone : ¬ e.index'.toNat < leafCnt X.v (wEs X n) pids (els0 ++ [e]) → (wEs X n)[idx]? = none := by
    intro h
    rw [hidx, if_neg (by rw [WKVs.leafIdx_append]; exact h)]
    simp
  wp_start as ⟨Hw, Hc, Hs, #Hown⟩
  unfold wStkOwn
  icases Hown with ⟨#Hnls, #Hinl⟩
  icases WBridge.wtxWQ_nodeLoc_agree K tx r m q X nl (els0 ++ [e]) $$ [Hw] with ⟨Hw, %Hag⟩
  · iframe; iframe #
  icases wtxWQ_pkgInit K tx r m q X $$ Hw with ⟨Hw, #Hpkg⟩
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  icases wtxWQ_cells_acc K tx r m q X $$ Hw with ⟨%Hbase0, Hcells0, Hwb0⟩
  ihave Hw := Hwb0 $$ Hcells0
  obtain ⟨ws, hL, hents, hcnt, hplain, hnode⟩ :=
    WBridge.wStk_top X n bl rt B hc hB Hbase0 nl _ pids hp Hag e pid he hpid
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  wp_auto
  have hidx' : sint.Z (stk.len - W64 1) = (els0.length : Int) := by
    simp only [List.length_append, List.length_singleton] at Hsl; word
  rw [if_pos (show 0 ≤ sint.Z (stk.len - W64 1) ∧ sint.Z (stk.len - W64 1) < sint.Z stk.len by
    rw [hidx']; word)]
  icases ownSlice_elem_acc (sint.Z (stk.len - W64 1)) e _ _ (els0 ++ [e]) (by omega)
    (by rw [hidx']; simp) $$ Hs with ⟨He, Hsback⟩
  rw [hidx']
  wp_auto
  wp_method_call; wp_call
  wp_auto
  by_cases hnn : e.node' = null
  · -- a page reference (possibly stale)
    obtain ⟨pg, hpg, hplainp, hpe, hinlg⟩ := hlo e pid he hpid hnn
    have hcnt' : leafCnt X.v (wEs X n) pids (els0 ++ [e]) = pageCount pg := by
      unfold leafCnt; rw [← hpe]; simp [pgEnts, pageWs]
    rw [hcnt'] at hix'
    obtain ⟨hleaf, hwf, h16⟩ : pageFlags pg = leafPageFlag ∧ leafWF pg pg.length ∧ 16 ≤ pg.length := by
      by_cases hp0 : pid = 0
      · obtain ⟨g1, g2, g3, g4, -⟩ := hinlg hp0
        exact ⟨g2, g3, g4⟩
      · unfold leafPgAt at hpg; rw [if_neg hp0] at hpg
        have hj := hp.2.2.2 els0.length e pid (by simp)
          (by rw [show els0.length = pids.length - 1 by omega, ← List.getLast?_eq_getElem?]; exact hpid)
        have hlf : pageFlags pg = leafPageFlag := by
          rcases hj.2.2.2 (by simp) with h | ⟨pg', hpg', hf⟩
          · exact absurd h hp0
          · rw [hpg] at hpg'; cases hpg'; exact hf
        have := (Read.viewWF_page X.v hvw pid pg hpg).2.2.1
        exact ⟨hlf, WKVs.viewWF_leafWF X.v hvw pid pg hpg hlf, by omega⟩
    ihave #Hsrc0 : ∃ src, ⌜src ≠ Src.stale⌝ ∗ srcLoc X.v e.page' src pg $$ []
    · by_cases hp0 : pid = 0
      · subst hp0
        obtain ⟨rfl, -, rfl⟩ := WKVs.sPathR_pid0 nl X.v hvw bl rt els0 e pids hp hpid
        unfold leafPgAt at hpg; simp only [↓reduceIte, Option.some.injEq] at hpg
        subst hpg
        isimp only [List.nil_append] at Hinl
        iapply WKVs.wInlOwn_src X.v ipg e hnn
        iexact Hinl
      · unfold leafPgAt at hpg; rw [if_neg hp0] at hpg
        have hj := hp.2.2.2 els0.length e pid (by simp)
          (by rw [show els0.length = pids.length - 1 by omega, ← List.getLast?_eq_getElem?]; exact hpid)
        rw [(hj.2.1 hnn).2 hp0]
        iexists Src.view
        isplitr
        · ipureintro; intro h; cases h
        · iapply srcLoc_view_page X.v pid pg hpg
    icases Hsrc0 with ⟨%src, %hsrcS, #Hsrc⟩
    icases wtxWQ_cells_acc K tx r m q X $$ Hw with ⟨%Hbase, Hcells, Hwb⟩
    icases Write.srcLoc_acc (QpMul q wq) X.v e.page' src pg $$ [Hcells] with ⟨%dq, Hp, Hpb⟩
    · iframe; iframe #
    icases Read.bytesPointsto_bounds e.page' dq pg (by intro h; simp [h] at h16) $$ Hp
      with ⟨Hp, %Hlb⟩
    icases bytesPointsto_view_read (V := Page) e.page' dq pg 0 e.page' (by simp) (by omega) Hlb.1
      $$ Hp with ⟨Hh, Hhb⟩
    rw [show (decode (List.take 16 (List.drop 0 pg)) : Page) = pageHdr pg from rfl]
    obtain ⟨hd, hH⟩ : ∃ hd, pageHdr pg = hd := ⟨_, rfl⟩
    have hcz : uint.Z hd.count' = (pageCount pg : Int) := by unfold pageCount; rw [hH]
    have hcnt16 : pageCount pg < 2 ^ 16 := by unfold pageCount; exact BitVec.isLt _
    obtain ⟨-, hcntb, helems, -⟩ := hwf
    rw [hH, hnn]
    wp_auto
    wp_apply hCnt e.page' hd dq $$ [Hh] as Hh
    · iexact Hh
    by_cases hc0 : pageCount pg = 0
    · have : W64 (uint.Z hd.count') = W64 0 := by rw [hcz, hc0]; rfl
      rw [this]
      wp_auto
      ihave Hp := Hhb $$ Hh
      ihave Hcells := Hpb $$ Hp
      ihave Hw := Hwb $$ Hcells
      ihave Hs := Hsback $$ He
      rw [show (els0 ++ [e]).set (↑els0.length : Int).toNat e = els0 ++ [e] by simp]
      iapply HΦ
      iframe
      unfold wEntKV
      rw [hnone (by rw [hcnt', hc0]; omega)]
      ipureintro; exact ⟨rfl, rfl, rfl⟩
    obtain ⟨hile, hsz⟩ := WKVs.leafIdx_sint e (pageCount pg) (by omega) hc0 hix'
    have hne : W64 (uint.Z hd.count') ≠ W64 0 := by
      rw [hcz]; intro h; apply hc0; have := congrArg BitVec.toNat h; simp at this; omega
    rw [decide_eq_false hne]
    wp_auto
    wp_method_call; wp_call
    wp_auto
    rw [hnn]
    wp_auto
    wp_apply hCnt e.page' hd dq $$ [Hh] as Hh
    · iexact Hh
    have hcn : sint.Z (W64 (uint.Z hd.count')) = (pageCount pg : Int) := by rw [hcz]; word
    rw [hcn]
    by_cases hge : (pageCount pg : Int) ≤ sint.Z e.index'
    · rw [decide_eq_true hge]
      wp_auto
      ihave Hp := Hhb $$ Hh
      ihave Hcells := Hpb $$ Hp
      ihave Hw := Hwb $$ Hcells
      ihave Hs := Hsback $$ He
      rw [show (els0 ++ [e]).set (↑els0.length : Int).toNat e = els0 ++ [e] by simp]
      iapply HΦ
      iframe
      unfold wEntKV
      rw [hnone (by rw [hcnt']; omega)]
      ipureintro; exact ⟨rfl, rfl, rfl⟩
    rw [decide_eq_false hge]
    wp_auto
    rw [hnn]
    wp_auto
    ihave Hp := Hhb $$ Hh
    obtain ⟨i, hi⟩ : ∃ i : Nat, sint.Z e.index' = (i : Int) := ⟨(sint.Z e.index').toNat, by omega⟩
    have hic : i < pageCount pg := by omega
    have hiN : e.index'.toNat = i := by omega
    have hu : uint.Z (W16 (sint.Z e.index')) = (i : Int) := by rw [hi]; word
    wp_apply hLPE e.page' (W16 (sint.Z e.index')) Hlb.1
      (by rw [hu]; unfold elemOff at hcntb; omega)
    rw [hu]
    have hoff : (16 + 16 * (i : Int)) = ((elemOff i : Nat) : Int) := by unfold elemOff; push_cast; rfl
    rw [hoff]
    obtain ⟨he1, he2⟩ := helems i hic
    icases bytesPointsto_view_read (V := leafPageElement) e.page' dq pg (elemOff i)
      (e.page' +ₗ ((elemOff i : Nat) : Int)) rfl (by unfold elemOff at hcntb ⊢; omega) Hlb.1
      $$ Hp with ⟨Hel, Helb⟩
    rw [show (decode (List.take 16 (List.drop (elemOff i) pg)) : leafPageElement) =
      leafElem pg i from rfl]
    obtain ⟨le, hle⟩ : ∃ le, leafElem pg i = le := ⟨_, rfl⟩
    have hpos : uint.Z le.pos' = (leafPos pg i : Int) := by unfold leafPos; rw [hle]
    have hks : uint.Z le.ksize' = (leafKsize pg i : Int) := by unfold leafKsize; rw [hle]
    have hvs : uint.Z le.vsize' = (leafVsize pg i : Int) := by unfold leafVsize; rw [hle]
    rw [hle]
    have hea : 0 < (e.page' +ₗ ((elemOff i : Nat) : Int)).addr := by simp [Loc.add]; omega
    wp_apply hK (e.page' +ₗ ((elemOff i : Nat) : Int)) le dq hea
      (by simp only [Loc.add]; rw [hpos, hks]; omega) $$ [Hel] as Hel
    · iexact Hel
    try wp_auto
    wp_apply hV (e.page' +ₗ ((elemOff i : Nat) : Int)) le dq hea
      (by simp only [Loc.add]; rw [hpos, hks, hvs]; omega) $$ [Hel] as Hel
    · iexact Hel
    try wp_auto
    wp_apply hF (e.page' +ₗ ((elemOff i : Nat) : Int)) le dq $$ [Hel] as Hel
    · iexact Hel
    try wp_auto
    ihave Hp := Helb $$ Hel
    ihave Hcells := Hpb $$ Hp
    ihave Hw := Hwb $$ Hcells
    have hk32 : leafKsize pg i < 2 ^ 32 := by unfold leafKsize; exact BitVec.isLt _
    have hv32 : leafVsize pg i < 2 ^ 32 := by unfold leafVsize; exact BitVec.isLt _
    ihave #Hks := Write.srcLoc_sub X.v e.page' src pg (elemOff i + leafPos pg i)
      (leafKsize pg i) hsrcS (by omega) hk32 Hlb.1 Hlb.2 $$ Hsrc
    ihave #Hvs := Write.srcLoc_sub X.v e.page' src pg (elemOff i + leafPos pg i + leafKsize pg i)
      (leafVsize pg i) hsrcS (by omega) hv32 Hlb.1 Hlb.2 $$ Hsrc
    ihave #Hks2 := WKVs.srcOwn_ent X.v _ src _ hsrcS $$ Hks
    ihave #Hvs2 := WKVs.srcOwn_ent X.v _ src _ hsrcS $$ Hvs
    ihave Hs := Hsback $$ He
    rw [show (els0 ++ [e]).set (↑els0.length : Int).toNat e = els0 ++ [e] by simp]
    have hkloc : (e.page' +ₗ ((elemOff i : Nat) : Int)) +ₗ uint.Z le.pos' =
        e.page' +ₗ ((elemOff i + leafPos pg i : Nat) : Int) := by
      rw [loc_add_assoc, hpos]; push_cast; rfl
    have hvloc : (e.page' +ₗ ((elemOff i : Nat) : Int)) +ₗ (uint.Z le.pos' + uint.Z le.ksize') =
        e.page' +ₗ ((elemOff i + leafPos pg i + leafKsize pg i : Nat) : Int) := by
      rw [loc_add_assoc, hpos, hks]; push_cast; rw [Int.add_assoc]
    rw [hkloc, hvloc, hks, hvs]
    iapply HΦ
    iframe
    unfold wEntKV
    have hent : (entsIn (wEs X n) (pathBnd X.v pids (els0 ++ [e])))[i]? =
        some (leafKey pg i, leafValue pg i) := by
      rw [← hpe]; unfold pgEnts
      rw [List.getElem?_map, pageWs_get pg i hic]
      simp [pageW, hleaf]
    rw [hget i hiN (by rw [hcnt']; exact hic), hent]
    simp only
    have hfl : le.flags' = W32 (leafFlags pg i : Int) := by
      unfold leafFlags; rw [hle]; exact (Write.w32_ofNat_toNat _).symm
    have hpl : ¬ isBktFlag (W32 (leafFlags pg i : Int)) := by
      have := hplainp (pageW pg i) (by
        unfold pageWs; exact List.mem_map.2 ⟨i, List.mem_range.2 hic, rfl⟩)
      simpa [pageW, hleaf] using this
    isplitr
    · ipureintro
      refine ⟨?_, ?_⟩
      · intro h
        injection h with h1
        have := congrArg Loc.addr h1
        simp [Loc.add, null] at this
        omega
      · rw [hfl]; exact hpl
    rw [show leafKey pg i = bytesAt pg (elemOff i + leafPos pg i) (leafKsize pg i) from rfl,
      show leafValue pg i = bytesAt pg (elemOff i + leafPos pg i + leafKsize pg i) (leafVsize pg i)
        from rfl]
    isimp only [bslice] at Hks2 Hvs2
    isplitl
    · iexact Hks2
    · iexact Hvs2
  · -- a node reference: the bucket's current leaf node there
    obtain ⟨hres, rn, hrn, hrws, hleaf⟩ := hnode hnn
    subst hrws
    obtain ⟨-, B0, hB0, hclean, -, -, hnsl, -⟩ := PubW.bktLocalOK_of_wOK X hok bl B hB
    rw [hB] at hB0; cases hB0
    obtain ⟨l, hm⟩ : ∃ l, e.node' = l := ⟨_, rfl⟩
    rw [hm] at hrn hnn
    have hnn0 := hnn
    have hlv := hnsl l rn hrn
    have hnc := hclean.2.2.2.2.2.2.2.1 l rn hrn
    icases wtxWQ_node_len K tx r m q X bl B l rn hB hrn hlv $$ Hw with ⟨Hw, %H63⟩
    icases wtxWQ_node_cells_acc K tx r m q X bl B l rn hB hrn hlv $$ Hw with ⟨%Hbase, Ho, Hcells, Hwb⟩
    isimp only [objOwn] at Ho
    icases Ho with ⟨Hn, Hins, Hcapn, Hws, Hch, Hchcap, Hnk⟩
    ihave %Hinl := ownSlice_len _ _ _ $$ Hins
    ihave %Hwl := BigSepL2.bigSepL2_length $$ Hws
    icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn⟩
    iStructNamed Hn
    rw [hm, decide_eq_false hnn0]
    wp_auto
    rw [hm]
    wp_auto
    have Hlen : sint.Z rn.nv.inodes'.len = (rn.ws.length : Int) := by word
    ihave Hclose : (∀ (k vl : GoSlice) (fl : w32),
        sliceIndexRef elemRef (els0.length : Int) stk ↦ e -∗
        l.[node, go!"inodes"] ↦{DFrac.own q} rn.nv.inodes' -∗ rn.nv.inodes' ↦*{DFrac.own q} rn.ins -∗
        ([∗list] it;w ∈ rn.ins;rn.ws, wOwn X.v true it w) -∗
        wEntKV X.v (wEs X n) idx k vl fl -∗
        Φ (PairV (PairV #k #vl) #fl)) $$ [HΦ Hc Hsback Hcells Hwb Hcapn Hch Hchcap Hnk
        bucket isLeaf unbalanced spilled key pgid parent children]
    · iintro %k %vl %fl He inodes Hins Hws Hkv
      ihave Hn : (l ↦{DFrac.own q} rn.nv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
      · iapply typedPointsto_combine _ _ _ Hnn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      ihave Ho : objOwn X.v l (DFrac.own q) true (.node bl rn) $$ [Hn Hins Hcapn Hws Hch Hchcap Hnk]
      · simp only [objOwn]; iframe
      ihave Hw := Hwb $$ Ho Hcells
      ihave Hs := Hsback $$ He
      rw [show (els0 ++ [e]).set (↑els0.length : Int).toNat e = els0 ++ [e] by simp]
      iapply HΦ
      iframe
    by_cases hc0 : rn.ws.length = 0
    · rw [decide_eq_true (show rn.nv.inodes'.len = W64 0 by
        apply BitVec.eq_of_toNat_eq; have := Hinl.1; rw [Hwl, hc0] at this; simp [sint.nat] at this ⊢; word)]
      wp_auto
      iapply Hclose $$ He inodes Hins Hws
      unfold wEntKV
      rw [hnone (by rw [← hcnt, hc0]; omega)]
      ipureintro; exact ⟨rfl, rfl, rfl⟩
    rw [hcnt] at hc0 H63
    obtain ⟨hile, hsz⟩ := WKVs.leafIdx_sint e _ H63 hc0 hix'
    rw [← hcnt] at hc0 H63 hile
    rw [decide_eq_false (show ¬ rn.nv.inodes'.len = W64 0 by
      intro h; rw [h] at Hlen; simp at Hlen; omega)]
    wp_auto
    wp_method_call; wp_call
    wp_auto
    rw [hm, decide_eq_false hnn0]
    wp_auto
    rw [hm]
    wp_auto
    rw [Hlen]
    by_cases hge : (rn.ws.length : Int) ≤ sint.Z e.index'
    · rw [decide_eq_true hge]
      wp_auto
      iapply Hclose $$ He inodes Hins Hws
      unfold wEntKV
      rw [hnone (by rw [← hcnt]; omega)]
      ipureintro; exact ⟨rfl, rfl, rfl⟩
    rw [decide_eq_false hge]
    wp_auto
    rw [hm, decide_eq_false hnn0]
    wp_auto
    rw [hm]
    wp_auto
    have hi0 : 0 ≤ sint.Z e.index' := by omega
    rw [if_pos (show 0 ≤ sint.Z e.index' ∧ sint.Z e.index' < sint.Z rn.nv.inodes'.len by
      rw [Hlen]; omega)]
    list_elem rn.ins (sint.Z e.index').toNat as it
    list_elem rn.ws (sint.Z e.index').toNat as w
    icases ownSlice_elem_acc (sint.Z e.index') it _ _ rn.ins hi0 Hit_lookup $$ Hins with ⟨Hit, Hsb⟩
    wp_auto
    wp_apply hIK $$ [$Hit] as Hit
    try wp_auto
    wp_apply hIV $$ [$Hit] as Hit
    try wp_auto
    wp_apply hIF $$ [$Hit] as Hit
    try wp_auto
    icases BigSepL2.bigSepL2_lookup_acc Hit_lookup Hw_lookup $$ Hws with ⟨Hw1, Hwsback⟩
    isimp only [wOwn, ↓reduceIte] at Hw1
    icases Hw1 with ⟨%Hfp, #Hik, #Hiv⟩
    ihave Hws := Hwsback $$ [Hik Hiv]
    · isimp only [wOwn, ↓reduceIte]; iframe; iframe #; ipureintro; exact Hfp
    ihave Hins := Hsb $$ Hit
    rw [list_set_lookup_self _ _ _ Hit_lookup]
    have hwm : w ∈ rn.ws := List.mem_of_getElem? Hw_lookup
    have hwks : w.ks ≠ Src.stale := (hnc.2.2.2.2.2.1 w hwm).1
    have hwvs : w.vs ≠ Src.stale := (hnc.2.2.2.2.2.1 w hwm).2
    have hk0 : 0 < w.key.length := hnc.2.2.2.2.1 w hwm
    ihave %Hkl := srcOwn_len_r X.v it.key' w.ks w.key hwks $$ Hik
    ihave #Hik2 := WKVs.srcOwn_ent X.v _ _ _ hwks $$ Hik
    ihave #Hiv2 := WKVs.srcOwn_ent X.v _ _ _ hwvs $$ Hiv
    iapply Hclose $$ He inodes Hins Hws
    unfold wEntKV
    have hiN : e.index'.toNat = (sint.Z e.index').toNat := by omega
    have hent : (entsIn (wEs X n) (pathBnd X.v pids (els0 ++ [e])))[(sint.Z e.index').toNat]? =
        some (w.key, w.value) := by
      rw [← hents, List.getElem?_map, Hw_lookup]; rfl
    rw [hget _ hiN (by rw [← hcnt]; omega), hent]
    simp only
    isplitr
    · ipureintro
      refine ⟨?_, ?_⟩
      · intro h
        rw [h] at Hkl
        have : sint.nat slice.nil.len = 0 := rfl
        rw [this] at Hkl
        omega
      · rw [Hfp.1]; exact hplain w hwm
    iframe; iframe #

end proof

end bbolt
end EtcdGrove
end Perennial
