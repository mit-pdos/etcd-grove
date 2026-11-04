/-
The proof of `Spec/go_etcd_io/bbolt/Cursor__keyValue_w.lean` (U6d, `notes/bbolt-proof-plan.md`):
the top element is a live leaf node (its inode, whose slices' sources `wOwn` holds) or a leaf
page (its element, whose key and value are sub-slices of the page's bytes, `srcLoc_sub`).
-/
module

public import Spec.go_etcd_io.bbolt.Cursor__keyValue_w
public import Spec.go_etcd_io.bbolt.internal.common.Page__Count
public import Spec.go_etcd_io.bbolt.internal.common.Page__LeafPageElement
public import Spec.go_etcd_io.bbolt.internal.common.leafPageElement__Key
public import Spec.go_etcd_io.bbolt.internal.common.leafPageElement__Value
public import Spec.go_etcd_io.bbolt.internal.common.leafPageElement__Flags
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Key
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Value
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Flags
public import Proof.go_etcd_io.bbolt.Read.WSearch
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

theorem Cursor.keyValue_w.wp_proof
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG))
    (hLPE : internal.common.Page.LeafPageElement.spec (GF := GF) (hG := hG))
    (hK : internal.common.leafPageElement.Key.spec (GF := GF) (hG := hG))
    (hV : internal.common.leafPageElement.Value.spec (GF := GF) (hG := hG))
    (hF : internal.common.leafPageElement.Flags.spec (GF := GF) (hG := hG))
    (hIK : internal.common.Inode.Key.spec (GF := GF) (hG := hG))
    (hIV : internal.common.Inode.Value.spec (GF := GF) (hG := hG))
    (hIF : internal.common.Inode.Flags.spec (GF := GF) (hG := hG)) :
    Cursor.keyValue_w.spec (GF := GF) (hG := hG) := by
  intro K tx r m X bl B c stk els e pid ws hB hloc hpm hinl hpos hra hlt hi0
  wp_start as ⟨Hw, Hc, Hs⟩
  icases wtxW_pkgInit K tx r m X $$ Hw with ⟨Hw, #Hpkg⟩
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  ihave %Hmax := wtxW_page_maxMap K tx r m X $$ Hw
  obtain ⟨-, B0, hB0, hclean, hkeys, hpgl, hnsl, hvw⟩ := id hloc
  rw [hB] at hB0; cases hB0
  obtain ⟨B', hB', hm⟩ := hra
  rw [hB] at hB'; cases hB'
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  wp_auto
  have hidx : sint.Z (stk.len - W64 1) = (els.length : Int) := by
    simp only [List.length_append, List.length_singleton] at Hsl; word
  rw [if_pos (show 0 ≤ sint.Z (stk.len - W64 1) ∧ sint.Z (stk.len - W64 1) < sint.Z stk.len by
    rw [hidx]; word)]
  icases ownSlice_elem_acc (sint.Z (stk.len - W64 1)) e _ _ (els ++ [e]) (by omega)
    (by rw [hidx]; simp) $$ Hs with ⟨He, Hsback⟩
  rw [hidx]
  wp_auto
  wp_method_call; wp_call
  wp_auto
  cases hr : resolve B pid with
  | none =>
    simp only [hr] at hm
    obtain ⟨hnode, pg, hwp⟩ := hm
    have hpage : (resolve B pid = none ∧ B.ib.root' = W64 0 ∧ pid = W64 0) ∨
        (B.ib.root' ≠ W64 0 ∧ treeWF X.v.pages X.t.mv.pgid'.toNat pid.toNat ∧
          ∀ d, treeHas X.v.pages pid.toNat d → B.nm !! W64 (d : Int) = none) := by
      rcases hpos with ⟨l, rn, hres, -⟩ | h | h
      · rw [hr] at hres; cases hres
      · exact Or.inl h
      · exact Or.inr h
    obtain ⟨-, pa, pg', hw', h16, hsrc, hpa, -, hkind⟩ :=
      posOK_page_facts X bl B pid hB hloc hpm hinl Hmax hpage
    rw [hwp] at hw'
    simp only [Option.some.injEq, Prod.mk.injEq] at hw'
    obtain ⟨rfl, rfl⟩ := hw'
    rw [ltree_page X bl B pid _ pg hB hr hwp] at hlt
    simp only [Option.some.injEq, Prod.mk.injEq, decide_eq_true_eq] at hlt
    obtain ⟨hleaf, hws⟩ := hlt
    subst hws
    have hwf : leafWF pg pg.length := by
      rcases hkind with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · rw [hleaf] at h; cases h
    obtain ⟨-, hcnt, helems, -⟩ := hwf
    have hls : leafSrc X bl Src.view = pgSrc B := by
      unfold leafSrc; rw [hB]; simp only
      by_cases h0 : B.ib.root' = W64 0
      · have hrn : B.bv.rootNode' = null := by
          unfold resolve at hr; rw [if_pos h0] at hr
          by_cases h1 : B.bv.rootNode' = null
          · exact h1
          · rw [if_neg h1] at hr; cases hr
        rw [if_pos ⟨h0, hrn⟩, pgSrc_inl X bl B hB hinl h0 hrn]
      · rw [if_neg (fun h => h0 h.1)]; unfold pgSrc; rw [if_neg h0]
    icases wtxW_page_srcLoc K tx r m X bl B pid e.page' pg hB hloc.1 hwp hsrc hpa $$ Hw
      with ⟨Hw, #Hsrc⟩
    icases wtxW_cells_acc K tx r m X $$ Hw with ⟨%Hbase, Hcells, Hwb⟩
    icases Write.srcLoc_acc wq X.v e.page' (pgSrc B) pg $$ [Hcells] with ⟨%dq, Hp, Hpb⟩
    · iframe; iframe #
    icases Read.bytesPointsto_bounds e.page' dq pg (by intro h; simp [h] at h16) $$ Hp
      with ⟨Hp, %Hlb⟩
    icases bytesPointsto_view_read (V := Page) e.page' dq pg 0 e.page' (by simp) (by omega) Hlb.1
      $$ Hp with ⟨Hh, Hhb⟩
    rw [show (decode (List.take 16 (List.drop 0 pg)) : Page) = pageHdr pg from rfl]
    obtain ⟨hd, hH⟩ : ∃ hd, pageHdr pg = hd := ⟨_, rfl⟩
    have hcz : uint.Z hd.count' = (pageCount pg : Int) := by unfold pageCount; rw [hH]
    have hcnt16 : pageCount pg < 2 ^ 16 := by unfold pageCount; exact BitVec.isLt _
    rw [hH, hnode]
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
      rw [show (els ++ [e]).set (↑els.length : Int).toNat e = els ++ [e] by simp]
      iapply HΦ
      iframe
      unfold wKV
      rw [pageWs_get_none pg _ (by omega)]
      ipureintro; exact ⟨rfl, rfl, rfl⟩
    have hne : W64 (uint.Z hd.count') ≠ W64 0 := by
      rw [hcz]; intro h; apply hc0; have := congrArg BitVec.toNat h; simp at this; omega
    rw [decide_eq_false hne]
    wp_auto
    wp_method_call; wp_call
    wp_auto
    rw [hnode]
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
      rw [show (els ++ [e]).set (↑els.length : Int).toNat e = els ++ [e] by simp]
      iapply HΦ
      iframe
      unfold wKV
      rw [pageWs_get_none pg _ (by omega)]
      ipureintro; exact ⟨rfl, rfl, rfl⟩
    rw [decide_eq_false hge]
    wp_auto
    rw [hnode]
    wp_auto
    ihave Hp := Hhb $$ Hh
    obtain ⟨i, hi⟩ : ∃ i : Nat, sint.Z e.index' = (i : Int) := ⟨(sint.Z e.index').toNat, by omega⟩
    have hic : i < pageCount pg := by omega
    have hu : uint.Z (W16 (sint.Z e.index')) = (i : Int) := by rw [hi]; word
    wp_apply hLPE e.page' (W16 (sint.Z e.index')) Hlb.1
      (by rw [hu]; unfold elemOff at hcnt; omega)
    rw [hu]
    have hoff : (16 + 16 * (i : Int)) = ((elemOff i : Nat) : Int) := by unfold elemOff; push_cast; rfl
    rw [hoff]
    obtain ⟨he1, he2⟩ := helems i hic
    icases bytesPointsto_view_read (V := leafPageElement) e.page' dq pg (elemOff i)
      (e.page' +ₗ ((elemOff i : Nat) : Int)) rfl (by unfold elemOff at hcnt ⊢; omega) Hlb.1
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
    ihave #Hks := Write.srcLoc_sub X.v e.page' (pgSrc B) pg (elemOff i + leafPos pg i)
      (leafKsize pg i) (pgSrc_ne_stale B) (by omega) hk32 Hlb.1 Hlb.2 $$ Hsrc
    ihave #Hvs := Write.srcLoc_sub X.v e.page' (pgSrc B) pg (elemOff i + leafPos pg i + leafKsize pg i)
      (leafVsize pg i) (pgSrc_ne_stale B) (by omega) hv32 Hlb.1 Hlb.2 $$ Hsrc
    ihave Hs := Hsback $$ He
    rw [show (els ++ [e]).set (↑els.length : Int).toNat e = els ++ [e] by simp]
    have hkloc : (e.page' +ₗ ((elemOff i : Nat) : Int)) +ₗ uint.Z le.pos' =
        e.page' +ₗ ((elemOff i + leafPos pg i : Nat) : Int) := by
      rw [loc_add_assoc, hpos]; push_cast; rfl
    have hvloc : (e.page' +ₗ ((elemOff i : Nat) : Int)) +ₗ (uint.Z le.pos' + uint.Z le.ksize') =
        e.page' +ₗ ((elemOff i + leafPos pg i + leafKsize pg i : Nat) : Int) := by
      rw [loc_add_assoc, hpos, hks]; push_cast; rw [Int.add_assoc]
    rw [hkloc, hvloc, hks, hvs]
    iapply HΦ
    iframe
    unfold wKV
    rw [hi, Int.toNat_natCast, pageWs_get pg i hic]
    have hpw : pageW pg i = ⟨W32 (leafFlags pg i : Int), W64 0, leafKey pg i, leafValue pg i,
        Src.view, Src.view⟩ := by simp [pageW, hleaf]
    rw [hpw]
    simp only
    rw [hls]
    isplitr
    · ipureintro
      refine ⟨?_, ?_⟩
      · intro h
        injection h with h1
        have := congrArg Loc.addr h1
        simp [Loc.add, null] at this
        omega
      · unfold leafFlags; rw [hle]; exact (Write.w32_ofNat_toNat _).symm
    rw [show leafKey pg i = bytesAt pg (elemOff i + leafPos pg i) (leafKsize pg i) from rfl,
      show leafValue pg i = bytesAt pg (elemOff i + leafPos pg i + leafKsize pg i) (leafVsize pg i)
        from rfl]
    isimp only [bslice] at Hks Hvs
    isplitl
    · iexact Hks
    · iexact Hvs
  | some l =>
    simp only [hr] at hm
    obtain ⟨rn, hrn⟩ : ∃ rn, B.ns !! l = some rn := by
      rcases hpos with ⟨l', rn, hres, hrn⟩ | ⟨hres, -⟩ | ⟨h0, ht, hnm⟩
      · rw [hr] at hres; cases hres; exact ⟨rn, hrn⟩
      · rw [hr] at hres; cases hres
      · have := (posOK_tree_page X B pid h0 ht hnm).1; rw [hr] at this; cases this
    rw [ltree_node X bl B pid l rn hB hr hrn] at hlt
    simp only [Option.some.injEq, Prod.mk.injEq] at hlt
    obtain ⟨hleaf, hws⟩ := hlt
    subst hws
    have hnmnn := bktLocalOK_nm_nonnull X bl B hloc hB
    have hnn0 : l ≠ null := by
      by_cases h0 : B.ib.root' = W64 0
      · unfold resolve at hr; rw [if_pos h0] at hr
        by_cases h1 : B.bv.rootNode' = null
        · rw [if_pos h1] at hr; cases hr
        · rw [if_neg h1] at hr; cases hr; exact h1
      · rw [resolve_tree B pid h0] at hr; exact hnmnn _ _ hr
    have hls : ∀ s, leafSrc X bl s = s := by
      intro s
      unfold leafSrc; rw [hB]; simp only
      rw [if_neg]
      rintro ⟨h0, h1⟩
      unfold resolve at hr; rw [if_pos h0, if_pos h1] at hr; cases hr
    have hlv := hnsl l rn hrn
    have hnc := hclean.2.2.2.2.2.2.2.1 l rn hrn
    icases wtxW_node_cells_acc K tx r m X bl B l rn hB hrn hlv $$ Hw with ⟨%Hbase, Ho, Hcells, Hwb⟩
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
    -- the closing of the node, the cells and the stack
    ihave Hclose : (∀ (k vl : GoSlice) (fl : w32),
        sliceIndexRef elemRef (els.length : Int) stk ↦ e -∗
        l.[node, go!"inodes"] ↦ rn.nv.inodes' -∗ rn.nv.inodes' ↦* rn.ins -∗
        ([∗list] it;w ∈ rn.ins;rn.ws, wOwn X.v true it w) -∗
        wKV X bl rn.ws (sint.Z e.index').toNat k vl fl -∗
        Φ (PairV (PairV #k #vl) #fl)) $$ [HΦ Hc Hsback Hcells Hwb Hcapn Hch Hchcap Hnk
        bucket isLeaf unbalanced spilled key pgid parent children]
    · iintro %k %vl %fl He inodes Hins Hws Hkv
      ihave Hn : (l ↦ rn.nv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
      · iapply typedPointsto_combine _ _ _ Hnn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      ihave Ho : objOwn X.v l (DFrac.own 1) true (.node bl rn) $$ [Hn Hins Hcapn Hws Hch Hchcap Hnk]
      · simp only [objOwn]; iframe
      ihave Hw := Hwb $$ Ho Hcells
      ihave Hs := Hsback $$ He
      rw [show (els ++ [e]).set (↑els.length : Int).toNat e = els ++ [e] by simp]
      iapply HΦ
      iframe
    by_cases hc0 : rn.ws.length = 0
    · rw [decide_eq_true (show rn.nv.inodes'.len = W64 0 by
        apply BitVec.eq_of_toNat_eq; have := Hinl.1; rw [Hwl, hc0] at this; simp [sint.nat] at this ⊢; word)]
      wp_auto
      iapply Hclose $$ He inodes Hins Hws
      unfold wKV
      rw [List.getElem?_eq_none (by omega)]
      ipureintro; exact ⟨rfl, rfl, rfl⟩
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
      unfold wKV
      rw [List.getElem?_eq_none (by omega)]
      ipureintro; exact ⟨rfl, rfl, rfl⟩
    rw [decide_eq_false hge]
    wp_auto
    rw [hm, decide_eq_false hnn0]
    wp_auto
    rw [hm]
    wp_auto
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
    have hk0 : 0 < w.key.length := hnc.2.2.2.2.1 w hwm
    ihave %Hkl := srcOwn_len_r X.v it.key' w.ks w.key hwks $$ Hik
    iapply Hclose $$ He inodes Hins Hws
    unfold wKV
    rw [Hw_lookup]
    simp only
    rw [hls, hls]
    isplitr
    · ipureintro
      refine ⟨?_, Hfp.1⟩
      intro h
      rw [h] at Hkl
      have : sint.nat slice.nil.len = 0 := rfl
      rw [this] at Hkl
      omega
    iframe; iframe #

end proof

end bbolt
end EtcdGrove
end Perennial
