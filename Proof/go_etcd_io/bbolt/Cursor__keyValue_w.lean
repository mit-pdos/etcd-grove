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
    sorry

end proof

end bbolt
end EtcdGrove
end Perennial
