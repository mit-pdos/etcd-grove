/-
The proof of `Spec/go_etcd_io/bbolt/Cursor__Last.lean` (U6h, `notes/bbolt-proof-plan.md`).
A reader (`wp_reader`): the root's reference at its last index, `last` (`Cursor.last_r`) down to
the bucket's last entry, or the empty root leaf at index `-1` (`rEmptyAt`); the loop over
trailing empty leaves never runs (a reader's leaves below a branch are not empty, `rKeysAt`), and
`keyValue` (`Cursor.keyValue_r`, `Cursor.keyValue_r0` on the empty root leaf). A writer
(`wp_writer`): U6w's.
-/
module

public import Spec.go_etcd_io.bbolt.Cursor__Last
public import Spec.go_etcd_io.bbolt.Cursor__last_r
public import Spec.go_etcd_io.bbolt.Cursor__keyValue_r
public import Spec.go_etcd_io.bbolt.Cursor__keyValue_r0
public import Spec.go_etcd_io.bbolt.Bucket__pageNode_r
public import Spec.go_etcd_io.bbolt.internal.common.Page__Count
public import Spec.go_etcd_io.bbolt.internal.common.Assert
public import Proof.go_etcd_io.bbolt.Read.Root
public import Proof.go_etcd_io.bbolt.Read.PubR
public import Proof.go_etcd_io.bbolt.Txn.RdInit
import all Spec.go_etcd_io.bbolt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem Cursor.Last.wp_reader [HasExt osFsExt]
    (hA : internal.common.Assert.spec (GF := GF) (hG := hG))
    (hRP : internal.common.InBucket.RootPage.spec (GF := GF) (hG := hG))
    (hpn : Bucket.pageNode_r.spec (GF := GF) (hG := hG))
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG))
    (hlast : Cursor.last_r.spec (GF := GF) (hG := hG))
    (hkv : Cursor.keyValue_r.spec (GF := GF) (hG := hG))
    (hkv0 : Cursor.keyValue_r0.spec (GF := GF) (hG := hG))
    (tx c : Loc) (γ : BoltName) (q : Qp) (T : TxView) (es : List BoltEnt) (pos : Option Nat)
    (hro : T.rw = false) :
  {{ boltTx (GF := GF) tx γ q T ∗ boltCur tx γ c T es pos }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"Last")) (Val #()))
  {{ (k v : GoSlice), RET (PairV #k #v); boltTx tx γ q T ∗
      boltCur tx γ c T es (some (es.length - 1)) ∗ curAt tx γ es (es.length - 1) k v }} := by
  wp_start as ⟨Ht, Hc⟩
  unfold boltTx boltCur
  icases rdCur_open _ _ tx c q T es pos hro $$ [Ht Hc] with
    ⟨%K, %v, %r, %b, %stk, %els, %bv, %ibp, %pp, Hk, #Hb, Hc, Hs, Hcap, #Hreg, #Hvo, %Hf, Hcl⟩
  · iframe
  obtain ⟨-, hfacts, -⟩ := Hf
  have hok := hfacts.2.1
  icases (persistent_entails_left (rdTxK_view K tx .loan q T v)) $$ Hk with ⟨Hk, %Hvw⟩
  obtain ⟨-, C, hokC, hvC⟩ := Hvw
  have hpv : v.pages = C.pages := by rw [← hvC]; rfl
  obtain ⟨-, -, -, pht, hpht⟩ := hokC.1
  rw [← hpv] at hpht
  obtain ⟨hrt, hrh⟩ := rRoot_ok pht hpht hok
  ihave #Hpkg := (rdTxK_pkgInit _ tx .loan q T v) $$ Hk
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  icases rdTxK_flags_acc K tx .loan q T v $$ Hk with ⟨Hmg, Hdb, Hw, -, %Hdbn, Hkcl⟩
  unfold rBktP
  icases Hb with ⟨#HIB, #Htx, #Hbks, #Hpage, #Hroot, #Hnodes, #Hhdr, #Hil⟩
  wp_auto
  rw [decide_eq_false Hdbn]
  simp only [Bool.not_false]
  wp_apply hA
  try wp_auto
  ihave Hk := Hkcl $$ Hmg Hdb Hw
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  ihave %Hcw := ownSliceCap_wf _ _ $$ Hcap
  try wp_auto
  rw [if_pos (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z stk.cap from ⟨by decide, by decide, by word⟩)]
  icases ownSlice_slice_with_cap (V := elemRef) (W64 0) (W64 0) stk els ⟨by decide, by decide, by word⟩
    $$ [Hs Hcap] with ⟨-, Hs, Hcap⟩
  · iframe
  have hsub : subslice (sint.nat (W64 0)) (sint.nat (W64 0)) els = ([] : List elemRef) := by
    simp [subslice]
  rw [hsub]
  wp_auto
  wp_method_call; wp_call
  wp_auto
  wp_apply wp_rd_rootPage hRP K tx .loan q T v bv ibp hok.1 $$ [Hk Hhdr] as ⟨Hk, -⟩
  · iframe; iframe #
  rw [show (decode (List.take 8 (bytesAt bv 0 16)) : w64) = (inBucketOf bv).root' from rfl]
  have hroot : (inBucketOf bv).root'.toNat = inBucketRoot bv := rfl
  obtain ⟨l, pg, hpa, h16, hpg⟩ := rTree_page v bv pp (inBucketRoot bv) hrt
  wp_apply hpn K tx .loan q T v b DFrac.discard bv ibp pp (inBucketOf bv).root' l pg hok.1
    (by rw [hroot]; exact hpa) $$ [Hk] as ⟨Hk, -⟩
  · iframe; unfold rBktP; iframe #
  try wp_auto
  -- `ref.count()`: the root page's count
  wp_method_call; wp_call
  wp_auto
  icases rd_hdr_acc K tx .loan q T v b DFrac.discard bv ibp pp (inBucketRoot bv) l pg hpa h16
    $$ [Hk] with ⟨%dqh, Hh, Hhb⟩
  · iframe; unfold rBktP; iframe #
  obtain ⟨hd, hH⟩ : ∃ hd, pageHdr pg = hd := ⟨_, rfl⟩
  have hcz : uint.Z hd.count' = (pageCount pg : Int) := by unfold pageCount; rw [hH]
  have hcnt16 := pageCount_lt pg
  rw [hH]
  wp_apply hCnt l hd dqh $$ [Hh] as Hh
  · iexact Hh
  ihave Hkb := Hhb $$ Hh
  icases Hkb with ⟨Hk, -⟩
  have hci : W64 (uint.Z hd.count') - W64 1 = W64 ((pageCount pg : Int) - 1) := by
    rw [hcz]; word
  rw [hci]
  try wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl', -⟩
  wp_apply wp_slice_append $$ [$Hs $Hcap $Hsl'] as %s1 ⟨Hs, Hcap, -⟩
  try wp_auto
  have hm : 0 < rFuel v bv := by unfold rFuel; split <;> omega
  obtain ⟨n0, hn0⟩ : ∃ n0, rFuel v bv = n0 + 1 := ⟨rFuel v bv - 1, by omega⟩
  have hlenR : (rEnts v bv).length = entCount (rLeaves v bv (rFuel v bv) (inBucketRoot bv)) := by
    rw [rLeaves_root]; rfl
  have hidx0 : W64 ((pageCount pg : Int) - 1) = W64 (((pageCount pg - 1 : Nat) : Int)) ∨
      pageCount pg = 0 := by
    by_cases h : pageCount pg = 0
    · exact Or.inr h
    · left; congr 1; omega
  have hcase : (¬ (pageFlags pg = leafPageFlag ∧ pageCount pg = 0) →
      rTlF v bv pp (rFuel v bv) (inBucketRoot bv)
        ⟨l, null, W64 ((pageCount pg : Int) - 1)⟩ (rEnts v bv).length) ∧
      (pageFlags pg = leafPageFlag ∧ pageCount pg = 0 →
        rLfTop v bv pp (inBucketRoot bv) ⟨l, null, W64 ((pageCount pg : Int) - 1)⟩) := by
    refine ⟨fun hne => ?_, fun h => ⟨pg, hpa, rfl, h.1⟩⟩
    rcases hpg with ⟨hlf, -⟩ | ⟨hbr, hi, -, hwm, hbwf, -⟩
    · have hc0 : pageCount pg ≠ 0 := fun h => hne ⟨hlf, h⟩
      right
      refine ⟨pg, pageCount pg - 1, ⟨hpa, rfl, hlf, by omega, ?_⟩, by omega, ?_⟩
      · show W64 ((pageCount pg : Int) - 1) = W64 (((pageCount pg - 1 : Nat) : Int))
        congr 1; omega
      · rw [hlenR, hn0, rLeaves_leaf v bv pp n0 _ l pg hpa hlf, entCount_single]; omega
    · left
      have hc0 := hbwf.1
      refine ⟨pg, pageCount pg - 1, ⟨hi, hpa, rfl, hbr, by omega, ?_⟩, ?_⟩
      · show W64 ((pageCount pg : Int) - 1) = W64 (((pageCount pg - 1 : Nat) : Int))
        congr 1; omega
      · rw [hlenR, hn0, rLeaves_branch v bv pp n0 _ l pg hi hpa hbr, Nat.sub_add_cancel hc0]
        rfl
  have hcase' : rTlF v bv pp (rFuel v bv) (inBucketRoot bv)
        ⟨l, null, W64 ((pageCount pg : Int) - 1)⟩ (rEnts v bv).length ∨
      rLfTop v bv pp (inBucketRoot bv) ⟨l, null, W64 ((pageCount pg : Int) - 1)⟩ := by
    by_cases h : pageFlags pg = leafPageFlag ∧ pageCount pg = 0
    · exact Or.inr (hcase.2 h)
    · exact Or.inl (hcase.1 h)
  wp_apply hlast K tx .loan q T v b DFrac.discard bv ibp pp c s1 [] _ (rFuel v bv) (inBucketRoot bv) 0
    (rEnts v bv).length hok (by simp [rPreF]) hm hcase' $$ [Hk Hc Hs Hcap]
    as ⟨%stk2, %els2, Hk, -, Hc, Hs, Hcap, %Hpost⟩
  · iframe; unfold rBktP; iframe #
  have hnil : els2 ≠ [] ∧ (1 < els2.length → ∃ e2 pid2 pg2, els2.getLast? = some e2 ∧
      rPageAt v bv pp pid2 = some (e2.page', pg2) ∧ e2.node' = null ∧ 16 ≤ pg2.length ∧
      0 < pageCount pg2) := by
    by_cases hc0 : pageFlags pg = leafPageFlag ∧ pageCount pg = 0
    · rw [Hpost.2 (hcase.2 hc0)]; simp
    · obtain ⟨i, hi, hpos, e2, pid2, pg2, idx, hl, hlf, -, hlwf, h16'⟩ := Hpost.1 (hcase.1 hc0)
      have hsl := rPosAt_last _ _ _ hpos e2 pid2 pg2 idx hl hlf
      refine ⟨(fun h => by rw [h] at hl; cases hl), fun _ => ⟨e2, pid2, pg2, hl, hlf.1, hlf.2.1, h16', ?_⟩⟩
      split at hsl <;> omega
  ihave %Hsl2 := ownSlice_len _ _ _ $$ Hs
  ihave IH : ("Hk" ∷ rdTxK K tx .loan q T v ∗ "Hcc" ∷ c ↦ Cursor.mk b stk2 ∗
      "Hs" ∷ stk2 ↦* els2 : IProp GF) $$ [Hk Hc Hs]
  · simp only [named]; iframe
  wp_for IH
  have hsl2 : sint.Z stk2.len = (els2.length : Int) := by
    have h1 := Hsl2.1; have h2 := Hsl2.2
    rw [show sint.nat stk2.len = (sint.Z stk2.len).toNat from rfl] at h1; omega
  have hlen2 : els2.length < 2 ^ 63 := by
    have h1 := Hsl2.1; rw [show sint.nat stk2.len = (sint.Z stk2.len).toNat from rfl] at h1; word
  by_cases h1 : 1 < els2.length
  rw [decide_eq_true (show sint.Z (W64 1) < sint.Z stk2.len by rw [hsl2, show sint.Z (W64 1) = 1 from rfl]; omega)]
  wp_auto
  obtain ⟨e2, pid2, pg2, hl2, hpa2, hn2, h162, hc2⟩ := hnil.2 h1
  have hsp2 : els2.dropLast ++ [e2] = els2 := by
    obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hl2; simp
  have hdl : (els2.dropLast.length : Int) + 1 = els2.length := by
    rw [← hsp2]; simp
  have hidx2 : sint.Z (stk2.len - W64 1) = (els2.dropLast.length : Int) := by
    rw [← hdl] at hsl2; word
  have hb2 : 0 ≤ sint.Z (stk2.len - W64 1) ∧ sint.Z (stk2.len - W64 1) < sint.Z stk2.len := by
    rw [hidx2]; omega
  rw [if_pos hb2]
  rw [← hsp2]
  icases ownSlice_elem_acc (sint.Z (stk2.len - W64 1)) e2 _ _ (els2.dropLast ++ [e2]) (by omega)
    (by rw [hidx2]; simp) $$ Hs with ⟨He, Hsback⟩
  wp_auto
  wp_method_call; wp_call
  wp_auto
  rw [hn2]
  wp_auto
  icases rd_hdr_acc K tx .loan q T v b DFrac.discard bv ibp pp pid2 e2.page' pg2 hpa2 h162
    $$ [Hk] with ⟨%dqh2, Hh, Hhb⟩
  · iframe; unfold rBktP; iframe #
  obtain ⟨hd2, hH2⟩ : ∃ hd, pageHdr pg2 = hd := ⟨_, rfl⟩
  have hcz2 : uint.Z hd2.count' = (pageCount pg2 : Int) := by unfold pageCount; rw [hH2]
  have hcL := pageCount_lt pg2
  rw [hH2]
  wp_apply hCnt e2.page' hd2 dqh2 $$ [Hh] as Hh
  · iexact Hh
  ihave Hkb := Hhb $$ Hh
  icases Hkb with ⟨Hk, -⟩
  ihave Hs := Hsback $$ He
  rw [show (els2.dropLast ++ [e2]).set (sint.Z (stk2.len - W64 1)).toNat e2 =
    els2.dropLast ++ [e2] by rw [hidx2]; simp, hsp2]
  have hne0 : W64 (uint.Z hd2.count') ≠ W64 0 := by
    rw [hcz2]; intro h; have := congrArg BitVec.toNat h; simp at this; omega
  rw [decide_eq_false hne0]
  try wp_auto
  simp only [intoVal_eq_iff, Bool.false_eq_true, decide_False_any, ite_false]
  rotate_left
  rw [decide_eq_false (show ¬ sint.Z (W64 1) < sint.Z stk2.len by rw [hsl2, show sint.Z (W64 1) = 1 from rfl]; omega)]
  try wp_auto
  simp only [intoVal_eq_iff, Bool.false_eq_true, decide_False_any, ite_false]
  rotate_left
  all_goals (
    simp only [decide_True_any, ite_true]
    wp_auto
    have hne : stk2.len ≠ W64 0 := by
      intro h; rw [h] at hsl2
      have : els2.length = 0 := by simp at hsl2; omega
      exact hnil.1 (List.eq_nil_of_length_eq_zero this)
    rw [decide_eq_false hne]
    wp_auto
    obtain ⟨-, -, hes, hplain⟩ := hfacts
    by_cases hc0 : pageFlags pg = leafPageFlag ∧ pageCount pg = 0
    · -- the empty root leaf, at index `-1`
      have hel := Hpost.2 (hcase.2 hc0)
      rw [hel]
      wp_apply hkv0 K tx .loan q T v b DFrac.discard bv ibp pp c stk2 [] ⟨l, null, W64 ((pageCount pg : Int) - 1)⟩ (inBucketRoot bv) pg
        hpa rfl h16 hc0.2 $$ [Hk Hcc Hs] as ⟨Hk, -, Hcc, Hs⟩
      · iframe; unfold rBktP; iframe #
      try wp_auto
      try rw [decide_eq_true (show (W32 0 : w32) &&& W32 1 = W32 0 by decide)]
      try simp only [Bool.not_true]
      try wp_auto
      have hre : rEnts v bv = [] := by
        unfold rEnts
        rw [← rLeaves_root, hn0, rLeaves_leaf v bv pp n0 _ l pg hpa hc0.1]
        simp [lEnts, hc0.2]
      have hes0 : es = [] := by
        rw [hes, ← rEnts_bktEntries, hre]; rfl
      iapply HΦ
      ihave Hfin := Hcl $$ %stk2 %([] ++ [⟨l, null, W64 ((pageCount pg : Int) - 1)⟩]) %(some (es.length - 1)) Hk Hcc Hs Hcap
      ihave Hfin := Hfin $$ []
      · ipureintro
        rw [hes0]
        refine Or.inr ⟨rfl, hre, _, pg, rfl, hpa, rfl, hc0.1, hc0.2, Or.inr ?_⟩
        show W64 ((pageCount pg : Int) - 1) = W64 (-1)
        rw [hc0.2]; rfl
      icases Hfin with ⟨Ht, Hc⟩
      iframe
      unfold curAt
      rw [hes0]
      simp only [List.length_nil, Nat.zero_sub, List.getElem?_nil]
      ipureintro; simp
    · obtain ⟨i, hi, hpos, e2, pid2, pg2, idx, hl, hlf, -, hlwf, h16'⟩ := Hpost.1 (hcase.1 hc0)
      have hsl := rPosAt_last _ _ _ hpos e2 pid2 pg2 idx hl hlf
      have hil : idx < pageCount pg2 := by
        by_cases h : idx < pageCount pg2
        · exact h
        · rw [if_neg h] at hsl; omega
      have hsp2 : els2.dropLast ++ [e2] = els2 := by
        obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hl; simp
      have hix : sint.Z e2.index' = (idx : Int) := by
        rw [hlf.2.2.2.2]; have := pageCount_lt pg2; word
      rw [← hsp2]
      wp_apply hkv K tx .loan q T v b DFrac.discard bv ibp pp c stk2 els2.dropLast e2 pid2 pg2 hlf.1
        hlf.2.1 hlf.2.2.1 hlwf h16' (by omega) $$ [Hk Hcc Hs] as %k %vl %fl ⟨Hk, -, Hcc, Hs, Hkv⟩
      · iframe; unfold rBktP; iframe #
      rw [hix, Int.toNat_natCast]
      have hent := rPosAt_ent' _ _ _ hpos (by omega) e2 pid2 pg2 idx hl hlf
      icases rKV_curAt γ tx r v bv es i pg2 idx k vl fl hes hent $$ [Hkv] with ⟨#Hca, %Hfl⟩
      · iframe #; iexact Hkv
      have hflb : fl &&& W32 1 = W32 0 := by
        obtain ⟨hpgm, -⟩ := rEnts_mem v bv i pg2 idx hent
        have := hplain pg2 hpgm idx hil
        unfold leafFlags at this; rw [← Hfl] at this; exact (w32_and_one fl).2 this
      try wp_auto
      rw [decide_eq_true hflb]
      simp only [Bool.not_true]
      wp_auto
      have hlen : es.length - 1 = i := by
        rw [hes, rEnts_length]; omega
      iapply HΦ
      ihave Hfin := Hcl $$ %stk2 %(els2.dropLast ++ [e2]) %(some (es.length - 1)) Hk Hcc Hs Hcap
      ihave Hfin := Hfin $$ []
      · ipureintro; rw [hlen, hsp2]; exact Or.inl ⟨_, hpos, fun h => by omega⟩
      icases Hfin with ⟨Ht, Hc⟩
      rw [hlen]
      iframe; iframe #)

/-- **A writer's `Last`**: U6w's (`Cursor.Last.wp_writer`, `Read/PubW*`). -/
theorem Cursor.Last.wp_writer [HasExt osFsExt]
    (tx c : Loc) (γ : BoltName) (q : Qp) (T : TxView) (es : List BoltEnt) (pos : Option Nat)
    (hrw : T.rw = true) :
  {{ boltTx (GF := GF) tx γ q T ∗ boltCur tx γ c T es pos }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"Last")) (Val #()))
  {{ (k v : GoSlice), RET (PairV #k #v); boltTx tx γ q T ∗
      boltCur tx γ c T es (some (es.length - 1)) ∗ curAt tx γ es (es.length - 1) k v }} := by
  sorry

theorem Cursor.Last.wp_proof
    (hA : internal.common.Assert.spec (GF := GF) (hG := hG))
    (hRP : internal.common.InBucket.RootPage.spec (GF := GF) (hG := hG))
    (hpn : ∀ [HasExt osFsExt], Bucket.pageNode_r.spec (GF := GF) (hG := hG))
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG))
    (hlast : ∀ [HasExt osFsExt], Cursor.last_r.spec (GF := GF) (hG := hG))
    (hkv : ∀ [HasExt osFsExt], Cursor.keyValue_r.spec (GF := GF) (hG := hG))
    (hkv0 : ∀ [HasExt osFsExt], Cursor.keyValue_r0.spec (GF := GF) (hG := hG)) :
    Cursor.Last.spec (GF := GF) (hG := hG) := by
  intro _ tx c γ q T es pos
  by_cases hrw : T.rw = true
  · exact Cursor.Last.wp_writer tx c γ q T es pos hrw
  · exact Cursor.Last.wp_reader hA hRP hpn hCnt hlast hkv hkv0 tx c γ q T es pos
      (Bool.eq_false_iff.2 hrw)

end proof

end bbolt
end EtcdGrove
end Perennial
