/-
A writer's `Cursor.Seek` at any fraction (U6aa, `notes/bbolt-proof-plan.md`, "Writer reads at a
fraction"): `wrCur_open`, `Assert` on the transaction's database, `seek` (`seek_w`: a logical stack
routing the key, at `seekIdx` by the bridge `WBridge.lPath_wStk`/`lPath_seek`, its persistent part
`WSeek.wtxWQ_lPath_own`); past its leaf's end, `next` (`next_w`, to the same position); the result as
`curAt`, and the cursor closed at `seekIdx`.
-/
module

public import Proof.go_etcd_io.bbolt.Read.PubWCur
public import Proof.go_etcd_io.bbolt.Read.PubWSeekOwn
public import Proof.go_etcd_io.bbolt.Read.WNextCnt
public import Proof.go_etcd_io.bbolt.Read.WOpenOK
public import Spec.go_etcd_io.bbolt.Cursor__seek_w
public import Spec.go_etcd_io.bbolt.Cursor__next_w
public import Spec.go_etcd_io.bbolt.internal.common.Assert
public import Spec.go_etcd_io.bbolt.internal.common.Page__Count
import all Spec.go_etcd_io.bbolt.Api

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pubWSeek
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `seekIdx` is at most the number of entries. -/
theorem seekIdx_le' (es : List BoltEnt) (k : List w8) : seekIdx es k ≤ es.length :=
  List.IsPrefix.length_le (List.takeWhile_prefix _)

/-- `curAt` of a nil key: the value is nil too. -/
theorem curAt_nil_key [HasExt osFsExt] (γ : BoltName) (tx : Loc) (es : List BoltEnt) (j : Nat)
    (vl : GoSlice) : curAt (GF := GF) tx γ es j slice.nil vl ⊢ ⌜vl = slice.nil⌝ := by
  unfold curAt
  split
  · iintro ⟨%h, -⟩; exact absurd rfl h
  · iintro %h; ipureintro; exact h.2

/-- `curAt` on an entry: the key is not nil. -/
theorem curAt_some_key [HasExt osFsExt] (γ : BoltName) (tx : Loc) (es : List BoltEnt) (j : Nat)
    (k vl : GoSlice) (x : BoltEnt) (h : es[j]? = some x) :
    curAt (GF := GF) tx γ es j k vl ⊢ ⌜k ≠ slice.nil⌝ := by
  unfold curAt
  rw [h]
  iintro ⟨%hk, -⟩; ipureintro; exact hk

/-- **A writer's `Seek`** at any fraction, over `seek_w` and `next_w` (`hD1`: `gensOK`'s third
clause; `hW`: `wrCurFacts`, OPEN). -/
theorem Cursor.Seek.wp_writerW [HasExt osFsExt]
    (hA : internal.common.Assert.spec (GF := GF) (hG := hG))
    (hseek : Cursor.seek_w.specQ (GF := GF) (hG := hG))
    (hnx : Cursor.next_w.specQ (GF := GF) (hG := hG))
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG))
    (tx c : Loc) (γ : BoltName) (q : Qp) (T : TxView) (es : List BoltEnt) (pos : Option Nat)
    (key : GoSlice) (kb : GoString) (dk : DFrac)
    (hrw : T.rw = true)
    (hD1 : ∀ X : WX, gensOK T X →
      ∀ b n, X.handles !! b = some (n, T.gen n) → bktLoc X n = some b)
    (hW : ∀ X : WX, wOK X → gensOK T X → wrFacts X → T.cur = wtxData X → T.base = X.v.data →
      wrCurFacts T X) :
  {{ boltTx (GF := GF) tx γ q T ∗ boltCur tx γ c T es pos ∗ key ↦*{dk} kb }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"Seek")) (Val #key))
  {{ (k v : GoSlice), RET (PairV #k #v); boltTx tx γ q T ∗ key ↦*{dk} kb ∗
      boltCur tx γ c T es (some (seekIdx es kb)) ∗ curAt tx γ es (seekIdx es kb) k v }} := by
  wp_start as ⟨Ht, Hc, Hkey⟩
  unfold boltTx boltCur
  icases wrCur_open _ _ tx c q T es pos hrw hD1 hW $$ [Ht Hc] with
    ⟨%K, %r, %X, %n, %b, %stk, %els, %nl, %ipg, Hw, Hc, Hs, Hcap, #Hown, #Hreg, #Hvo, %Hf, Hcl⟩
  · iframe
  obtain ⟨hctx, hes, hbrl, -⟩ := Hf
  have hok := hctx.1
  icases wtxWQ_pkgInit K tx r true q X $$ Hw with ⟨Hw, #Hpkg⟩
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  icases wtxWQ_heapOK K tx r true q X $$ Hw with ⟨Hw, %Hhok⟩
  obtain ⟨C, hC⟩ := PubW.bktLoc_rec X hctx.1 n b hctx.2.1
  icases wtxWQ_child_tx K tx r true q X b C hC hbrl Hhok $$ Hw with ⟨Hw, #Hbtx⟩
  icases (persistent_entails_left (wtxWQ_page_maxMap K tx r true q X)) $$ Hw with ⟨Hw, %Hmax⟩
  icases wtxWQ_cells_acc K tx r true q X $$ Hw with ⟨%Hbase, Hcells, Hwb⟩
  ihave Hw := Hwb $$ Hcells
  have hloc := PubW.bktLocalOK_of_wOK X hok b C hC
  have hpm := PubW.pmFresh_of_wOK X hok
  icases wtxWQ_db_acc K tx r true q X $$ Hw with ⟨Hdb, %Hdbn, Hwdb⟩
  wp_auto
  rw [decide_eq_false Hdbn]
  simp only [Bool.not_false]
  wp_apply hA
  try wp_auto
  ihave Hw := Hwdb $$ Hdb
  have hand : ∀ f : w32, ¬ isBktFlag f → f &&& W32 1 = W32 0 := by
    intro f h; unfold isBktFlag at h; exact Classical.not_not.1 h
  wp_apply hseek K tx r true q X b c stk els key kb (KeyR.heap dk) hloc hpm
    $$ [Hw Hc Hs Hcap Hkey]
    as %k %vl %fl ⟨%stk', %els', %pids, Hw, Hc, Hs, Hcap, Hkey, %Hr, Hkv⟩
  · iframe; unfold keyR; iframe
  obtain ⟨hp, hrt⟩ := Hr
  have hrt0 : (X.rootPid b).toNat = wRoot X.v T n := hctx.2.2.2.1
  obtain ⟨hpath, hlo, hents, hplain⟩ :=
    WBridge.lPath_wStk X n b C hok hctx.2.1 hbrl hctx.2.2.1 hC Hbase els' pids hp
  obtain ⟨hsp, hli⟩ :=
    WBridge.lPath_seek X n b C hok hctx.2.1 hbrl hctx.2.2.1 hC Hbase els' pids kb hp hrt
  rw [hrt0] at hpath
  subst hes
  icases WSeek.wtxWQ_lPath_own K tx r true q X n b (wRoot X.v T n) C hctx hC Hmax Hbase els' pids hp
    $$ Hw with ⟨Hw, #Hown'⟩
  -- the stack's top
  have hne : els' ≠ [] := hp.1
  obtain ⟨E, e, hEe⟩ : ∃ E e, els' = E ++ [e] :=
    ⟨els'.dropLast, els'.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
  subst hEe
  have hcnt : leafCnt X.v (wEs X n) (pids.map (·.toNat)) (E ++ [e]) = (lLeaf X b pids).length := by
    unfold leafCnt; rw [← hents, List.length_map]
  have hwl := Write.wsIdx_le (lLeaf X b pids) kb
  have hli' : leafIdx (E ++ [e]) = e.index'.toNat := by exact WKVs.leafIdx_append E e
  ihave %Hsl2 := ownSlice_len _ _ _ $$ Hs
  have hidx2 : sint.Z (stk'.len - W64 1) = (E.length : Int) := by
    have h1 := Hsl2.1; have h2 := Hsl2.2
    rw [show sint.nat stk'.len = (sint.Z stk'.len).toNat from rfl] at h1
    simp only [List.length_append, List.length_singleton] at h1; word
  try wp_auto
  rw [if_pos (show 0 ≤ sint.Z (stk'.len - W64 1) ∧ sint.Z (stk'.len - W64 1) < sint.Z stk'.len by
    rw [hidx2]; constructor <;> word)]
  icases ownSlice_elem_acc (sint.Z (stk'.len - W64 1)) e _ _ (E ++ [e]) (by omega)
    (by rw [hidx2]; simp) $$ Hs with ⟨He, Hsback⟩
  rw [hidx2]
  wp_auto
  wp_apply WNext.wp_lvl_count hCnt K tx r true q X n b (wRoot X.v T n) C.ipg (WGoFirst.nlX X)
    (E ++ [e]) (pids.map (fun x : w64 => x.toNat)) hctx hpath hlo E.length (by simp) e (by simp) _
    $$ [Hw He] as ⟨Hw, He, %H63⟩
  · iframe; iframe #
  rw [WNext.cntAt_leaf X.v (wEs X n) _ _ E.length (by simp), hcnt] at H63 ⊢
  have hix : sint.Z e.index' = (wsIdx (lLeaf X b pids) kb : Int) := by
    have h1 : e.index'.toNat = wsIdx (lLeaf X b pids) kb := by rw [← hli', hli]
    have h2 : e.index'.toNat < 2 ^ 63 := by omega
    word
  have hcz : sint.Z (W64 ((lLeaf X b pids).length : Int)) = ((lLeaf X b pids).length : Int) := by
    word
  obtain ⟨pl, ws, ⟨jl, hjl⟩, hL, hle⟩ := WOpen.lPath_leaf X b C hC hloc (E ++ [e]) pids hp
  have hI := WOpen.lPath_posI X b C hC hloc (E ++ [e]) pids hp jl pl hjl
  have hlt_iff : leafIdx (E ++ [e]) < leafCnt X.v (wEs X n) (pids.map (fun x : w64 => x.toNat))
      (E ++ [e]) ↔ wsIdx (lLeaf X b pids) kb < (lLeaf X b pids).length := by rw [hli, hcnt]
  ihave Hs := Hsback $$ He
  rw [show (E ++ [e]).set (↑E.length : Int).toNat e = E ++ [e] by simp]
  cases hw : (lLeaf X b pids)[wsIdx (lLeaf X b pids) kb]? with
  | some w =>
    -- on an entry
    have hlt : wsIdx (lLeaf X b pids) kb < (lLeaf X b pids).length := by
      apply Nat.lt_of_not_le; intro h; rw [List.getElem?_eq_none h] at hw; cases hw
    have hc : ¬ (sint.Z (W64 ((lLeaf X b pids).length : Int)) ≤ sint.Z e.index') := by
      rw [hcz, hix]; omega
    rw [decide_eq_false hc]
    icases Hkv with ⟨%Hkw, #Hks, #Hvs⟩
    obtain ⟨Hkn, rfl⟩ := Hkw
    have hwm : w ∈ lLeaf X b pids := List.mem_of_getElem? hw
    have hwm' : w ∈ ws := by rw [← hle]; exact hwm
    obtain ⟨hlks, hlvs⟩ := WOpen.leaf_live X b C hC hloc pl hI ws hL w hwm'
    have hfl := hplain w hwm
    have hget : (wEs X n)[seekIdx (wEs X n) kb]? = some (w.key, w.value) := by
      rw [← hsp]
      have h := WKVs.stackPos_get X.v (((wtxData X) !! n).getD ∅) (pids.map (fun x : w64 => x.toNat))
        (E ++ [e]) (hlt_iff.2 hlt)
      refine h.trans ?_
      unfold wEs at hents
      rw [← hents, hli, List.getElem?_map, hw]; rfl
    ihave #Hkv : wEntKV X.v (wEs X n) (seekIdx (wEs X n) kb) k vl w.flags $$ []
    · unfold wEntKV; rw [hget]
      isplitr
      · ipureintro; exact ⟨Hkn, hfl⟩
      isplitl
      · iapply WKVs.srcOwn_ent X.v k _ w.key (WOpen.leafSrc_live X b C hC hloc _ hlks) $$ Hks
      · iapply WKVs.srcOwn_ent X.v vl _ w.value (WOpen.leafSrc_live X b C hC hloc _ hlvs) $$ Hvs
    icases wEntKV_curAt γ tx r X (wEs X n) (seekIdx (wEs X n) kb) k vl w.flags $$ [Hkv] with
      ⟨#Hca, -⟩
    · iframe #
    wp_auto
    rw [decide_eq_false Hkn]
    wp_auto
    rw [decide_eq_true (hand _ hfl)]
    simp only [Bool.not_true]
    wp_auto
    iapply HΦ
    ihave Hfin := Hcl $$ %stk' %(E ++ [e]) %(WGoFirst.nlX X) %C.ipg %(some (seekIdx (wEs X n) kb))
      Hw Hc Hs Hcap Hown'
    ihave Hfin := Hfin $$ []
    · ipureintro; exact ⟨_, hpath, hlo, Or.inl ⟨hlt_iff.2 hlt, hsp.symm⟩⟩
    icases Hfin with ⟨Ht, Hc⟩
    unfold keyR
    iframe; iframe #
  | none =>
    -- past the leaf's end: `next`
    have hge : ¬ wsIdx (lLeaf X b pids) kb < (lLeaf X b pids).length := by
      intro h; rw [List.getElem?_eq_getElem h] at hw; cases hw
    have hc : sint.Z (W64 ((lLeaf X b pids).length : Int)) ≤ sint.Z e.index' := by
      rw [hcz, hix]; omega
    rw [decide_eq_true hc]
    icases Hkv with %Hnil
    wp_auto
    have hstk : wStk (WGoFirst.nlX X) X.v (wEs X n) b (wRoot X.v T n) C.ipg (E ++ [e])
        (pids.map (fun x : w64 => x.toNat)) :=
      ⟨hpath, hlo, by rw [hli, hcnt]; exact hwl⟩
    have hto : wNextTo X.v (wEs X n) (pids.map (fun x : w64 => x.toNat)) (E ++ [e]) =
        seekIdx (wEs X n) kb := by
      unfold wNextTo; rw [if_neg (fun h => hge (hlt_iff.1 h)), hsp]
    wp_apply hnx K tx r true q X n b (wRoot X.v T n) C.ipg (WGoFirst.nlX X) c stk' (E ++ [e])
      (pids.map (fun x : w64 => x.toNat)) hctx hstk $$ [Hw Hc Hs Hcap]
      as %k2 %vl2 %fl2 ⟨%stk3, %els3, %nl3, Hw, Hc, Hs, Hcap, #Hown3, %Hpost, #Hkv2⟩
    · iframe; iframe #
    rw [hto] at Hpost ⊢
    icases wEntKV_curAt γ tx r X (wEs X n) (seekIdx (wEs X n) kb) k2 vl2 fl2 $$ [Hkv2] with
      ⟨#Hca, %Hfl2⟩
    · iframe #
    have hcp : wCurAt nl3 X.v (wEs X n) b (wRoot X.v T n) C.ipg els3
        (some (seekIdx (wEs X n) kb)) := by
      obtain ⟨pids', hp', hlf', hcase⟩ := Hpost
      rcases hcase with ⟨-, hli3, hst3⟩ | ⟨hle3, hcase⟩
      · exact ⟨pids', hp', hlf', Or.inl ⟨hli3, hst3.symm⟩⟩
      · rcases hcase with ⟨-, -, hbad⟩ | hend
        · exact absurd hbad (fun h => hge (hlt_iff.1 h))
        · exact ⟨pids', hp', hlf', Or.inr ⟨hend, Or.inl (by
            have := seekIdx_le' (wEs X n) kb; omega)⟩⟩
    try wp_auto
    by_cases hk : k2 = slice.nil
    · subst hk
      ihave %Hv := curAt_nil_key γ tx (wEs X n) _ vl2 $$ Hca
      subst Hv
      try rw [decide_eq_true (rfl : (slice.nil : GoSlice) = slice.nil)]
      wp_auto
      iapply HΦ
      ihave Hfin := Hcl $$ %stk3 %els3 %nl3 %C.ipg %(some (seekIdx (wEs X n) kb))
        Hw Hc Hs Hcap Hown3
      ihave Hfin := Hfin $$ []
      · ipureintro; exact hcp
      icases Hfin with ⟨Ht, Hc⟩
      unfold keyR
      iframe; iframe #
    · rw [decide_eq_false hk]
      wp_auto
      rw [decide_eq_true (hand _ Hfl2)]
      simp only [Bool.not_true]
      wp_auto
      iapply HΦ
      ihave Hfin := Hcl $$ %stk3 %els3 %nl3 %C.ipg %(some (seekIdx (wEs X n) kb))
        Hw Hc Hs Hcap Hown3
      ihave Hfin := Hfin $$ []
      · ipureintro; exact hcp
      icases Hfin with ⟨Ht, Hc⟩
      unfold keyR
      iframe; iframe #

end pubWSeek

end bbolt
end EtcdGrove
end Perennial
