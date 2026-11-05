/-
A writer's `Cursor.Last` at any fraction (U6aa, `notes/bbolt-proof-plan.md`, "Writer reads at a
fraction"): `wrCur_open`, `Assert` on the transaction's database, the stack emptied, the root
reference from `pageNode_w` at its last index (`Read/PubWLastRoot`), `last_w` down to a leaf (every
branch and the leaf at their last index: `Last`'s invariant `wLastInv`), the loop of `prev_w` over
trailing empty leaves (`wLastInv` kept), and `keyValue_ws`: the last entry (`sTailEmpty`), or the
empty bucket.
-/
module

public import Proof.go_etcd_io.bbolt.Read.PubWCur
public import Proof.go_etcd_io.bbolt.Read.PubWLastRoot
public import Proof.go_etcd_io.bbolt.Read.WNextCnt
public import Proof.go_etcd_io.bbolt.Read.WPrevPure
public import Proof.go_etcd_io.bbolt.Read.WPrevOwn
public import Proof.go_etcd_io.bbolt.Read.WFirstTop
public import Spec.go_etcd_io.bbolt.Bucket__pageNode_w
public import Spec.go_etcd_io.bbolt.Cursor__last_w
public import Spec.go_etcd_io.bbolt.Cursor__prev_w
public import Spec.go_etcd_io.bbolt.Cursor__keyValue_ws
public import Spec.go_etcd_io.bbolt.internal.common.Assert
public import Spec.go_etcd_io.bbolt.internal.common.Page__Count
public import Spec.go_etcd_io.bbolt.internal.common.InBucket__RootPage
import all Spec.go_etcd_io.bbolt.Api

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace WLastPub

section pure
variable [GooseExts]

open Classical in
/-- **Where `Last`'s loop stops** (`wLastInv`, the top a leaf of a one-element stack or not empty):
`keyValue`'s premise, its entry the last (`es.length - 1`; the empty bucket at the empty root
leaf), and the cursor there (`wCurAt`). -/
theorem last_exit (nl : Loc → Option (Loc × Nat)) (v : View) (es : List BoltEnt) (b : Loc)
    (rt : Nat) (ipg : List w8) (els : List elemRef) (pids : List Nat)
    (hinv : wLastInv nl v es b rt ipg els pids)
    (hex : els.length ≤ 1 ∨ leafCnt v es pids els ≠ 0) :
    (leafIdx els ≤ leafCnt v es pids els ∨ wEndAt v es pids els ∨
      (leafCnt v es pids els = 0 ∧ ∃ e, els.getLast? = some e ∧ e.index' = W64 (-1))) ∧
    (if leafIdx els < leafCnt v es pids els then stackPos v es pids els else es.length) =
      es.length - 1 ∧
    wCurAt nl v es b rt ipg els (some (es.length - 1)) := by
  obtain ⟨hp, hlo, ht, e, he, hcase⟩ := hinv
  have hli := WNext.leafIdx_of els e he
  have ht' := ht
  unfold sTailEmpty at ht'
  rcases hcase with ⟨h0, hi⟩ | ⟨hpos, hi⟩
  · -- an empty leaf: the root leaf alone, the bucket empty
    have hl1 : els.length = 1 := by
      rcases hex with h | h
      · have : 0 < els.length := List.length_pos_iff.2 hp.1
        omega
      · exact absurd h0 h
    obtain ⟨lf, rfl⟩ : ∃ lf, els = [lf] := by
      match els, hl1 with
      | [x], _ => exact ⟨x, rfl⟩
    have hes : es = [] := WPrev.tail_root v es [] lf pids (by have := hp.2.1; simpa using this)
      (fun x hx => by simp at hx) (by simpa using ht) (by simpa using h0)
    clear ht'
    subst hes
    have hlf : e = lf := by simpa using he.symm
    subst hlf
    have hend : wEndAt v [] pids [e] := by
      refine ⟨fun j pid x _ _ hj => by simp at hj, e, he, ?_⟩
      rcases hi with hi | hi
      · left; rw [hi, h0]; rfl
      · right; exact ⟨h0, hi⟩
    refine ⟨Or.inr (Or.inl hend), ?_, ⟨pids, hp, hlo, Or.inr ⟨hend, Or.inl (by simp)⟩⟩⟩
    rw [if_neg (by omega)]; rfl
  · have hlt : leafIdx els < leafCnt v es pids els := by omega
    have hsp : stackPos v es pids els = es.length - 1 := by unfold stackPos; omega
    refine ⟨Or.inl (by omega), by rw [if_pos hlt, hsp], ⟨pids, hp, hlo, Or.inl ⟨hlt, hsp.symm⟩⟩⟩

end pure

end WLastPub

section pubWLast
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **A writer's `Last`** at any fraction, over `pageNode_w`, `last_w`, `prev_w` and `keyValue_ws`
(`hD1`: `gensOK`'s third clause; `hW`: `wrCurFacts`, OPEN). -/
theorem Cursor.Last.wp_writerW [HasExt osFsExt]
    (hA : internal.common.Assert.spec (GF := GF) (hG := hG))
    (hRP : internal.common.InBucket.RootPage.spec (GF := GF) (hG := hG))
    (hpn : Bucket.pageNode_w.specQ (GF := GF) (hG := hG))
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG))
    (hlast : Cursor.last_w.specQ (GF := GF) (hG := hG))
    (hprev : Cursor.prev_w.specQ (GF := GF) (hG := hG))
    (hkv : Cursor.keyValue_ws.specQ (GF := GF) (hG := hG))
    (tx c : Loc) (γ : BoltName) (q : Qp) (T : TxView) (es : List BoltEnt) (pos : Option Nat)
    (hrw : T.rw = true)
    (hD1 : ∀ X : WX, gensOK T X →
      ∀ b n, X.handles !! b = some (n, T.gen n) → bktLoc X n = some b)
    (hW : ∀ X : WX, wOK X → gensOK T X → wrFacts X → T.cur = wtxData X → T.base = X.v.data →
      wrCurFacts T X) :
  {{ boltTx (GF := GF) tx γ q T ∗ boltCur tx γ c T es pos }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"Last")) (Val #()))
  {{ (k v : GoSlice), RET (PairV #k #v); boltTx tx γ q T ∗
      boltCur tx γ c T es (some (es.length - 1)) ∗ curAt tx γ es (es.length - 1) k v }} := by
  wp_start as ⟨Ht, Hc⟩
  unfold boltTx boltCur
  icases wrCur_open _ _ tx c q T es pos hrw hD1 hW $$ [Ht Hc] with
    ⟨%K, %r, %X, %n, %b, %stk, %els, %nl, %ipg, Hw, Hc, Hs, Hcap, #Hown, #Hreg, #Hvo, %Hf, Hcl⟩
  · iframe
  obtain ⟨hctx, hes, hbrl, -⟩ := Hf
  subst hes
  have hok := hctx.1
  icases wtxWQ_pkgInit K tx r true q X $$ Hw with ⟨Hw, #Hpkg⟩
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  icases wtxWQ_heapOK K tx r true q X $$ Hw with ⟨Hw, %Hhok⟩
  obtain ⟨B, hB⟩ := PubW.bktLoc_rec X hctx.1 n b hctx.2.1
  have hlive : b ∈ X.liveB := hok.2.2.2.2.2.1.2.2.1 b B hB
  have hcl := Write.wOK_bktClean X hok b B hB
  icases wtxWQ_child_tx K tx r true q X b B hB hbrl Hhok $$ Hw with ⟨Hw, #Hbtx⟩
  icases (persistent_entails_left (wtxWQ_page_maxMap K tx r true q X)) $$ Hw with ⟨Hw, %Hmax⟩
  icases wtxWQ_cells_acc K tx r true q X $$ Hw with ⟨%Hbase, Hcells, Hwb⟩
  ihave Hw := Hwb $$ Hcells
  icases wtxWQ_nodes_nonnull K tx r true q X b B hB $$ Hw with ⟨Hw, %Hnodes⟩
  icases wtxWQ_db_acc K tx r true q X $$ Hw with ⟨Hdb, %Hdbn, Hwdb⟩
  wp_auto
  rw [decide_eq_false Hdbn]
  simp only [Bool.not_false]
  wp_apply hA
  try wp_auto
  ihave Hw := Hwdb $$ Hdb
  have hand : ∀ f : w32, ¬ isBktFlag f → f &&& W32 1 = W32 0 := by
    intro f h; unfold isBktFlag at h; exact Classical.not_not.1 h
  -- the stack emptied
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  ihave %Hcw := ownSliceCap_wf _ _ $$ Hcap
  rw [if_pos ⟨by decide, by decide, by word⟩]
  icases ownSlice_slice_with_cap (V := elemRef) (W64 0) (W64 0) stk els
    ⟨by decide, by decide, by word⟩ $$ [Hs Hcap] with ⟨-, Hs, Hcap⟩
  · iframe
  have hsub : subslice (sint.nat (W64 0)) (sint.nat (W64 0)) els = ([] : List elemRef) := by
    simp [subslice]
  rw [hsub]
  wp_auto
  wp_method_call; wp_call
  icases wtxWQ_bkt_acc K tx r true q X b B hB $$ Hw with ⟨Ho, Hback⟩
  isimp only [objOwn] at Ho
  icases Ho with ⟨HIB, Htx, Hbks, Hpage, Hroot, Hnodes, Hib, Hnm, Hbm, Hpo⟩
  wp_auto
  wp_apply hRP $$ [Hib] as Hib
  · iexact Hib
  ihave Hw := Hback $$ [HIB Htx Hbks Hpage Hroot Hnodes Hib Hnm Hbm Hpo]
  · isimp only [objOwn]; iframe
  have hpre := WFirst.root_pn_pre X n b (wRoot X.v T n) B hctx hB Hmax
  wp_apply hpn K tx r true q X b B B.ib.root' hB hlive (fun h => h) (fun h => absurd h Hnodes)
    (fun c l h => (hcl.2.2.2.2.1 c l h).1)
    (fun h => by obtain ⟨pa, pg, h1, h2, -, h4⟩ := hpre h; exact ⟨pa, pg, h1, h2, h4⟩) $$ [Hw]
    as %p %nd ⟨Hw, %Hpn⟩
  · iframe
  obtain ⟨lf, ws, hL, hra, hnode, hpage⟩ :=
    WLastPub.root_ws X n b (wRoot X.v T n) B hctx hB Hbase p nd Hpn
  try wp_auto
  wp_apply WLastPub.wp_root_count hCnt K tx r true q X n b (wRoot X.v T n) B hctx hB Hmax p nd ws
    hnode hpage _ _ $$ [Hw ref] as ⟨Hw, Href, %Hwl⟩
  · iframe
  try wp_auto
  rw [show W64 (ws.length : Int) - W64 1 = W64 ((ws.length : Int) - 1) by word]
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl', -⟩
  wp_apply wp_slice_append $$ [$Hs $Hcap $Hsl'] as %s1 ⟨Hs, Hcap, -⟩
  try wp_auto
  obtain ⟨hpre1, hlok1, htop1⟩ :=
    WLastPub.root_last X n b (wRoot X.v T n) B hctx hB Hbase p nd lf ws hL hra Hwl
  obtain ⟨-, -, hnl1⟩ := WFirst.root_push X n b (wRoot X.v T n) B hctx hB Hbase ⟨p, nd, W64 0⟩ rfl Hpn
  icases WFirst.root_own K tx r true q X n b (wRoot X.v T n) B hctx hB Hmax
    ⟨p, nd, W64 ((ws.length : Int) - 1)⟩ hnl1 Hpn $$ Hw with ⟨Hw, #Hown1⟩
  wp_apply hlast K tx r true q X n b (wRoot X.v T n) B.ipg (WGoFirst.nlX X) c s1
    [⟨p, nd, W64 ((ws.length : Int) - 1)⟩] [wRoot X.v T n] hctx hpre1 hlok1
    $$ [Hw Hc Hs Hcap Hown1] as ⟨%stk2, %R, %Q, %nl2, Hw, Hc, Hs, Hcap, #Hown2, %Hpost⟩
  · iframe; iframe #
  obtain ⟨hp2, hlo2, -, -, hlast2⟩ := Hpost
  obtain ⟨hbl2, htl2⟩ := hlast2 (fun j pid e hj1 hj2 hj => by simp at hj) htop1
  icases WPrev.leafCnt_lt K tx r true q X n b (wRoot X.v T n) B.ipg nl2 _ _ hctx hp2 hlo2
    $$ [Hw Hown2] with ⟨Hw, %Hc63⟩
  · iframe; iframe #
  have hv : viewWF X.v := hok.2.2.2.2.2.2.2
  have hinv2 := WPrev.lastInv_new nl2 X.v hv (wEs X n) b (wRoot X.v T n) B.ipg _ _ hp2 hlo2
    (WNext.brLast_cnt X.v (wEs X n) _ _ hp2.2.1 hbl2) htl2 Hc63
  ihave IH : (∃ (stk1 : GoSlice) (els1 : List elemRef) (pids1 : List Nat)
        (nl1 : Loc → Option (Loc × Nat)) (ipg1 : List w8),
      "Hw" ∷ wtxWQ K tx r true q X ∗ "Hcc" ∷ c ↦ Cursor.mk b stk1 ∗
      "Hs" ∷ stk1 ↦* els1 ∗ "Hcap" ∷ ownSliceCap elemRef stk1 (DFrac.own 1) ∗
      "Ho" ∷ wStkOwn r nl1 X.v (wRoot X.v T n) ipg1 els1 ∗
      "%Hinv" ∷ ⌜wLastInv nl1 X.v (wEs X n) b (wRoot X.v T n) ipg1 els1 pids1⌝ : IProp GF)
      $$ [Hw Hc Hs Hcap]
  · iexists stk2, _, _, nl2, B.ipg
    simp only [named]
    iframe; iframe #
    ipureintro; exact hinv2
  wp_for IH
  have hinv1 := Hinv
  obtain ⟨hp1, hlo1, -, -⟩ := Hinv
  obtain ⟨E1, e1, hE⟩ : ∃ E e, els1 = E ++ [e] := by
    rcases List.eq_nil_or_concat els1 with h | ⟨L, x, h⟩
    · exact absurd h hp1.1
    · exact ⟨L, x, by simpa using h⟩
  subst hE
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  have hlen : sint.Z stk1.len = ((E1.length + 1 : Nat) : Int) := by
    simp only [List.length_append, List.length_singleton] at Hsl; word
  by_cases hgt : 0 < E1.length
  · rw [decide_eq_true (show sint.Z (W64 1) < sint.Z stk1.len by rw [hlen]; word)]
    wp_auto
    have hidx : sint.Z (stk1.len - W64 1) = (E1.length : Int) := by word
    rw [if_pos (show 0 ≤ sint.Z (stk1.len - W64 1) ∧ sint.Z (stk1.len - W64 1) < sint.Z stk1.len by
      rw [hidx, hlen]; constructor <;> omega)]
    icases ownSlice_elem_acc (sint.Z (stk1.len - W64 1)) e1 _ _ (E1 ++ [e1]) (by omega)
      (by rw [hidx]; simp) $$ Hs with ⟨He, Hsback⟩
    rw [hidx]
    try wp_auto
    icases Ho with #Ho
    wp_apply WFirst.wp_top_count hCnt K tx r true q X n b (wRoot X.v T n) ipg1 nl1 E1 e1 pids1 _
      hctx hp1 hlo1 $$ [Hw He] as ⟨Hw, He, %H63⟩
    · iframe; iframe #
    ihave Hs := Hsback $$ He
    rw [show (E1 ++ [e1]).set (↑E1.length : Int).toNat e1 = E1 ++ [e1] by simp]
    try wp_auto
    by_cases hc0 : leafCnt X.v (wEs X n) pids1 (E1 ++ [e1]) = 0
    · rw [decide_eq_true (show W64 (leafCnt X.v (wEs X n) pids1 (E1 ++ [e1]) : Int) = W64 0 by
        rw [hc0]; rfl)]
      try wp_auto
      rw [if_pos (by simp)]
      wp_auto
      wp_apply hprev K tx r true q X n b (wRoot X.v T n) ipg1 nl1 c stk1 (E1 ++ [e1]) pids1 hctx
        hinv1 (by simp only [List.length_append, List.length_singleton]; omega) hc0
        $$ [Hw Hcc Hs Hcap] as %k0 %vl0 %fl0 ⟨%stk3, %els3, %pids3, %nl3, %ipg3, Hw, Hcc, Hs, Hcap,
          #Ho3, %Hinv3⟩
      · iframe; iframe #
      wp_for_post
      iframe
      iexists stk3, els3, pids3, nl3, ipg3
      simp only [named]
      iframe; iframe #
      ipureintro; exact Hinv3
    · rw [decide_eq_false (show ¬ W64 (leafCnt X.v (wEs X n) pids1 (E1 ++ [e1]) : Int) = W64 0 by
        intro h; apply hc0; have := congrArg BitVec.toNat h; simp at this; omega)]
      try wp_auto
      rw [if_neg (fun h => Bool.false_ne_true (go.intoVal_inj (of_decide_eq_true h))),
        if_pos (by simp)]
      have hex : (E1 ++ [e1]).length ≤ 1 ∨ leafCnt X.v (wEs X n) pids1 (E1 ++ [e1]) ≠ 0 :=
        Or.inr hc0
      obtain ⟨hkvpre, hidxE, hcur⟩ := WLastPub.last_exit nl1 X.v (wEs X n) b (wRoot X.v T n) ipg1 _
        pids1 hinv1 hex
      wp_auto
      rw [decide_eq_false (show stk1.len ≠ W64 0 by
        intro h; rw [h] at hlen; simp at hlen; omega)]
      wp_auto
      wp_apply hkv K tx r true q X n b (wRoot X.v T n) ipg1 nl1 c stk1 (E1 ++ [e1]) pids1 hctx hp1 hlo1
        hkvpre $$ [Hw Hcc Hs] as %k %vl %fl ⟨Hw, Hcc, Hs, #Hkv⟩
      · iframe; iframe #
      rw [hidxE]
      icases wEntKV_curAt γ tx r X (wEs X n) _ k vl fl $$ [Hkv] with ⟨#Hca, %Hfl⟩
      · iframe #
      try wp_auto
      rw [decide_eq_true (hand fl Hfl)]
      simp only [Bool.not_true]
      wp_auto
      iapply HΦ
      ihave Hfin := Hcl $$ %stk1 %(E1 ++ [e1]) %nl1 %ipg1 %(some ((wEs X n).length - 1)) Hw Hcc Hs
        Hcap Ho
      ihave Hfin := Hfin $$ []
      · ipureintro; exact hcur
      icases Hfin with ⟨Ht, Hc⟩
      iframe; iframe #
  · rw [decide_eq_false (show ¬ sint.Z (W64 1) < sint.Z stk1.len by rw [hlen]; word)]
    wp_auto
    rw [if_neg (fun h => Bool.false_ne_true (go.intoVal_inj (of_decide_eq_true h))),
      if_pos (by simp)]
    have hex : (E1 ++ [e1]).length ≤ 1 ∨ leafCnt X.v (wEs X n) pids1 (E1 ++ [e1]) ≠ 0 :=
      Or.inl (by simp only [List.length_append, List.length_singleton]; omega)
    icases Ho with #Ho
    obtain ⟨hkvpre, hidxE, hcur⟩ := WLastPub.last_exit nl1 X.v (wEs X n) b (wRoot X.v T n) ipg1 _
      pids1 hinv1 hex
    wp_auto
    rw [decide_eq_false (show stk1.len ≠ W64 0 by
      intro h; rw [h] at hlen; simp at hlen; omega)]
    wp_auto
    icases Ho with #Ho
    wp_apply hkv K tx r true q X n b (wRoot X.v T n) ipg1 nl1 c stk1 (E1 ++ [e1]) pids1 hctx hp1 hlo1
      hkvpre $$ [Hw Hcc Hs] as %k %vl %fl ⟨Hw, Hcc, Hs, #Hkv⟩
    · iframe; iframe #
    rw [hidxE]
    icases wEntKV_curAt γ tx r X (wEs X n) _ k vl fl $$ [Hkv] with ⟨#Hca, %Hfl⟩
    · iframe #
    try wp_auto
    rw [decide_eq_true (hand fl Hfl)]
    simp only [Bool.not_true]
    wp_auto
    iapply HΦ
    ihave Hfin := Hcl $$ %stk1 %(E1 ++ [e1]) %nl1 %ipg1 %(some ((wEs X n).length - 1)) Hw Hcc Hs
      Hcap Ho
    ihave Hfin := Hfin $$ []
    · ipureintro; exact hcur
    icases Hfin with ⟨Ht, Hc⟩
    iframe; iframe #

end pubWLast

end bbolt
end EtcdGrove
end Perennial
