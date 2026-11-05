/-
The proof of `Spec/go_etcd_io/bbolt/Cursor__first_w.lean` (U6z/U6aa, `notes/bbolt-proof-plan.md`,
"Writer reads at a fraction"): the stack emptied, the root reference from `Bucket.pageNode_w.specQ`
at the bucket's root id (`Read/WFirstRoot`: a one-element prefix over the writer's registry, its
`wStkOwn`), `goToFirstElementOnTheStack_w` down to a leaf, the top's count (`Read/WFirstTop`), `next_w`
on an empty first leaf, then `keyValue_ws`: entry `0` (`Read/WFirstPos`); the bucket flag branch is
dead (`wEntKV`'s flags plain).
-/
module

public import Spec.go_etcd_io.bbolt.Cursor__first_w
public import Spec.go_etcd_io.bbolt.Bucket__pageNode_w
public import Spec.go_etcd_io.bbolt.Cursor__goToFirstElementOnTheStack_w
public import Spec.go_etcd_io.bbolt.Cursor__next_w
public import Spec.go_etcd_io.bbolt.Cursor__keyValue_ws
public import Spec.go_etcd_io.bbolt.internal.common.InBucket__RootPage
public import Proof.go_etcd_io.bbolt.Read.WFirstRoot
public import Proof.go_etcd_io.bbolt.Read.WFirstTop
public import Proof.go_etcd_io.bbolt.Read.WFirstPos

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

theorem Cursor.first_w.wp_proofQ
    (hpn : Bucket.pageNode_w.specQ (GF := GF) (hG := hG))
    (hg : Cursor.goToFirstElementOnTheStack_w.specQ (GF := GF) (hG := hG))
    (hnx : Cursor.next_w.specQ (GF := GF) (hG := hG))
    (hkv : Cursor.keyValue_ws.specQ (GF := GF) (hG := hG))
    (hRP : internal.common.InBucket.RootPage.spec (GF := GF) (hG := hG))
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG)) :
    Cursor.first_w.specQ (GF := GF) (hG := hG) := by
  intro K tx r m q X n bl rt c stk els hc
  have hok := hc.1
  obtain ⟨B, hB⟩ := PubW.bktLoc_rec X hok n bl hc.2.1
  have hlive : bl ∈ X.liveB := hok.2.2.2.2.2.1.2.2.1 bl B hB
  have hcl := Write.wOK_bktClean X hok bl B hB
  wp_start as ⟨Hw, Hc, Hs, Hcap⟩
  icases wtxWQ_pkgInit K tx r m q X $$ Hw with ⟨Hw, #Hpkg⟩
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  icases (persistent_entails_left (wtxWQ_page_maxMap K tx r m q X)) $$ Hw with ⟨Hw, %Hmax⟩
  icases wtxWQ_cells_acc K tx r m q X $$ Hw with ⟨%Hbase, Hcells0, Hwb0⟩
  ihave Hw := Hwb0 $$ Hcells0
  icases wtxWQ_nodes_nonnull K tx r m q X bl B hB $$ Hw with ⟨Hw, %Hnodes⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  ihave %Hcw := ownSliceCap_wf _ _ $$ Hcap
  wp_auto
  rw [if_pos ⟨by decide, by decide, by word⟩]
  icases ownSlice_slice_with_cap (V := elemRef) (W64 0) (W64 0) stk els
    ⟨by decide, by decide, by word⟩ $$ [Hs Hcap] with ⟨-, Hs, Hcap⟩
  · iframe
  have hsub : subslice (sint.nat (W64 0)) (sint.nat (W64 0)) els = ([] : List elemRef) := by
    simp [subslice]
  rw [hsub]
  wp_auto
  wp_method_call; wp_call
  icases wtxWQ_bkt_acc K tx r m q X bl B hB $$ Hw with ⟨Ho, Hback⟩
  isimp only [objOwn] at Ho
  icases Ho with ⟨HIB, Htx, Hbks, Hpage, Hroot, Hnodes, Hib, Hnm, Hbm, Hpo⟩
  wp_auto
  wp_apply hRP $$ [Hib] as Hib
  · iexact Hib
  ihave Hw := Hback $$ [HIB Htx Hbks Hpage Hroot Hnodes Hib Hnm Hbm Hpo]
  · isimp only [objOwn]; iframe
  have hpre := WFirst.root_pn_pre X n bl rt B hc hB Hmax
  wp_apply hpn K tx r m q X bl B B.ib.root' hB hlive (fun h => h) (fun h => absurd h Hnodes)
    (fun c l h => (hcl.2.2.2.2.1 c l h).1)
    (fun h => by obtain ⟨pa, pg, h1, h2, -, h4⟩ := hpre h; exact ⟨pa, pg, h1, h2, h4⟩) $$ [Hw]
    as %p %nd ⟨Hw, %Hpn⟩
  · iframe
  try wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl', -⟩
  wp_apply wp_slice_append $$ [$Hs $Hcap $Hsl'] as %s1 ⟨Hs, Hcap, -⟩
  try wp_auto
  obtain ⟨hpre1, hlok1, hnl1⟩ := WFirst.root_push X n bl rt B hc hB Hbase ⟨p, nd, W64 0⟩ rfl Hpn
  icases WFirst.root_own K tx r m q X n bl rt B hc hB Hmax ⟨p, nd, W64 0⟩ hnl1 Hpn $$ Hw
    with ⟨Hw, #Hown⟩
  wp_apply hg K tx r m q X n bl rt B.ipg (WGoFirst.nlX X) c s1 [⟨p, nd, W64 0⟩] [rt] hc hpre1 hlok1
    $$ [Hw Hc Hs Hcap Hown] as ⟨%stk2, %R, %Q, %nl2, Hw, Hc, Hs, Hcap, #Hown2, %Hpost⟩
  · iframe; iframe #
  obtain ⟨hp2, hlo2, hall2⟩ := Hpost
  have hallF : sAllFirst ([⟨p, nd, W64 0⟩] ++ R) := by
    intro x hx
    rcases List.mem_append.1 hx with h | h
    · simp at h; subst h; rfl
    · exact hall2 x h
  generalize [⟨p, nd, W64 0⟩] ++ R = E at hp2 hlo2 hallF ⊢
  generalize [rt] ++ Q = P at hp2 hlo2
  obtain ⟨els0, e2, rfl⟩ : ∃ els0 e2, E = els0 ++ [e2] := by
    rcases List.eq_nil_or_concat E with h | ⟨L, b, h⟩
    · exact absurd h hp2.1
    · exact ⟨L, b, by simpa using h⟩
  ihave %Hsl2 := ownSlice_len _ _ _ $$ Hs
  try wp_auto
  have hidx' : sint.Z (stk2.len - W64 1) = (els0.length : Int) := by
    simp only [List.length_append, List.length_singleton] at Hsl2; word
  rw [if_pos (show 0 ≤ sint.Z (stk2.len - W64 1) ∧ sint.Z (stk2.len - W64 1) < sint.Z stk2.len by
    rw [hidx']; simp only [List.length_append, List.length_singleton] at Hsl2; word)]
  icases ownSlice_elem_acc (sint.Z (stk2.len - W64 1)) e2 _ _ (els0 ++ [e2]) (by omega)
    (by rw [hidx']; simp) $$ Hs with ⟨He, Hsback⟩
  rw [hidx']
  try wp_auto
  wp_apply WFirst.wp_top_count hCnt K tx r m q X n bl rt B.ipg nl2 els0 e2 P _ hc hp2 hlo2
    $$ [Hw He] as ⟨Hw, He, %H63⟩
  · iframe; iframe #
  ihave Hs := Hsback $$ He
  rw [show (els0 ++ [e2]).set (↑els0.length : Int).toNat e2 = els0 ++ [e2] by simp]
  try wp_auto
  by_cases hc0 : leafCnt X.v (wEs X n) P (els0 ++ [e2]) = 0
  · rw [decide_eq_true (show W64 (leafCnt X.v (wEs X n) P (els0 ++ [e2]) : Int) = W64 0 by
      rw [hc0]; rfl)]
    wp_auto
    obtain ⟨hwstk, hnext⟩ := WFirst.first_next nl2 X.v (wEs X n) bl rt B.ipg _ P hp2 hlo2 hallF hc0
    wp_apply hnx K tx r m q X n bl rt B.ipg nl2 c stk2 (els0 ++ [e2]) P hc hwstk
      $$ [Hw Hc Hs Hcap] as %k0 %vl0 %fl0 ⟨%stk3, %els3, %nl3, Hw, Hc, Hs, Hcap, #Hown3, %Hnp, -⟩
    · iframe; iframe #
    obtain ⟨pids3, hp3, hlo3, hpre3, hcur3, hidx3⟩ := hnext nl3 els3 Hnp
    try wp_auto
    wp_apply hkv K tx r m q X n bl rt B.ipg nl3 c stk3 els3 pids3 hc hp3 hlo3 hpre3
      $$ [Hw Hc Hs] as %k %vl %fl ⟨Hw, Hc, Hs, #Hkv⟩
    · iframe; iframe #
    rw [hidx3]
    ihave %Hfl := WFirst.wEntKV_flag _ _ _ _ _ _ $$ Hkv
    try wp_auto
    rw [decide_eq_true Hfl]
    simp only [Bool.not_true]
    wp_auto
    iapply HΦ
    iexists stk3, els3, nl3, B.ipg
    iframe; iframe #
    ipureintro; exact hcur3
  · rw [decide_eq_false (show ¬ W64 (leafCnt X.v (wEs X n) P (els0 ++ [e2]) : Int) = W64 0 by
      intro h; apply hc0; have := congrArg BitVec.toNat h; simp at this; omega)]
    wp_auto
    obtain ⟨hcur2, hidx2, hpre2⟩ := WFirst.first_landed nl2 X.v (wEs X n) bl rt B.ipg _ P hp2 hlo2
      hallF hc0
    wp_apply hkv K tx r m q X n bl rt B.ipg nl2 c stk2 (els0 ++ [e2]) P hc hp2 hlo2 hpre2
      $$ [Hw Hc Hs] as %k %vl %fl ⟨Hw, Hc, Hs, #Hkv⟩
    · iframe; iframe #
    rw [hidx2]
    ihave %Hfl := WFirst.wEntKV_flag _ _ _ _ _ _ $$ Hkv
    try wp_auto
    rw [decide_eq_true Hfl]
    simp only [Bool.not_true]
    wp_auto
    iapply HΦ
    iexists stk2, els0 ++ [e2], nl2, B.ipg
    iframe; iframe #
    ipureintro; exact hcur2

end proof

end bbolt
end EtcdGrove
end Perennial
