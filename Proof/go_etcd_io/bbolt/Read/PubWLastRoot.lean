/-
The root reference of a writer's `Last` (U6aa, `notes/bbolt-proof-plan.md`, "Writer reads at a
fraction"): the reference `pageNode` returns at the bucket's root id, its count (its logical entries
`ws`, `wp_root_count`), and at index `count - 1` a one-element stack prefix whose leaf page, once a
path, holds its entries, at its last index (`root_last`: `last_w`'s premises and the `sTopLast` its
post carries over).
-/
module

public import Proof.go_etcd_io.bbolt.Read.WFirstRoot
public import Proof.go_etcd_io.bbolt.Read.WFirstCount
public import Proof.go_etcd_io.bbolt.Read.WLastPure

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

namespace WLastPub

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common Write WBridge
  WGoFirst

section pure
variable [GooseExts]

/-- **The root reference's logical entries**: a node reference is a live node with them, a page
reference the page `wpageAt` names (its bytes at least a header). -/
theorem root_ws (X : WX) (n : GoString) (bl : Loc) (rt : Nat) (B : BRec)
    (hc : wCurCtx X n bl rt) (hB : X.t.bs !! bl = some B) (hbase : 0 < X.v.base.addr)
    (p nd : Loc)
    (hpn : match resolve B B.ib.root' with
      | some l => p = null ∧ nd = l
      | none => nd = null ∧ ∃ pg2, wpageAt X.v B B.ib.root' = some (p, pg2)) :
    ∃ lf ws, ltree X bl B.ib.root' = some (lf, ws) ∧
      (∀ i, refAt X bl B.ib.root' ⟨p, nd, i⟩) ∧
      (nd ≠ null → ∃ rn, B.ns !! nd = some rn ∧ nd ∈ X.live ∧ rn.ws = ws) ∧
      (nd = null → resolve B B.ib.root' = none ∧ ∃ pg, wpageAt X.v B B.ib.root' = some (p, pg) ∧
        ws = pageWs pg ∧ 16 ≤ pg.length) := by
  have hok := hc.1
  have hv : viewWF X.v := hok.2.2.2.2.2.2.2
  have hcl := wOK_bktClean X hok bl B hB
  cases hr : resolve B B.ib.root' with
  | some l =>
    rw [hr] at hpn
    have hnm : B.nm !! B.ib.root' = some l := by
      by_cases h0 : B.ib.root' = W64 0
      · unfold resolve at hr; rw [if_pos h0] at hr
        by_cases hrn : B.bv.rootNode' = null
        · rw [if_pos hrn] at hr; cases hr
        · rw [if_neg hrn] at hr; cases hr; exact hcl.2.2.2.1 hrn
      · rw [← resolve_tree B _ h0]; exact hr
    obtain ⟨hlnn, r, hr', -⟩ := hcl.2.2.2.2.1 _ l hnm
    refine ⟨r.nv.isLeaf', r.ws, ltree_node X bl B _ l r hB hr hr',
      fun i => refAt_node X bl B _ l _ hB hr hpn.2, fun _ => ⟨r, by rw [hpn.2]; exact hr', ?_, rfl⟩,
      fun h => absurd (hpn.2 ▸ h) hlnn⟩
    rw [hpn.2]; exact wOK_nsLive X hok bl B _ r hB hr'
  | none =>
    rw [hr] at hpn
    obtain ⟨hnn, pg', hw⟩ := hpn
    have hL := ltree_page X bl B _ _ pg' hB hr hw
    refine ⟨_, _, hL, fun i => refAt_page X bl B _ pg' _ hB hr hnn hw, fun h => absurd hnn h,
      fun _ => ⟨rfl, pg', hw, rfl, ?_⟩⟩
    by_cases h0 : B.ib.root' = W64 0
    · obtain ⟨-, -, -, -, P5⟩ := pos_facts X bl B hok hB hc.2.2.1 hbase _ ⟨p, nd, W64 0⟩ _ _
        (refAt_page X bl B _ pg' _ hB hr hnn hw) hL (fun h => h)
      obtain ⟨pg, hlp, -, hig⟩ := P5 hnn
      have ht0 : B.ib.root'.toNat = 0 := by rw [h0]; rfl
      unfold leafPgAt at hlp; rw [if_pos ht0] at hlp; cases hlp
      unfold wpageAt at hw; rw [if_pos h0, if_pos h0] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.2]
      exact (hig ht0).2.2.2.1
    · unfold wpageAt at hw; rw [if_neg h0] at hw
      obtain ⟨pg0, hpg, e⟩ := Option.map_eq_some_iff.1 hw
      simp only [Prod.mk.injEq] at e
      obtain ⟨-, rfl⟩ := e
      have := (Read.viewWF_page _ hv _ _ hpg).2.2.1
      omega

/-- **The root reference at its last index** (what `Last` pushes on the emptied stack, its count's
entries `ws`): a one-element prefix (a branch's index on its last entry) whose leaf page, once a
path, holds its entries, at its last index (`sTopLast`; `-1` in an empty leaf). -/
theorem root_last (X : WX) (n : GoString) (bl : Loc) (rt : Nat) (B : BRec)
    (hc : wCurCtx X n bl rt) (hB : X.t.bs !! bl = some B) (hbase : 0 < X.v.base.addr)
    (p nd : Loc) (lf : Bool) (ws : List WEntry) (hL : ltree X bl B.ib.root' = some (lf, ws))
    (hra : ∀ i, refAt X bl B.ib.root' ⟨p, nd, i⟩) (hwl : ws.length < 2 ^ 63) :
    sPrefix (nlX X) X.v bl rt [⟨p, nd, W64 ((ws.length : Int) - 1)⟩] [rt] ∧
    (sPathR (nlX X) X.v bl rt [⟨p, nd, W64 ((ws.length : Int) - 1)⟩] [rt] →
      sLeafOK X.v B.ipg (wEs X n) [rt] [⟨p, nd, W64 ((ws.length : Int) - 1)⟩]) ∧
    sTopLast X.v (wEs X n) [rt] [⟨p, nd, W64 ((ws.length : Int) - 1)⟩] := by
  have hok := hc.1
  have hv : viewWF X.v := hok.2.2.2.2.2.2.2
  have hrt := WFirst.root_rt X n bl rt B hc hB
  obtain ⟨P1, P2, P3, P4, P5⟩ := pos_facts X bl B hok hB hc.2.2.1 hbase _
    ⟨p, nd, W64 ((ws.length : Int) - 1)⟩ lf ws (hra _) hL (fun h => h)
  rw [hrt] at P1 P2 P3 P4 P5
  have hidx : ∀ k : Nat, k ≠ 0 → k < 2 ^ 63 → (W64 ((k : Int) - 1)).toNat + 1 = k := by
    intro k hk hk'
    have : (W64 ((k : Int) - 1)).toNat = k - 1 := by
      rw [show ((k : Int) - 1) = ((k - 1 : Nat) : Int) by omega]
      exact W64_toNat_lt _ (by omega)
    omega
  have hpre : sPrefix (nlX X) X.v bl rt [⟨p, nd, W64 ((ws.length : Int) - 1)⟩] [rt] := by
    refine ⟨by simp, rfl, rfl, fun j e0 p0 h1 h2 => ?_⟩
    cases j with
    | succ j => simp at h1
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2
      subst h1; subst h2
      refine ⟨P1, P2, fun hj => by simp at hj, fun _ => ?_⟩
      cases lf with
      | false =>
        obtain ⟨pg', hpg', hb', hwl', -⟩ := P3 rfl
        obtain ⟨_, hbw⟩ := viewWF_branchWF _ hv _ _ hpg' hb'
        refine Or.inr ⟨pg', hpg', Or.inr ⟨hb', ?_⟩⟩
        have h0 : 0 < pageCount pg' := hbw.1
        have := hidx ws.length (by omega) hwl
        show (W64 ((ws.length : Int) - 1)).toNat < pageCount pg'
        omega
      | true =>
        rcases P4 rfl with h | ⟨pg', hpg', hl'⟩
        · exact Or.inl h
        · exact Or.inr ⟨pg', hpg', Or.inl hl'⟩
  have hlast : ([⟨p, nd, W64 ((ws.length : Int) - 1)⟩] : List elemRef).getLast? =
      some ⟨p, nd, W64 ((ws.length : Int) - 1)⟩ := by simp
  have hplast : ([rt] : List Nat).getLast? = some rt := by simp
  have hrw : (W64 (rt : Int)) = B.ib.root' := by rw [← hrt]; exact w64_cast_toNat _
  refine ⟨hpre, fun hpath => ?_, fun e0 p0 h1 h2 => ?_⟩
  · intro e0 p0 h1 h2 hnull
    rw [hlast] at h1; cases h1
    rw [hplast] at h2; cases h2
    obtain ⟨ws0, hL0, hents, -, hplain, -⟩ :=
      wStk_top X n bl rt B hc hB hbase (nlX X) _ _ hpath (fun _ _ _ => rfl) _ rt hlast hplast
    rw [hrw, hL] at hL0
    simp only [Option.some.injEq, Prod.mk.injEq] at hL0
    obtain ⟨-, rfl⟩ := hL0
    obtain ⟨pg', hlp, hws, hig⟩ := P5 hnull
    exact ⟨pg', hlp, by rw [← hws]; exact hplain, by unfold pgEnts; rw [← hws]; exact hents, hig⟩
  · rw [hlast] at h1; cases h1
    rw [hplast] at h2; cases h2
    cases lf with
    | false =>
      obtain ⟨pg', hpg', hb', hwl', -⟩ := P3 rfl
      obtain ⟨_, hbw⟩ := viewWF_branchWF _ hv _ _ hpg' hb'
      have h0 : 0 < pageCount pg' := hbw.1
      left
      refine ⟨pg', hpg', hb', ?_⟩
      have := hidx ws.length (by omega) hwl
      show (W64 ((ws.length : Int) - 1)).toNat + 1 = pageCount pg'
      omega
    | true =>
      right
      have hpath : sPathR (nlX X) X.v bl rt [⟨p, nd, W64 ((ws.length : Int) - 1)⟩] [rt] :=
        sPrefix_sPathR _ _ _ _ _ _ hpre (fun e1 p1 h1 h2 => by
          rw [hplast] at h2; cases h2
          rcases P4 rfl with h | h
          · exact Or.inl h
          · exact Or.inr h)
      obtain ⟨ws0, hL0, -, hcnt0, -, -⟩ :=
        wStk_top X n bl rt B hc hB hbase (nlX X) _ _ hpath (fun _ _ _ => rfl) _ rt hlast hplast
      rw [hrw, hL] at hL0
      simp only [Option.some.injEq, Prod.mk.injEq] at hL0
      obtain ⟨-, rfl⟩ := hL0
      refine ⟨?_, ?_⟩
      · rcases P4 rfl with h | h
        · exact Or.inl h
        · exact Or.inr h
      · exact congrArg (fun k : Nat => W64 ((k : Int) - 1)) hcnt0

end pure

section iprop
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **The root reference's count**: its logical entries' number, below `2 ^ 63`. -/
theorem wp_root_count
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG))
    (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX) (n : GoString) (bl : Loc)
    (rt : Nat) (B : BRec) (hc : wCurCtx X n bl rt) (hB : X.t.bs !! bl = some B)
    (hmax : ∀ id pg, X.v.pages !! id = some pg → id * 4096 < 0xFFFFFFFFFFFF)
    (p nd : Loc) (ws : List WEntry)
    (hnode : nd ≠ null → ∃ rn, B.ns !! nd = some rn ∧ nd ∈ X.live ∧ rn.ws = ws)
    (hpage : nd = null → resolve B B.ib.root' = none ∧ ∃ pg,
      wpageAt X.v B B.ib.root' = some (p, pg) ∧ ws = pageWs pg ∧ 16 ≤ pg.length)
    (ptr : Loc) (i : w64) :
  {{ wtxWQ (GF := GF) K tx r m q X ∗ ptr ↦ (⟨p, nd, i⟩ : elemRef) }}
    (App (Val (ptr @!! go.GoType.PointerType elemRef.ty @!! go!"count")) (Val #()))
  {{ RET #(W64 (ws.length : Int)); wtxWQ K tx r m q X ∗ ptr ↦ (⟨p, nd, i⟩ : elemRef) ∗
      ⌜ws.length < 2 ^ 63⌝ }} := by
  have hlive : bl ∈ X.liveB := hc.1.2.2.2.2.2.1.2.2.1 bl B hB
  iintro %Φ ⟨Hw, He⟩ HΦ
  by_cases hnn : nd = null
  · obtain ⟨hres, pg, hw, hws, h16⟩ := hpage hnn
    obtain ⟨pa, pg', hw', hsrc, hpa, -⟩ := WFirst.root_pn_pre X n bl rt B hc hB hmax hres
    rw [hw] at hw'
    simp only [Option.some.injEq, Prod.mk.injEq] at hw'
    obtain ⟨rfl, rfl⟩ := hw'
    icases wtxWQ_page_srcLoc K tx r m q X bl B B.ib.root' p pg hB hlive hw hsrc hpa $$ Hw
      with ⟨Hw, #Hsrc⟩
    wp_apply WFirst.wp_count_page hCnt K tx r m q X ptr ⟨p, nd, i⟩ (pgSrc B) pg hnn h16
      $$ [Hw He] as ⟨Hw, He⟩
    · iframe; iframe #
    have hl : ws.length = pageCount pg := by rw [hws, pageWs_length]
    rw [hl]
    iapply HΦ
    iframe
    ipureintro
    have : pageCount pg < 2 ^ 16 := by unfold pageCount; exact BitVec.isLt _
    omega
  · obtain ⟨rn, hrn, hlv, hrws⟩ := hnode hnn
    icases wtxWQ_node_len K tx r m q X bl B _ rn hB hrn hlv $$ Hw with ⟨Hw, %H63⟩
    wp_apply WFirst.wp_count_node K tx r m q X bl B ptr ⟨p, nd, i⟩ rn hB hnn hrn hlv $$ [Hw He]
      as ⟨Hw, He⟩
    · iframe
    rw [hrws]
    iapply HΦ
    iframe
    ipureintro
    rw [← hrws]; exact H63

end iprop

end WLastPub

end bbolt
end EtcdGrove
end Perennial
