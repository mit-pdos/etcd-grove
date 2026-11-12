/-
The root reference of a writer's cursor (U6aa, `notes/bbolt-proof-plan.md`, "Writer reads at a
fraction"; for `Cursor.first_w`): `pageNode`'s premises at the bucket's root id, and the reference
it returns there, at index `0`, as a one-element stack prefix (`sPrefix`) over the writer's registry
(`nlX`), whose leaf page, once a path, holds its entries (`sLeafOK` with the bucket's inline page),
with its registry fragment and inline page bytes (`wStkOwn`).
-/
module

public import Proof.go_etcd_io.bbolt.Read.WGoFirst
public import Proof.go_etcd_io.bbolt.Read.WSearch
public import Proof.go_etcd_io.bbolt.Read.PubWGet

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace WFirst

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common Write WBridge
  WGoFirst

section pure
variable [GooseExts]

/-- **`pageNode`'s page premise at the bucket's root id** (and the inline page's location). -/
theorem root_pn_pre (X : WX) (n : GoString) (bl : Loc) (rt : Nat) (B : BRec)
    (hc : wCurCtx X n bl rt) (hB : X.t.bs !! bl = some B)
    (hmax : ∀ id pg, X.v.pages !! id = some pg → id * 4096 < 0xFFFFFFFFFFFF) :
    resolve B B.ib.root' = none → ∃ pa pg, wpageAt X.v B B.ib.root' = some (pa, pg) ∧
      (B.ib.root' = W64 0 → B.pst = PageSt.view ∨ ∃ dq, B.isrc = Src.own dq) ∧
      (B.ib.root' = W64 0 → B.bv.page' ≠ null) ∧
      (B.ib.root' ≠ W64 0 → X.t.pm !! B.ib.root' = none ∧ 16 ≤ pg.length ∧
        pageId pg = B.ib.root'.toNat ∧
        (pageFlags pg = branchPageFlag ∨ pageFlags pg = leafPageFlag) ∧
        B.ib.root'.toNat * 4096 < 0xFFFFFFFFFFFF) := by
  intro hres
  have hloc := PubW.bktLocalOK_of_wOK X hc.1 bl B hB
  rcases posOK_root X bl B hloc hB with ⟨l, rn, h, -⟩ | h | h
  · rw [hres] at h; cases h
  all_goals
    obtain ⟨-, pa, pg, hw, -, h1, h2, h3, -⟩ := posOK_page_facts X bl B B.ib.root' hB hloc
      (PubW.pmFresh_of_wOK X hc.1) (inlSrcOK_of_bktLocalOK X bl hloc) hmax (by
        first
        | exact Or.inl h
        | exact Or.inr h)
    exact ⟨pa, pg, hw, h1, h2, h3⟩

/-- The root id as a position. -/
theorem root_rt (X : WX) (n : GoString) (bl : Loc) (rt : Nat) (B : BRec)
    (hc : wCurCtx X n bl rt) (hB : X.t.bs !! bl = some B) : B.ib.root'.toNat = rt := by
  have := hc.2.2.2.1; simpa [WX.rootPid, hB] using this

/-- **The root reference at index `0`** (what `first` pushes on the emptied stack). -/
theorem root_push (X : WX) (n : GoString) (bl : Loc) (rt : Nat) (B : BRec)
    (hc : wCurCtx X n bl rt) (hB : X.t.bs !! bl = some B) (hbase : 0 < X.v.base.addr)
    (e : elemRef) (hi : e.index' = W64 0)
    (hpn : match resolve B B.ib.root' with
      | some l => e.page' = null ∧ e.node' = l
      | none => e.node' = null ∧ ∃ pg2, wpageAt X.v B B.ib.root' = some (e.page', pg2)) :
    sPrefix (nlX X) X.v bl rt [e] [rt] ∧
    (sPathR (nlX X) X.v bl rt [e] [rt] → sLeafOK X.v B.ipg (wEs X n) [rt] [e]) ∧
    (e.node' ≠ null → X.nloc !! e.node' = some (bl, rt)) := by
  have hok := hc.1
  have hv : viewWF X.v := hok.2.2.2.2.2.2.2
  have hcl := wOK_bktClean X hok bl B hB
  have hrt := root_rt X n bl rt B hc hB
  obtain ⟨lf, ws, hra, hL⟩ : ∃ lf ws, refAt X bl B.ib.root' e ∧
      ltree X bl B.ib.root' = some (lf, ws) := by
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
      obtain ⟨-, r, hr', -⟩ := hcl.2.2.2.2.1 _ l hnm
      exact ⟨r.nv.isLeaf', r.ws, refAt_node X bl B _ l e hB hr hpn.2, ltree_node X bl B _ l r hB hr hr'⟩
    | none =>
      rw [hr] at hpn
      obtain ⟨hnn, pg', hw⟩ := hpn
      exact ⟨_, _, refAt_page X bl B _ pg' e hB hr hnn hw, ltree_page X bl B _ _ pg' hB hr hw⟩
  obtain ⟨P1, P2, P3, P4, P5⟩ := pos_facts X bl B hok hB hc.2.2.1 hbase _ e lf ws hra hL
    (fun h => h)
  rw [hrt] at P1 P2 P3 P4 P5
  refine ⟨⟨by simp, rfl, rfl, fun j e0 p0 h1 h2 => ?_⟩, fun hpath => ?_, P1⟩
  · cases j with
    | succ j => simp at h1
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2
      subst h1; subst h2
      refine ⟨P1, P2, fun hj => by simp at hj, fun _ => ?_⟩
      cases lf with
      | false =>
        obtain ⟨pg', hpg', hb', -⟩ := P3 rfl
        obtain ⟨_, hbw⟩ := viewWF_branchWF _ hv _ _ hpg' hb'
        refine Or.inr ⟨pg', hpg', Or.inr ⟨hb', ?_⟩⟩
        rw [hi]; exact hbw.1
      | true =>
        rcases P4 rfl with h | ⟨pg', hpg', hl'⟩
        · exact Or.inl h
        · exact Or.inr ⟨pg', hpg', Or.inl hl'⟩
  · intro e0 p0 h1 h2 hnull
    simp only [List.getLast?_singleton, Option.some.injEq] at h1 h2
    subst h1; subst h2
    obtain ⟨ws0, hL0, hents, -, hplain, -⟩ :=
      wStk_top X n bl rt B hc hB hbase (nlX X) _ _ hpath (fun _ _ _ => rfl) e rt (by simp) (by simp)
    have hrw : (W64 (rt : Int)) = B.ib.root' := by rw [← hrt]; exact w64_cast_toNat _
    rw [hrw, hL] at hL0
    simp only [Option.some.injEq, Prod.mk.injEq] at hL0
    obtain ⟨-, rfl⟩ := hL0
    obtain ⟨pg', hlp, hws, hig⟩ := P5 hnull
    exact ⟨pg', hlp, by rw [← hws]; exact hplain, by unfold pgEnts; rw [← hws]; exact hents, hig⟩

end pure

section iprop
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

theorem srcLoc_locOwn (v : View) (p : Loc) (s : Src) (bs : List w8) :
    srcLoc (GF := GF) v p s bs ⊢ locOwn v p bs := by
  unfold srcLoc locOwn
  cases s with
  | view => iintro %H; ileft; ipureintro; exact H
  | own dq => iintro #H; iright; iexact H
  | stale => iintro %H; exact H.elim

/-- **The root reference's persistent part** (`wStkOwn`): its registry fragment, its inline page's
bytes. -/
theorem root_own (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX) (n : GoString)
    (bl : Loc) (rt : Nat) (B : BRec) (hc : wCurCtx X n bl rt) (hB : X.t.bs !! bl = some B)
    (hmax : ∀ id pg, X.v.pages !! id = some pg → id * 4096 < 0xFFFFFFFFFFFF) (e : elemRef)
    (hnl : e.node' ≠ null → X.nloc !! e.node' = some (bl, rt))
    (hpn : match resolve B B.ib.root' with
      | some l => e.page' = null ∧ e.node' = l
      | none => e.node' = null ∧ ∃ pg2, wpageAt X.v B B.ib.root' = some (e.page', pg2)) :
    wtxWQ (GF := GF) K tx r m q X ⊢ wtxWQ K tx r m q X ∗ wStkOwn r (nlX X) X.v rt B.ipg [e] := by
  have hrt := root_rt X n bl rt B hc hB
  have hlive : bl ∈ X.liveB := hc.1.2.2.2.2.2.1.2.2.1 bl B hB
  unfold wStkOwn
  have hI : wInlOwn (GF := GF) X.v rt B.ipg [e] =
      (if rt = 0 ∧ e.node' = null then locOwn X.v e.page' B.ipg else iprop(emp)) := rfl
  rw [hI]
  by_cases hnn : e.node' = null
  · have hres : resolve B B.ib.root' = none := by
      cases hr : resolve B B.ib.root' with
      | none => rfl
      | some l =>
        rw [hr] at hpn
        exfalso; apply (show l ≠ null from ?_); rw [← hpn.2]; exact hnn
        have hcl := wOK_bktClean X hc.1 bl B hB
        by_cases h0 : B.ib.root' = W64 0
        · unfold resolve at hr; rw [if_pos h0] at hr
          by_cases hrn : B.bv.rootNode' = null
          · rw [if_pos hrn] at hr; cases hr
          · rw [if_neg hrn] at hr; cases hr; exact hrn
        · rw [resolve_tree B _ h0] at hr; exact (hcl.2.2.2.2.1 _ l hr).1
    rw [hres] at hpn
    obtain ⟨-, pg2, hw⟩ := hpn
    have hnl0 : nodeLoc (GF := GF) r (nlX X) e = iprop(emp) := by unfold nodeLoc; rw [if_pos hnn]
    by_cases hr0 : rt = 0
    · have h0 : B.ib.root' = W64 0 := by
        apply BitVec.eq_of_toNat_eq; rw [hrt, hr0]; rfl
      obtain ⟨pa, pg, hw', hsrc, hpa, -⟩ := root_pn_pre X n bl rt B hc hB hmax hres
      have hpg : pg2 = B.ipg := by
        unfold wpageAt at hw; rw [if_pos h0, if_pos h0] at hw
        simp only [Option.some.injEq, Prod.mk.injEq] at hw; exact hw.2.symm
      subst hpg
      rw [if_pos ⟨hr0, hnn⟩]
      iintro Hw
      icases wtxWQ_page_srcLoc K tx r m q X bl B B.ib.root' e.page' B.ipg hB hlive hw hsrc hpa $$ Hw
        with ⟨Hw, #Hs⟩
      iframe Hw
      isplitl
      · iapply (BigSepL.bigSepL_cons (Φ := fun _ e => nodeLoc (GF := GF) r (nlX X) e)).2
        rw [hnl0]
        isplitl
        · iempintro
        · iapply BigSepL.bigSepL_nil.2; iempintro
      · iapply srcLoc_locOwn $$ Hs
    · rw [if_neg (fun h => hr0 h.1)]
      iintro Hw
      iframe Hw
      isplitl
      · iapply (BigSepL.bigSepL_cons (Φ := fun _ e => nodeLoc (GF := GF) r (nlX X) e)).2
        rw [hnl0]
        isplitl
        · iempintro
        · iapply BigSepL.bigSepL_nil.2; iempintro
      · iempintro
  · rw [if_neg (fun h => hnn h.2)]
    iintro Hw
    icases wtxWQ_nlFrag K tx r m q X e.node' (bl, rt) (hnl hnn) $$ Hw with ⟨Hw, #Hf⟩
    iframe Hw
    isplitl
    · iapply (BigSepL.bigSepL_cons (Φ := fun _ e => nodeLoc (GF := GF) r (nlX X) e)).2
      isplitl
      · unfold nodeLoc; rw [if_neg hnn]
        iexists (bl, rt); iframe #; ipureintro; exact hnl hnn
      · iapply BigSepL.bigSepL_nil.2; iempintro
    · iempintro

end iprop

end WFirst

end bbolt
end EtcdGrove
end Perennial
