/-
U7n (`notes/bbolt-proof-plan.md`): **`DeleteBucket`'s child made dead** (`WX.killBkt`), the ghost
step before `child.nodes = nil`: the child `bl` (record `C`) leaves `X.t.bs` and `X.liveB` for
`X.t.deadB` (its record without nodes), its nodes move to the dead nodes `X.t.dead` (their
objects and registrations kept: `objs_killBkt`; out of `live`), and its live page ownership is dropped.
-/
module

public import Proof.go_etcd_io.bbolt.Write.WalkDead

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

namespace Write

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

/-- `X` with bucket `bl` (record `C`) dead: out of `bs` and `liveB`, in `deadB` without nodes,
its nodes dead. -/
def _root_.Perennial.EtcdGrove.bbolt.WX.killBkt (X : WX) (bl : Loc) (C : BRec) : WX :=
  { X with
    t := { X.t with bs := GMap.delete bl X.t.bs,
                    dead := (C.ns.fmap fun r => (bl, r)) ∪ X.t.dead,
                    deadB := X.t.deadB.insert bl { C with ns := ∅ } },
    live := GMap.filter (fun l _ => (C.ns !! l).isNone) X.live,
    liveB := GMap.delete bl X.liveB }

theorem killBkt_live (X : WX) (bl : Loc) (C : BRec) (l : Loc) :
    l ∈ (X.killBkt bl C).live ↔ l ∈ X.live ∧ C.ns !! l = none := by
  simp only [WX.killBkt, GMap.mem_iff, GMap.lookup_filter]
  cases h : X.live !! l <;> cases h' : C.ns !! l <;> simp [Option.filter]

theorem killBkt_bs (X : WX) (bl : Loc) (C : BRec) (k : Loc) :
    (X.killBkt bl C).t.bs !! k = if bl = k then none else X.t.bs !! k := by
  simp only [WX.killBkt, GMap.lookup_delete_iff]

theorem killBkt_bs_none (X : WX) (bl : Loc) (C : BRec) : (X.killBkt bl C).t.bs !! bl = none := by
  simp only [killBkt_bs, if_true]

theorem killBkt_deadB (X : WX) (bl : Loc) (C : BRec) :
    (X.killBkt bl C).t.deadB !! bl = some { C with ns := ∅ } := by
  simp only [WX.killBkt, GMap.lookup_insert]

theorem killBkt_liveB (X : WX) (bl : Loc) (C : BRec) : bl ∉ (X.killBkt bl C).liveB := by
  simp only [WX.killBkt]
  intro h
  have := (GMap.mem_iff _ _).1 h
  simp only [GMap.lookup_delete_iff, if_true] at this
  cases this

theorem objsDisj_killBkt (X : WX) (bl : Loc) (C : BRec) (hd : objsDisj X.t) :
    objsDisj (X.killBkt bl C).t := by
  intro b B hb n hn b' B' hb' hne
  rw [killBkt_bs] at hb hb'
  split at hb
  · cases hb
  split at hb'
  · cases hb'
  exact hd b B hb n hn b' B' hb' hne

/-- **The node objects are kept** when a bucket's nodes become dead. -/
theorem objs_killBkt (X : WX) (bl : Loc) (C : BRec) (hd : objsDisj X.t)
    (hC : X.t.bs !! bl = some C) : (X.killBkt bl C).t.objs = X.t.objs := by
  apply GMap.map_eq
  intro k
  have hd' := objsDisj_killBkt X bl C hd
  by_cases hk : ∃ b B, X.t.bs !! b = some B ∧ b ≠ bl ∧ (B.ns !! k).isSome
  · obtain ⟨b, B, hb, hne, hks⟩ := hk
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hks
    have hb' : (X.killBkt bl C).t.bs !! b = some B := by
      rw [killBkt_bs, if_neg (Ne.symm hne)]; exact hb
    rw [objs_node _ b B k r hd' hb' hr, objs_node _ b B k r hd hb hr]
  · have hoth : ∀ b B, (X.killBkt bl C).t.bs !! b = some B → B.ns !! k = none := by
      intro b B hb
      rw [killBkt_bs] at hb
      split at hb
      · cases hb
      rename_i hne
      cases h : B.ns !! k with
      | none => rfl
      | some _ => exact absurd ⟨b, B, hb, Ne.symm hne, by simp [h]⟩ hk
    rw [objs_other _ k hoth]
    cases hck : C.ns !! k with
    | some r =>
      rw [objs_node _ bl C k r hd hC hck]
      simp [WTx.deadObjs, WX.killBkt, hck]
    | none =>
      have hoth0 : ∀ b B, X.t.bs !! b = some B → B.ns !! k = none := by
        intro b B hb
        by_cases hbe : b = bl
        · subst hbe; rw [hC] at hb; cases hb; exact hck
        · cases h : B.ns !! k with
          | none => rfl
          | some _ => exact absurd ⟨b, B, hb, hbe, by simp [h]⟩ hk
      rw [objs_other _ k hoth0]
      simp [WTx.deadObjs, WX.killBkt, hck]

/-- The bucket objects: `bl`'s record replaced by its record without nodes. -/
theorem bobjs_killBkt (X : WX) (bl : Loc) (C : BRec) :
    (X.killBkt bl C).t.bobjs = X.t.bobjs.insert bl { C with ns := ∅ } := by
  apply GMap.map_eq
  intro k
  by_cases hk : bl = k
  · subst hk
    simp only [WX.killBkt, WTx.bobjs, GMap.lookup_union, GMap.lookup_delete_iff, GMap.lookup_insert,
      if_true]; rfl
  · simp only [WX.killBkt, WTx.bobjs, GMap.lookup_union, GMap.lookup_delete_iff,
      GMap.lookup_insert_ne _ _ hk, if_neg hk]

end pure

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem heapOK_killBkt (tx : Loc) (X : WX) (bl : Loc) (C : BRec) (hC : X.t.bs !! bl = some C)
    (h : heapOK (GF := GF) tx X) : heapOK (GF := GF) tx (X.killBkt bl C) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hsub : ∀ b B, (X.killBkt bl C).t.bs !! b = some B → X.t.bs !! b = some B := by
    intro b B hb; rw [killBkt_bs] at hb; split at hb
    · cases hb
    · exact hb
  refine ⟨h1, objsDisj_killBkt X bl C h2, fun b B hb => h3 b B (hsub b B hb),
    fun b B n r hb hr => h4 b B n r (hsub b B hb) hr, fun n y hn => ?_,
    fun b B hb => h6 b B (hsub b B hb)⟩
  show ((X.killBkt bl C).t.objs !! n).isSome
  rw [objs_killBkt X bl C h2 hC]
  exact h5 n y hn

/-- **The child made dead** (`WX.killBkt`): `wtxW` at `X.killBkt bl C`, the bucket's live page
ownership dropped. -/
theorem wtxW_killBkt (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc) (C : BRec)
    (hC : X.t.bs !! bl = some C) :
    wtxW (GF := GF) K tx r m X ⊢ wtxW K tx r m (X.killBkt bl C) := by
  iintro Hw
  icases wtxW_open K tx r m X $$ Hw with ⟨-, -, -, Hh, Hv, Hst, Hwback⟩
  unfold wtxHeap
  icases Hh with ⟨%Hok, Hf, Hrf, Hm, Hbk⟩
  have Ho := bobjs_bkt X.t bl C hC
  icases (BigSepM.bigSepM_delete (M := GMap Loc) Ho).1 $$ Hbk with ⟨Hb, Hbk⟩
  iapply Hwback $$ %(X.killBkt bl C) [] [Hf Hrf Hm Hbk Hb] Hv Hst
  · ipureintro; exact ⟨rfl, rfl, rfl⟩
  isplitr
  · ipureintro; exact heapOK_killBkt tx X bl C hC Hok
  isplitl [Hf]
  · unfold txFields WX.killBkt; iexact Hf
  isplitl [Hrf]
  · iexact Hrf
  rw [bobjs_killBkt X bl C, objs_killBkt X bl C Hok.2.1 hC]
  have hv : (X.killBkt bl C).v = X.v := rfl
  simp only [hv]
  isplitl [Hm]
  · iapply (BigSepM.bigSepM_mono_of_forall ?_) $$ Hm
    intro k o
    apply objOwn_weaken
    intro h
    simp only [decide_eq_true_eq] at h ⊢
    exact ((killBkt_live X bl C k).1 h).1
  iapply (BigSepM.bigSepM_insert_delete (M := GMap Loc)).2
  isplitl [Hb]
  · rw [decide_eq_false (killBkt_liveB X bl C)]
    simp only [objOwn]
    icases Hb with ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, -⟩
    iframe
    simp only [Bool.false_eq_true, if_false]
    iempintro
  · iapply (BigSepM.bigSepM_mono (M := GMap Loc)) $$ Hbk
    intro k B hk
    have hne : k ≠ bl := by
      intro e; subst e
      have h0 : Std.get? (Std.delete X.t.bobjs k) k = none := GMap.lookup_delete _ _
      rw [h0] at hk; cases hk
    have hm : (k ∈ (X.killBkt bl C).liveB) ↔ (k ∈ X.liveB) := by
      simp only [WX.killBkt]
      rw [GMap.mem_iff, GMap.mem_iff, GMap.lookup_delete_iff, if_neg (Ne.symm hne)]
    have : decide (k ∈ (X.killBkt bl C).liveB) = decide (k ∈ X.liveB) := decide_eq_decide.2 hm
    rw [this]

end heap

end Write

end bbolt
end EtcdGrove
end Perennial
