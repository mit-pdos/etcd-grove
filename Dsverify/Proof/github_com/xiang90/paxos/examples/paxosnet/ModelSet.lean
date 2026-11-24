/-
The register's porcupine model, pure (notes/dsv-paxos.md): `step` (kit.go) on the model's state
`(Known, Val, Pend)` is the pending-writes model's step on the set of configurations the state stands
for (`woSet`, `Kit.lean`): `stepG_pSeq`. The sets are closed under late effects (`silent_K`,
`silent_U`); each kind of step's next set is computed by extensionality.
-/
module

public import Dsverify.Proof.github_com.xiang90.paxos.examples.paxosnet.Kit

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

namespace github_com.xiang90.paxos.examples.paxosnet

open EtcdGrove EtcdGrove.linkv

/-- `step` (kit.go) on the model's pure state: its verdict and next `(Known, Val, Pend)`. -/
def stepG (kn : Bool) (val : GoString) (pend : List BStr) (i : BStr) (u : Bool) (w : BStr) :
    Bool × Bool × GoString × List BStr :=
  if u then (true, kn, val, pend ++ [i])
  else if kn then (if w.1 = val then (true, kn, val, pend) else (false, kn, val, pend))
  else if w.1 = i.1 then (true, true, i.1, pend)
  else if w ∈ pend then (true, true, w.1, pend.erase w) else (false, kn, val, pend)

section pure
variable [GooseExts] [GoGlobalContext]

abbrev Cfg := PCfg (Option GoString) BStr

theorem woSet_K (w : GoString) (P : List BStr) (c : Cfg) :
    woSet true w P c ↔ c.st = some w ∧ c.pend.Subperm P := by
  simp [woSet]

theorem woSet_U (v : GoString) (P : List BStr) (c : Cfg) :
    woSet false v P c ↔ (c.st = none ∧ c.pend.Perm P) ∨
      ∃ x ∈ P, c.st = some x.1 ∧ c.pend.Subperm (P.erase x) := by
  simp [woSet]

theorem silent_K {w : GoString} {P : List BStr} {c c' : Cfg} (hs : PSilent woB c c')
    (hc : woSet true w P c) : woSet true w P c' := by
  rw [woSet_K] at hc ⊢
  obtain ⟨h1, h2⟩ := hc
  cases hs with
  | apply i _ =>
    refine ⟨?_, (List.erase_subperm i _).trans h2⟩
    simp [woB, h1]
  | perm p hp => exact ⟨h1, hp.subperm.trans h2⟩

theorem silent_U {v : GoString} {P : List BStr} {c c' : Cfg} (hs : PSilent woB c c')
    (hc : woSet false v P c) : woSet false v P c' := by
  rw [woSet_U] at hc ⊢
  rcases hc with ⟨h1, h2⟩ | ⟨x, hx, h1, h2⟩
  · cases hs with
    | apply i hi =>
      right
      refine ⟨i, h2.subset hi, by simp [woB, h1], ?_⟩
      exact (h2.erase i).subperm
    | perm p hp => exact .inl ⟨h1, hp.trans h2⟩
  · right
    cases hs with
    | apply i _ =>
      exact ⟨x, hx, by simp [woB, h1], (List.erase_subperm i _).trans h2⟩
    | perm p hp => exact ⟨x, hx, h1, hp.subperm.trans h2⟩

theorem closed_of_silent {S : PSet (Option GoString) BStr}
    (h : ∀ c c', PSilent woB c c' → S c → S c') : PSet.Closed woB S := by
  intro c c' hc hr
  induction hr with
  | refl => exact hc
  | step hs _ ih => exact ih (h _ _ hs hc)

theorem K_closed (w : GoString) (P : List BStr) : PSet.Closed woB (woSet true w P) :=
  closed_of_silent fun _ _ hs hc => silent_K hs hc

theorem U_closed (v : GoString) (P : List BStr) : PSet.Closed woB (woSet false v P) :=
  closed_of_silent fun _ _ hs hc => silent_U hs hc

/-- From a decided state, any sub-multiset of the pending writes is reachable. -/
theorem reach_append (w : GoString) (Q : List BStr) :
    ∀ D : List BStr, PReach woB (⟨some w, D ++ Q⟩ : Cfg) ⟨some w, Q⟩
  | [] => .refl _
  | d :: D => by
    refine .step (.apply _ d (by simp)) ?_
    simpa [woB] using reach_append w Q D

theorem reach_subperm (w : GoString) {R Q : List BStr} (h : Q.Subperm R) :
    PReach woB (⟨some w, R⟩ : Cfg) ⟨some w, Q⟩ := by
  obtain ⟨l, hl, hsub⟩ := h
  obtain ⟨L, hL⟩ := hsub.exists_perm_append
  have hp : (L ++ Q).Perm R :=
    (List.perm_append_comm.trans ((hl.symm.append_right L))).trans hL.symm
  exact .step (.perm _ (L ++ Q) hp) (reach_append w Q L)

theorem ppost_iff {S : PSet (Option GoString) BStr} (hS : PSet.Closed woB S) (i : BStr)
    (a : Ans BStr) (c' : Cfg) :
    ppost woB S i a c' ↔ ∃ c c₁, S c ∧ PStep woB c i a c₁ ∧ PReach woB c₁ c' := by
  constructor
  · rintro ⟨c₀, c, c₁, h0, hr, hst, hr2⟩
    exact ⟨c, c₁, hS _ _ h0 hr, hst, hr2⟩
  · rintro ⟨c, c₁, hc, hst, hr2⟩
    exact ⟨c, c, c₁, hc, .refl _, hst, hr2⟩

theorem pSeq_some {S T : PSet (Option GoString) BStr} {i : BStr} {a : Ans BStr}
    (h : ∀ c', ppost woB S i a c' ↔ T c') (hne : ∃ c, T c) :
    (pSeq woB).step S (i, a) = some T := by
  have e : ppost woB S i a = T := funext fun c => propext (h c)
  simp only [pSeq]
  rw [if_pos (by obtain ⟨c, hc⟩ := hne; exact ⟨c, (h c).2 hc⟩), e]

theorem pSeq_none {S : PSet (Option GoString) BStr} {i : BStr} {a : Ans BStr}
    (h : ∀ c', ¬ ppost woB S i a c') : (pSeq woB).step S (i, a) = none := by
  simp only [pSeq]
  rw [if_neg (fun ⟨c, hc⟩ => h c hc)]

theorem pstep_err {c c₁ : Cfg} {i : BStr} (h : PStep woB c i .err c₁) :
    c₁ = ⟨c.st, i :: c.pend⟩ := by
  cases h with
  | errW _ _ => rfl
  | errR h _ => simp [woB] at h

theorem pstep_ok {c c₁ : Cfg} {i w : BStr} (h : PStep woB c i (.ok w) c₁) :
    w = bnd (c.st.getD i.1) i ∧ c₁ = ⟨some (c.st.getD i.1), c.pend⟩ := by
  cases h with
  | ok _ => exact ⟨rfl, rfl⟩
  | obs _ h _ => simp [woB] at h

theorem pstep_err_mk (c : Cfg) (i : BStr) : PStep woB c i .err ⟨c.st, i :: c.pend⟩ :=
  .errW c i rfl rfl

theorem pstep_ok_mk (c : Cfg) (i : BStr) :
    PStep woB c i (.ok (woB.step i c.st).2) ⟨(woB.step i c.st).1, c.pend⟩ :=
  .ok c i rfl

theorem bnd_self (i : BStr) : bnd i.1 i = i := bnd_of i.2 i

theorem bnd_bstr (x i : BStr) : bnd x.1 i = x := bnd_of x.2 i

/-! ### The kinds of step -/

theorem step_err_U (v : GoString) (P : List BStr) (i : BStr) :
    (pSeq woB).step (woSet false v P) (i, .err) = some (woSet false v (P ++ [i])) := by
  refine pSeq_some (fun c' => ?_) ⟨⟨none, P ++ [i]⟩, (woSet_U _ _ _).2 (.inl ⟨rfl, .refl _⟩)⟩
  rw [ppost_iff (U_closed v P)]
  constructor
  · rintro ⟨c, c₁, hc, hst, hr⟩
    rw [pstep_err hst] at hr
    refine U_closed v (P ++ [i]) _ _ ?_ hr
    rw [woSet_U] at hc ⊢
    rcases hc with ⟨h1, h2⟩ | ⟨x, hx, h1, h2⟩
    · exact .inl ⟨h1, (h2.cons i).trans (List.perm_append_singleton i P).symm⟩
    · refine .inr ⟨x, List.mem_append_left _ hx, h1, ?_⟩
      rw [List.erase_append_left _ hx]
      exact ((List.subperm_cons i).2 h2).trans (List.perm_append_singleton i _).symm.subperm
  · intro hc'
    rw [woSet_U] at hc'
    have hP : (P ++ [i]).Perm (i :: P) := List.perm_append_singleton i P
    rcases hc' with ⟨h1, h2⟩ | ⟨x, hx, h1, h2⟩
    · refine ⟨⟨none, P⟩, ⟨none, i :: P⟩, (woSet_U _ _ _).2 (.inl ⟨rfl, .refl _⟩),
        pstep_err_mk _ i, ?_⟩
      have e : c' = ⟨none, c'.pend⟩ := by cases c'; simp_all
      rw [e]
      exact .step (.perm _ _ (h2.trans hP)) (.refl _)
    · refine ⟨⟨none, P⟩, ⟨none, i :: P⟩, (woSet_U _ _ _).2 (.inl ⟨rfl, .refl _⟩),
        pstep_err_mk _ i, ?_⟩
      have e : c' = ⟨some x.1, c'.pend⟩ := by cases c'; simp_all
      rw [e]
      refine .step (.apply _ x (hP.subset hx)) ?_
      simp only [woB, Option.getD_none]
      exact reach_subperm x.1 (h2.trans (hP.erase x).subperm)

theorem step_err_K (w : GoString) (P : List BStr) (i : BStr) :
    (pSeq woB).step (woSet true w P) (i, .err) = some (woSet true w (P ++ [i])) := by
  refine pSeq_some (fun c' => ?_) ⟨⟨some w, P ++ [i]⟩, (woSet_K _ _ _).2 ⟨rfl, .refl _⟩⟩
  rw [ppost_iff (K_closed w P)]
  have hP : (P ++ [i]).Perm (i :: P) := List.perm_append_singleton i P
  constructor
  · rintro ⟨c, c₁, hc, hst, hr⟩
    rw [pstep_err hst] at hr
    refine K_closed w (P ++ [i]) _ _ ?_ hr
    rw [woSet_K] at hc ⊢
    exact ⟨hc.1, ((List.subperm_cons i).2 hc.2).trans hP.symm.subperm⟩
  · intro hc'
    rw [woSet_K] at hc'
    refine ⟨⟨some w, P⟩, ⟨some w, i :: P⟩, (woSet_K _ _ _).2 ⟨rfl, .refl _⟩,
      pstep_err_mk _ i, ?_⟩
    have e : c' = ⟨some w, c'.pend⟩ := by cases c'; simp_all
    rw [e]
    exact reach_subperm w (hc'.2.trans hP.subperm)

theorem step_ok_K (val : GoString) (P : List BStr) (i w : BStr) (hw : w.1 = val) :
    (pSeq woB).step (woSet true val P) (i, .ok w) = some (woSet true val P) := by
  refine pSeq_some (fun c' => ?_) ⟨⟨some val, P⟩, (woSet_K _ _ _).2 ⟨rfl, .refl _⟩⟩
  rw [ppost_iff (K_closed val P)]
  constructor
  · rintro ⟨c, c₁, hc, hst, hr⟩
    obtain ⟨-, e⟩ := pstep_ok hst
    rw [e] at hr
    refine K_closed val P _ _ ?_ hr
    rw [woSet_K] at hc ⊢
    simp [hc.1, hc.2]
  · intro hc'
    rw [woSet_K] at hc'
    have hb : bnd val i = w := by rw [← hw]; exact bnd_bstr w i
    refine ⟨⟨some val, P⟩, ⟨some val, P⟩, (woSet_K _ _ _).2 ⟨rfl, .refl _⟩, ?_, ?_⟩
    · have := pstep_ok_mk ⟨some val, P⟩ i
      simpa [woB, hb] using this
    · have e : c' = ⟨some val, c'.pend⟩ := by cases c'; simp_all
      rw [e]
      exact reach_subperm val hc'.2

theorem step_ok_K_no (val : GoString) (hv : (val.length : Int) < 2 ^ 48) (P : List BStr)
    (i w : BStr) (hw : w.1 ≠ val) :
    (pSeq woB).step (woSet true val P) (i, .ok w) = none := by
  refine pSeq_none (fun c' hc' => ?_)
  rw [ppost_iff (K_closed val P)] at hc'
  obtain ⟨c, c₁, hc, hst, -⟩ := hc'
  obtain ⟨e, -⟩ := pstep_ok hst
  rw [woSet_K] at hc
  rw [hc.1] at e
  simp only [Option.getD_some] at e
  rw [bnd_of hv] at e
  exact hw (by rw [e])

theorem step_ok_U_self (v : GoString) (P : List BStr) (i w : BStr) (hw : w.1 = i.1) :
    (pSeq woB).step (woSet false v P) (i, .ok w) = some (woSet true i.1 P) := by
  have hwi : w = i := Subtype.ext hw
  subst hwi
  refine pSeq_some (fun c' => ?_) ⟨⟨some w.1, P⟩, (woSet_K _ _ _).2 ⟨rfl, .refl _⟩⟩
  rw [ppost_iff (U_closed v P)]
  constructor
  · rintro ⟨c, c₁, hc, hst, hr⟩
    obtain ⟨e1, e2⟩ := pstep_ok hst
    rw [e2] at hr
    refine K_closed w.1 P _ _ ?_ hr
    rw [woSet_K]
    rw [woSet_U] at hc
    rcases hc with ⟨h1, h2⟩ | ⟨x, hx, h1, h2⟩
    · simp [h1, h2.subperm]
    · rw [h1, Option.getD_some, bnd_bstr] at e1
      subst e1
      simp [h1, h2.trans (List.erase_subperm _ _)]
  · intro hc'
    rw [woSet_K] at hc'
    refine ⟨⟨none, P⟩, ⟨some w.1, P⟩, (woSet_U _ _ _).2 (.inl ⟨rfl, .refl _⟩), ?_, ?_⟩
    · have := pstep_ok_mk ⟨none, P⟩ w
      simpa [woB, bnd_self] using this
    · have e : c' = ⟨some w.1, c'.pend⟩ := by cases c'; simp_all
      rw [e]
      exact reach_subperm w.1 hc'.2

theorem step_ok_U_pend (v : GoString) (P : List BStr) (i w : BStr) (hw : w.1 ≠ i.1)
    (hm : w ∈ P) :
    (pSeq woB).step (woSet false v P) (i, .ok w) = some (woSet true w.1 (P.erase w)) := by
  refine pSeq_some (fun c' => ?_) ⟨⟨some w.1, P.erase w⟩, (woSet_K _ _ _).2 ⟨rfl, .refl _⟩⟩
  rw [ppost_iff (U_closed v P)]
  constructor
  · rintro ⟨c, c₁, hc, hst, hr⟩
    obtain ⟨e1, e2⟩ := pstep_ok hst
    rw [e2] at hr
    refine K_closed w.1 (P.erase w) _ _ ?_ hr
    rw [woSet_K]
    rw [woSet_U] at hc
    rcases hc with ⟨h1, h2⟩ | ⟨x, hx, h1, h2⟩
    · rw [h1, Option.getD_none, bnd_self] at e1
      exact absurd (congrArg Subtype.val e1) hw
    · rw [h1, Option.getD_some, bnd_bstr] at e1
      subst e1
      simp [h1, h2]
  · intro hc'
    rw [woSet_K] at hc'
    refine ⟨⟨some w.1, P.erase w⟩, ⟨some w.1, P.erase w⟩,
      (woSet_U _ _ _).2 (.inr ⟨w, hm, rfl, .refl _⟩), ?_, ?_⟩
    · have := pstep_ok_mk ⟨some w.1, P.erase w⟩ i
      simpa [woB, bnd_bstr] using this
    · have e : c' = ⟨some w.1, c'.pend⟩ := by cases c'; simp_all
      rw [e]
      exact reach_subperm w.1 hc'.2

theorem step_ok_U_no (v : GoString) (P : List BStr) (i w : BStr) (hw : w.1 ≠ i.1)
    (hm : w ∉ P) : (pSeq woB).step (woSet false v P) (i, .ok w) = none := by
  refine pSeq_none (fun c' hc' => ?_)
  rw [ppost_iff (U_closed v P)] at hc'
  obtain ⟨c, c₁, hc, hst, -⟩ := hc'
  obtain ⟨e1, -⟩ := pstep_ok hst
  rw [woSet_U] at hc
  rcases hc with ⟨h1, -⟩ | ⟨x, hx, h1, -⟩
  · rw [h1, Option.getD_none, bnd_self] at e1
    exact hw (congrArg Subtype.val e1)
  · rw [h1, Option.getD_some, bnd_bstr] at e1
    subst e1
    exact hm hx

/-- **`step` is the model's step** on the set its state stands for (with a bounded known value). -/
theorem stepG_pSeq (kn : Bool) (val : GoString) (hv : (val.length : Int) < 2 ^ 48)
    (pend : List BStr) (i : BStr) (u : Bool) (w : BStr) :
    (pSeq woB).step (woSet kn val pend) (i, if u then .err else .ok w) =
      if (stepG kn val pend i u w).1 then
        some (woSet (stepG kn val pend i u w).2.1 (stepG kn val pend i u w).2.2.1
          (stepG kn val pend i u w).2.2.2)
      else none := by
  unfold stepG
  cases u
  · cases kn
    · simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases h1 : w.1 = i.1
      · simp only [h1, ↓reduceIte]; exact step_ok_U_self val pend i w h1
      · simp only [h1, ↓reduceIte]
        by_cases h2 : w ∈ pend
        · simp only [h2, ↓reduceIte]; exact step_ok_U_pend val pend i w h1 h2
        · simp only [h2, ↓reduceIte]; exact step_ok_U_no val pend i w h1 h2
    · simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases h1 : w.1 = val
      · simp only [h1, ↓reduceIte]; exact step_ok_K val pend i w h1
      · simp only [h1, ↓reduceIte]; exact step_ok_K_no val hv pend i w h1
  · simp only [↓reduceIte]
    cases kn
    · exact step_err_U val pend i
    · exact step_err_K val pend i

/-- `step`'s next state: its known value bounded, at most one more pending. -/
theorem stepG_bounds (kn : Bool) (val : GoString) (hv : (val.length : Int) < 2 ^ 48)
    (pend : List BStr) (i : BStr) (u : Bool) (w : BStr) :
    ((stepG kn val pend i u w).2.2.1.length : Int) < 2 ^ 48 ∧
      (stepG kn val pend i u w).2.2.2.length ≤ pend.length + 1 := by
  have hi := i.2
  have hw := w.2
  have he := List.length_erase_le (a := w) (l := pend)
  cases u <;> cases kn <;> simp only [stepG, ↓reduceIte, Bool.false_eq_true] <;>
    (repeat' split) <;> simp only [List.length_append, List.length_singleton] <;> omega

/-- The initial set: `State{}`'s. -/
theorem woSet_init : woSet false [] [] = pInit woB := by
  funext c
  apply propext
  rw [woSet_U]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨x, hx, -⟩)
    · have : c.pend = [] := List.Perm.eq_nil h2
      cases c; simp_all [pInit, woB]
    · simp at hx
  · intro h
    simp only [pInit] at h
    subst h
    exact .inl ⟨rfl, .refl _⟩

end pure

section dec
variable [GooseExts] [go_gctx : GoGlobalContext] [lctx : GoLocalContext] [GoSemanticsFunctions]
variable [sem : go.Semantics] [bvi : go.BasicIntoValInj]
variable [package_sem : github_com.xiang90.paxos.examples.paxosnet.Assumptions]

/-- `Out`'s values are injective (`Unknown` and `V` are read off by deterministic steps). -/
theorem out_intoVal_inj {x y : Out} (h : (#x : val) = #y) : x = y := by
  have hV := (Out.TypeAssumptions.get'V x).isGoStep_det_internal.isGoStep_pure_det
  have hV' := (Out.TypeAssumptions.get'V y).isGoStep_det_internal.isGoStep_pure_det
  have hU := (Out.TypeAssumptions.get'Unknown x).isGoStep_det_internal.isGoStep_pure_det
  have hU' := (Out.TypeAssumptions.get'Unknown y).isGoStep_det_internal.isGoStep_pure_det
  rw [h, hV'] at hV
  rw [h, hU'] at hU
  have eV : Val #x.V' = Val #y.V' := (congrFun hV (Val #y.V')) ▸ rfl
  have eU : Val #x.Unknown' = Val #y.Unknown' := (congrFun hU (Val #y.Unknown')) ▸ rfl
  injection eV with eV
  injection eU with eU
  have eV' := go.intoVal_inj eV
  have eU' := GoGlobalContext.intoVal_inj_bool eU
  cases x; cases y
  simp only at eV' eU'
  subst eV' eU'
  rfl

theorem strV_inj {a b : GoString} (h : strV a = strV b) : a = b := by
  simp only [strV, interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq,
    _root_.true_and] at h
  exact go.intoVal_inj h

theorem outV_inj {u v u' v'} (h : outV u v = outV u' v') : u = u' ∧ v = v' := by
  simp only [outV, interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq,
    _root_.true_and] at h
  have := out_intoVal_inj h
  simp only [Out.mk.injEq] at this
  exact this

/-- `Out{u, w}`'s bytes. -/
theorem encOutV_outV (u : Bool) (w : BStr) : encOutV (outV u w.1) = encOutB u w.1 := by
  unfold encOutV
  split
  · rename_i h
    obtain ⟨h1, h2⟩ := outV_inj h.choose_spec
    rw [← h1, ← h2]
  · rename_i h
    exact absurd ⟨(u, w), rfl⟩ h

/-- `woDec` on a boxed bounded `string` and a boxed bounded `Out`. -/
theorem woDec_box (i : BStr) (u : Bool) (w : BStr) :
    woDec (strV i.1, outV u w.1) = some (i, if u then .err else .ok w) := by
  unfold woDec
  split
  · next h =>
    have hs := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h))
    obtain ⟨h1, h2⟩ := Prod.mk.inj hs
    have e1 := Subtype.ext (strV_inj h1)
    obtain ⟨e2, e3⟩ := outV_inj h2
    have e3' := Subtype.ext e3
    dsimp only
    rw [← e3', ← e2, ← e1]
  · next hn => exact absurd ⟨i, u, w, rfl⟩ hn

end dec

end github_com.xiang90.paxos.examples.paxosnet
end Perennial
