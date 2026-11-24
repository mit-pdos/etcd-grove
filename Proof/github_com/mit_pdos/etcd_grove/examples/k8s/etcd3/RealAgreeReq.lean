/-
Lean-first (no Rocq counterpart).

# Equal requests step alike (k8s 7g step 5, decision 1, lemma (ii))

`rstepL x m out` depends on the input `x` only through `realRequest(x)`: two inputs whose views
(`reqRep`, with the closures' captured cells `reqPin`) are of one `Request` value step alike.

- pure congruences of `rstepL`, per kind (`rstepL_list_congr`, `rstepL_get_congr`, `rstepL_create_congr`,
  `rstepL_delete_congr`);
- `preAt_agree`, `labelSel_intoVal_inj`, `fieldSel_intoVal_inj`;
- **`reqRep_agree`**.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RealAgree
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ClosPin
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ModelFit

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI Iris.ProofMode k8sDeep k8s_etcd3
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input labelSel fieldSel)

section pure
variable [GooseExts]

theorem rstepL_list_eq (x : Input) (h : x.Kind' = W64 4) (m : RM) (out : RResp) :
    rstepL x m out = (rvalidateListL x m (rlistL x m) out, m, none) := by
  unfold rstepL rexecL; rw [if_pos h, if_pos h]

theorem rstepL_get_eq (x : Input)
    (h : ¬ (x.Kind' = W64 4 ∨ x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2)) (m : RM) (out : RResp) :
    rstepL x m out = (rvalidateGetL x m (rgetL x m) out, m, none) := by
  simp only [not_or] at h
  obtain ⟨a, b, c, d⟩ := h
  have e : ¬ (x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2) := by simp only [not_or]; exact ⟨b, c, d⟩
  unfold rstepL rexecL; rw [if_neg a, if_neg e, if_neg a, if_neg b, if_neg c, if_neg d]

theorem rstepL_write_congr (x1 x2 : Input) (h1 : x1.Kind' = W64 0 ∨ x1.Kind' = W64 1 ∨ x1.Kind' = W64 2)
    (h2 : x2.Kind' = W64 0 ∨ x2.Kind' = W64 1 ∨ x2.Kind' = W64 2) (m : RM) (out : RResp)
    (he : rexecL x1 m = rexecL x2 m) : rstepL x1 m out = rstepL x2 m out := by
  have n4 : ∀ x : Input, (x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2) → x.Kind' ≠ W64 4 := by
    intro x h e; rw [e] at h; revert h; decide
  unfold rstepL; rw [if_neg (n4 x1 h1), if_neg (n4 x2 h2), if_pos h1, if_pos h2, he]

theorem rstepL_list_congr (x1 x2 : Input) (h1 : x1.Kind' = W64 4) (h2 : x2.Kind' = W64 4)
    (hkey : x1.ListKey' = x2.ListKey') (hrec : x1.Recursive' = x2.Recursive') (hlim : x1.Limit' = x2.Limit')
    (hlc : listConsL x1 = listConsL x2) (hsel : selOkL x1 = selOkL x2) (hpe : predEmptyL x1 = predEmptyL x2)
    (m : RM) (out : RResp) : rstepL x1 m out = rstepL x2 m out := by
  have hln : limitN x1 = limitN x2 := by unfold limitN; rw [hlim]
  rw [rstepL_list_eq x1 h1, rstepL_list_eq x2 h2]
  unfold rlistL rvalidateListL equalListRespL validCacherContinueL listItemsL
  rw [hkey, hrec, hlim, hlc, hsel, hpe, hln]

theorem rstepL_get_congr (x1 x2 : Input)
    (h1 : ¬ (x1.Kind' = W64 4 ∨ x1.Kind' = W64 0 ∨ x1.Kind' = W64 1 ∨ x1.Kind' = W64 2))
    (h2 : ¬ (x2.Kind' = W64 4 ∨ x2.Kind' = W64 0 ∨ x2.Kind' = W64 1 ∨ x2.Kind' = W64 2))
    (hkey : storeKeyL x1.Key' = storeKeyL x2.Key') (hmin : x1.MinRV' = x2.MinRV')
    (hign : x1.IgnoreNotFound' = x2.IgnoreNotFound') (m : RM) (out : RResp) :
    rstepL x1 m out = rstepL x2 m out := by
  rw [rstepL_get_eq x1 h1, rstepL_get_eq x2 h2]
  unfold rvalidateGetL rgetL
  rw [hkey, hmin, hign]

theorem rstepL_create_congr (x1 x2 : Input) (h1 : x1.Kind' = W64 0) (h2 : x2.Kind' = W64 0)
    (hkey : storeKeyL x1.Key' = storeKeyL x2.Key') (hc : createObjL x1 = createObjL x2)
    (m : RM) (out : RResp) : rstepL x1 m out = rstepL x2 m out := by
  unfold createObjL at hc
  simp only [Obj.mk.injEq] at hc
  obtain ⟨hn, hs, hu, hv, hnd, ha, -, -⟩ := hc
  have n4 : ∀ x : Input, x.Kind' = W64 0 → x.Kind' ≠ W64 4 := by intro x h e; rw [h] at e; revert e; decide
  refine rstepL_write_congr x1 x2 (Or.inl h1) (Or.inl h2) m out ?_
  unfold rexecL
  rw [if_neg (n4 x1 h1), if_neg (n4 x2 h2), if_pos h1, if_pos h2]
  simp only [rcreateL, hkey, hn, hs, hu, hv, hnd, ha]

theorem checkMsgL_congr (x1 x2 : Input) (h : kpreOf x1 = kpreOf x2) : checkMsgL x1 = checkMsgL x2 := by
  unfold kpreOf at h
  simp only [k8s.KPre.mk.injEq] at h
  obtain ⟨hu, hr⟩ := h
  funext o
  unfold checkMsgL
  by_cases a1 : x1.HasPreUID' <;> by_cases a2 : x2.HasPreUID' <;> simp only [a1, a2, Bool.false_eq_true,
    ↓reduceIte, reduceCtorEq, Option.some.injEq] at hu <;>
    by_cases b1 : x1.HasPreRV' <;> by_cases b2 : x2.HasPreRV' <;> simp only [b1, b2, Bool.false_eq_true,
      ↓reduceIte, reduceCtorEq, Option.some.injEq] at hr <;> simp [a1, a2, b1, b2, hu, hr]

theorem rstepL_delete_congr (x1 x2 : Input) (h1 : x1.Kind' = W64 1) (h2 : x2.Kind' = W64 1)
    (hkey : storeKeyL x1.Key' = storeKeyL x2.Key') (hp : kpreOf x1 = kpreOf x2)
    (hh : x1.HasReject' = x2.HasReject') (hr : x1.Reject' = x2.Reject')
    (m : RM) (out : RResp) : rstepL x1 m out = rstepL x2 m out := by
  have n : ∀ x : Input, x.Kind' = W64 1 → x.Kind' ≠ W64 4 ∧ x.Kind' ≠ W64 0 := by
    intro x h; rw [h]; exact ⟨by decide, by decide⟩
  have hcm := checkMsgL_congr x1 x2 hp
  refine rstepL_write_congr x1 x2 (Or.inr (Or.inl h1)) (Or.inr (Or.inl h2)) m out ?_
  unfold rexecL
  rw [if_neg (n x1 h1).1, if_neg (n x2 h2).1, if_neg (n x1 h1).2, if_neg (n x2 h2).2, if_pos h1, if_pos h2]
  simp only [rdeleteL, hkey, hcm, hh, hr]

theorem matchOptL_iff (x : Input) :
    (matchOptL x = go!"NotOlderThan" ↔ x.Match' = W64 1) ∧ (matchOptL x = go!"Exact" ↔ x.Match' = W64 2) := by
  unfold matchOptL
  by_cases a : x.Match' = W64 1
  · rw [if_pos a, a]; decide
  rw [if_neg a]
  by_cases b : x.Match' = W64 2
  · rw [if_pos b, b]; decide
  rw [if_neg b]
  exact ⟨iff_of_false (by decide) a, iff_of_false (by decide) b⟩

theorem listConsL_congr (x1 x2 : Input) (hmin : x1.MinRV' = x2.MinRV') (hm : matchOptL x1 = matchOptL x2)
    (hrec : x1.Recursive' = x2.Recursive') (hlim : x1.Limit' = x2.Limit') : listConsL x1 = listConsL x2 := by
  obtain ⟨a1, b1⟩ := matchOptL_iff x1
  obtain ⟨a2, b2⟩ := matchOptL_iff x2
  rw [hm] at a1 b1
  have e1 : (x1.Match' = W64 1) = (x2.Match' = W64 1) := propext (a1.symm.trans a2)
  have e2 : (x1.Match' = W64 2) = (x2.Match' = W64 2) := propext (b1.symm.trans b2)
  unfold listConsL
  simp only [hmin, hrec, hlim, e1, e2]

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

include sem package_sem in
theorem labelSel_intoVal_inj : Function.Injective (intoVal (V := labelSel)) := by
  intro x y h
  have h : (#x : val) = #y := h
  have := GoGlobalContext.intoVal_inj_bool (Expr.Val.inj (proj_eq
    (labelSel.TypeAssumptions.get'all x) (labelSel.TypeAssumptions.get'all y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (labelSel.TypeAssumptions.get'app x) (labelSel.TypeAssumptions.get'app y) h))
  cases x; cases y; simp_all

include sem package_sem in
theorem fieldSel_intoVal_inj : Function.Injective (intoVal (V := fieldSel)) := by
  intro x y h
  have h : (#x : val) = #y := h
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (fieldSel.TypeAssumptions.get'n x) (fieldSel.TypeAssumptions.get'n y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (fieldSel.TypeAssumptions.get'f1 x) (fieldSel.TypeAssumptions.get'f1 y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (fieldSel.TypeAssumptions.get'v1 x) (fieldSel.TypeAssumptions.get'v1 y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (fieldSel.TypeAssumptions.get'f2 x) (fieldSel.TypeAssumptions.get'f2 y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (fieldSel.TypeAssumptions.get'v2 x) (fieldSel.TypeAssumptions.get'v2 y) h))
  cases x; cases y; simp_all

theorem optStrPtr_agree (l : Loc) (a b : Option GoString) :
    (k8s.optStrPtr l a ∗ k8s.optStrPtr l b : IProp GF) ⊢ ⌜a = b⌝ := by
  iintro ⟨H1, H2⟩
  cases a <;> cases b <;> simp only [k8s.optStrPtr]
  · ipureintro; trivial
  · icases H1 with %e
    ihave %hn := typedPointsto_not_null _ _ _ $$ H2
    exact absurd e hn
  · icases H2 with %e
    ihave %hn := typedPointsto_not_null _ _ _ $$ H1
    exact absurd e hn
  · icombine H1 H2 gives %e
    ipureintro; rw [e]

/-- **A `*storage.Preconditions` holds one precondition pair.** -/
theorem preAt_agree (pp : Loc) (p1 p2 : k8s.KPre) :
    (k8s.preAt pp p1 ∗ k8s.preAt pp p2 : IProp GF) ⊢ ⌜p1 = p2⌝ := by
  iintro ⟨H1, H2⟩
  iunfold k8s.preAt at H1 H2
  icases H1 with (%e1 | ⟨%lu1, %lr1, #Hp1, Hu1, Hr1⟩)
  · icases H2 with (%e2 | ⟨%lu2, %lr2, #Hp2, -, -⟩)
    · ipureintro; rw [e1.2, e2.2]
    · ihave %hn := typedPointsto_not_null _ _ _ $$ Hp2
      exact absurd e1.1 hn
  · icases H2 with (%e2 | ⟨%lu2, %lr2, #Hp2, Hu2, Hr2⟩)
    · ihave %hn := typedPointsto_not_null _ _ _ $$ Hp1
      exact absurd e2.1 hn
    · icombine Hp1 Hp2 gives %e
      simp only [k8s_io.apiserver.pkg.storage.Preconditions.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      ihave %hu := optStrPtr_agree lu1 p1.uid p2.uid $$ [Hu1 Hu2]
      · iframe
      ihave %hr := optStrPtr_agree lr1 p1.rv p2.rv $$ [Hr1 Hr2]
      · iframe
      ipureintro
      cases p1; cases p2
      simp only at hu hr
      rw [hu, hr]

/-- **The captured cells of `realRequest(x)`'s closure** (a delete's `validateFor`, an update's
`tryUpdateFor`; persistent). -/
def reqPin (r : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Request) (x : Input) :
    IProp GF :=
  if x.Kind' = W64 1 then validatePin x.HasReject' x.Reject' r.Delete'.ValidateDeletion'
  else if x.Kind' = W64 2 then tryUpdatePin x r.Update'.UpdateFunc'
  else iprop(True)

instance reqPin_persistent (r : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Request)
    (x : Input) : Persistent (reqPin (GF := GF) r x) := by
  unfold reqPin; repeat (first | infer_instance | split)

/-- The `Op` of `realRequest(x)`. -/
def opName (x : Input) : GoString :=
  if x.Kind' = W64 4 then go!"List" else if x.Kind' = W64 0 then go!"Create"
  else if x.Kind' = W64 1 then go!"Delete" else if x.Kind' = W64 2 then go!"Update" else go!"Get"

theorem reqRep_op (r : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Request) (x : Input) :
    reqRep (GF := GF) r x ⊢ ⌜r.Op' = opName x⌝ := by
  unfold reqRep opName
  by_cases a : x.Kind' = W64 4
  · rw [if_pos a, if_pos a]; iintro %h; ipureintro; exact h.1
  rw [if_neg a, if_neg a]
  by_cases b : x.Kind' = W64 0
  · rw [if_pos b, if_pos b]; iintro ⟨%h, -⟩; ipureintro; exact h.1
  rw [if_neg b, if_neg b]
  by_cases c : x.Kind' = W64 1
  · rw [if_pos c, if_pos c]; iintro ⟨%h, -⟩; ipureintro; exact h.1
  rw [if_neg c, if_neg c]
  by_cases d : x.Kind' = W64 2
  · rw [if_pos d, if_pos d]; iintro ⟨%h, -⟩; ipureintro; exact h.1
  · rw [if_neg d, if_neg d]; iintro %h; ipureintro; exact h.1

theorem opName_iff (x : Input) :
    (opName x = go!"List" ↔ x.Kind' = W64 4) ∧ (opName x = go!"Create" ↔ x.Kind' = W64 0) ∧
    (opName x = go!"Delete" ↔ x.Kind' = W64 1) ∧ (opName x = go!"Update" ↔ x.Kind' = W64 2) := by
  unfold opName
  by_cases a : x.Kind' = W64 4
  · rw [if_pos a, a]; decide
  rw [if_neg a]
  by_cases b : x.Kind' = W64 0
  · rw [if_pos b, b]; decide
  rw [if_neg b]
  by_cases c : x.Kind' = W64 1
  · rw [if_pos c, c]; decide
  rw [if_neg c]
  by_cases d : x.Kind' = W64 2
  · rw [if_pos d, d]; decide
  rw [if_neg d]
  exact ⟨iff_of_false (by decide) a, iff_of_false (by decide) b, iff_of_false (by decide) c,
    iff_of_false (by decide) d⟩

theorem opName_class (x1 x2 : Input) (h : opName x1 = opName x2) :
    (x1.Kind' = W64 4 ↔ x2.Kind' = W64 4) ∧ (x1.Kind' = W64 0 ↔ x2.Kind' = W64 0) ∧
    (x1.Kind' = W64 1 ↔ x2.Kind' = W64 1) ∧ (x1.Kind' = W64 2 ↔ x2.Kind' = W64 2) := by
  obtain ⟨a1, b1, c1, d1⟩ := opName_iff x1
  obtain ⟨a2, b2, c2, d2⟩ := opName_iff x2
  rw [h] at a1 b1 c1 d1
  exact ⟨a1.symm.trans a2, b1.symm.trans b2, c1.symm.trans c2, d1.symm.trans d2⟩

theorem reqRep_list (r : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Request) (x : Input)
    (h : x.Kind' = W64 4) : reqRep (GF := GF) r x ⊢ ⌜r.Key' = x.ListKey' ∧ r.List'.Options' = listOptsV x⌝ := by
  unfold reqRep; rw [if_pos h]; iintro %h; ipureintro; exact h.2

theorem reqRep_create (r : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Request) (x : Input)
    (h : x.Kind' = W64 0) : reqRep (GF := GF) r x ⊢ ⌜r.Key' = storeKeyL x.Key'⌝ ∗ ∃ op : Loc,
      ⌜r.Create'.Object' = interface.mkOk
        (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty) #op⌝ ∗
      op ↦□ createObjL x := by
  have n : x.Kind' ≠ W64 4 := by rw [h]; decide
  unfold reqRep; rw [if_neg n, if_pos h]; iintro ⟨%h, H⟩; iframe H; ipureintro; exact h.2

theorem reqRep_delete (r : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Request) (x : Input)
    (h : x.Kind' = W64 1) : reqRep (GF := GF) r x ⊢ ⌜r.Key' = storeKeyL x.Key'⌝ ∗
      k8s.preAt r.Delete'.Preconditions' (kpreOf x) := by
  have n4 : x.Kind' ≠ W64 4 := by rw [h]; decide
  have n0 : x.Kind' ≠ W64 0 := by rw [h]; decide
  unfold reqRep; rw [if_neg n4, if_neg n0, if_pos h]; iintro ⟨%h, H, -⟩; iframe H; ipureintro; exact h.2.1

theorem reqRep_get (r : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Request) (x : Input)
    (h : ¬ (x.Kind' = W64 4 ∨ x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2)) :
    reqRep (GF := GF) r x ⊢ ⌜r.Key' = storeKeyL x.Key' ∧ r.Get'.Options'.ResourceVersion' = x.MinRV' ∧
      r.Get'.Options'.IgnoreNotFound' = x.IgnoreNotFound'⌝ := by
  simp only [not_or] at h
  obtain ⟨a, b, c, d⟩ := h
  unfold reqRep; rw [if_neg a, if_neg b, if_neg c, if_neg d]; iintro %h; ipureintro; exact h.2

theorem reqPin_delete (r : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Request) (x : Input)
    (h : x.Kind' = W64 1) :
    reqPin (GF := GF) r x ⊢ validatePin x.HasReject' x.Reject' r.Delete'.ValidateDeletion' := by
  unfold reqPin; rw [if_pos h]

theorem reqPin_update (r : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Request) (x : Input)
    (h : x.Kind' = W64 2) : reqPin (GF := GF) r x ⊢ tryUpdatePin x r.Update'.UpdateFunc' := by
  have n : x.Kind' ≠ W64 1 := by rw [h]; decide
  unfold reqPin; rw [if_neg n, if_pos h]

/-- **Two inputs of one request step alike** (decision 1, lemma (ii)). -/
theorem reqRep_agree (r : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Request)
    (x1 x2 : Input) :
    reqRep (GF := GF) r x1 ∗ reqPin r x1 ∗ reqRep r x2 ∗ reqPin r x2 ⊢
      ⌜∀ m out, rstepL x1 m out = rstepL x2 m out⌝ := by
  iintro ⟨#R1, #P1, #R2, #P2⟩
  ihave %o1 := reqRep_op r x1 $$ R1
  ihave %o2 := reqRep_op r x2 $$ R2
  obtain ⟨c4, c0, c1, c2⟩ := opName_class x1 x2 (o1.symm.trans o2)
  by_cases a : x1.Kind' = W64 4
  · have a2 := c4.1 a
    ihave %h1 := reqRep_list r x1 a $$ R1
    ihave %h2 := reqRep_list r x2 a2 $$ R2
    have hk := h1.1.symm.trans h2.1
    have ho := h1.2.symm.trans h2.2
    unfold listOptsV predV at ho
    simp only [k8s_io.apiserver.pkg.storage.ListOptions.mk.injEq,
      k8s_io.apiserver.pkg.storage.SelectionPredicate.mk.injEq] at ho
    obtain ⟨hmin, hm, ⟨hl, hf, -, -, -, hlim, -⟩, hrec, -⟩ := ho
    have hls : labelSelL x1 = labelSelL x2 :=
      labelSel_intoVal_inj (sem := sem) (package_sem := package_sem)
        (GoInterfaceOk.mk.inj (GoInterface.ok.inj hl)).2
    have hfs : fieldSelForL x1 = fieldSelForL x2 :=
      fieldSel_intoVal_inj (sem := sem) (package_sem := package_sem)
        (GoInterfaceOk.mk.inj (GoInterface.ok.inj hf)).2
    have hsel : selOkL x1 = selOkL x2 := by funext o; unfold selOkL; rw [hls, hfs]
    have hpe : predEmptyL x1 = predEmptyL x2 := by unfold predEmptyL; rw [hls, hfs]
    ipureintro
    intro m out
    exact rstepL_list_congr x1 x2 a a2 hk hrec hlim (listConsL_congr x1 x2 hmin hm hrec hlim) hsel hpe m out
  by_cases b : x1.Kind' = W64 0
  · have b2 := c0.1 b
    iclear P1 P2
    ihave ⟨%k1, %op1, %e1, #O1⟩ := reqRep_create r x1 b $$ R1
    ihave ⟨%k2, %op2, %e2, #O2⟩ := reqRep_create r x2 b2 $$ R2
    obtain ⟨-, rfl⟩ := mkOk_loc_inj (sem := sem) _ _ _ _ (e1.symm.trans e2)
    icombine O1 O2 gives %hc
    ipureintro
    intro m out
    exact rstepL_create_congr x1 x2 b b2 (k1.symm.trans k2) hc m out
  by_cases c : x1.Kind' = W64 1
  · have c2 := c1.1 c
    ihave ⟨%k1, #Q1⟩ := reqRep_delete r x1 c $$ R1
    ihave ⟨%k2, #Q2⟩ := reqRep_delete r x2 c2 $$ R2
    ihave %hp := preAt_agree r.Delete'.Preconditions' (kpreOf x1) (kpreOf x2) $$ [Q1 Q2]
    · isplit
      · iexact Q1
      · iexact Q2
    ihave #V1 := reqPin_delete r x1 c $$ P1
    ihave #V2 := reqPin_delete r x2 c2 $$ P2
    ihave %hv := validatePin_agree x1.HasReject' x2.HasReject' x1.Reject' x2.Reject'
      r.Delete'.ValidateDeletion' $$ [V1 V2]
    · isplit
      · iexact V1
      · iexact V2
    ipureintro
    intro m out
    exact rstepL_delete_congr x1 x2 c c2 (k1.symm.trans k2) hp hv.1 hv.2 m out
  by_cases d : x1.Kind' = W64 2
  · have d2 := c2.1 d
    ihave #U1 := reqPin_update r x1 d $$ P1
    ihave #U2 := reqPin_update r x2 d2 $$ P2
    ihave %hx := tryUpdatePin_agree x1 x2 r.Update'.UpdateFunc' $$ [U1 U2]
    · isplit
      · iexact U1
      · iexact U2
    subst hx
    ipureintro
    intro m out
    rfl
  have g1 : ¬ (x1.Kind' = W64 4 ∨ x1.Kind' = W64 0 ∨ x1.Kind' = W64 1 ∨ x1.Kind' = W64 2) := by
    simp only [not_or]; exact ⟨a, b, c, d⟩
  have g2 : ¬ (x2.Kind' = W64 4 ∨ x2.Kind' = W64 0 ∨ x2.Kind' = W64 1 ∨ x2.Kind' = W64 2) := by
    simp only [not_or]
    exact ⟨fun e => a (c4.2 e), fun e => b (c0.2 e), fun e => c (c1.2 e), fun e => d (c2.2 e)⟩
  ihave %h1 := reqRep_get r x1 g1 $$ R1
  ihave %h2 := reqRep_get r x2 g2 $$ R2
  ipureintro
  intro m out
  exact rstepL_get_congr x1 x2 g1 g2 (h1.1.symm.trans h2.1) (h1.2.1.symm.trans h2.2.1)
    (h1.2.2.symm.trans h2.2.2) m out
end defs

end k8s_correctness
end EtcdGrove
end Perennial
