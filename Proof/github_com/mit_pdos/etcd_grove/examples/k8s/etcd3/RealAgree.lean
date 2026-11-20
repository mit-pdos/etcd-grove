/-
Lean-first (no Rocq counterpart).

# Equal values have equal views (k8s 7g step 5, decision 1)

`realCheck`'s porcupine model decodes a boxed `Request`/`Response` by the view of the first operation with
those values (`RealModel.decR`). Its step is `realS`'s on every operation's own view because operations
with equal values have views that step alike:

- `deepRep_agree`: an interface value has one deep value (read-only points-tos agree, the dynamic types
  tell the constructors apart);
- `respRep_agree`: a `Response` has one view, outside `RErr.other` (which says only "not nil").
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI Iris.ProofMode k8sDeep
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input)

section types
variable [GooseExts] [GoGlobalContext]

/-- The dynamic type a deep value's interface holds (`none`: the nil interface). -/
def deepTy : DeepV → Option go.GoType
  | .nil => none
  | .obj _ => some (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty)
  | .list _ _ _ _ => some (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList.ty)
  | .storageErr _ _ _ _ => some (go.GoType.PointerType k8s_io.apiserver.pkg.storage.StorageError.ty)
  | .errString _ => some (go.GoType.PointerType _root_.Perennial.errors.errorString.ty)

/-- The constructor of a deep value. -/
def deepCtor : DeepV → Nat
  | .nil => 0
  | .obj _ => 1
  | .list _ _ _ _ => 2
  | .storageErr _ _ _ _ => 3
  | .errString _ => 4

theorem deepTy_ctor (d1 d2 : DeepV) (h : deepTy d1 = deepTy d2) : deepCtor d1 = deepCtor d2 := by
  cases d1 <;> cases d2 <;> simp only [deepTy, deepCtor, reduceCtorEq, Option.some.injEq,
    go.GoType.PointerType.injEq] at h ⊢ <;>
    first
    | rfl
    | (simp only [github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty,
          github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList.ty,
          k8s_io.apiserver.pkg.storage.StorageError.ty, _root_.Perennial.errors.errorString.ty,
          go.GoType.Named.injEq] at h; exact absurd h.1 (by decide))

theorem statusError_ne_deepTy (d : DeepV) :
    deepTy d ≠ some (go.GoType.PointerType k8s_io.apimachinery.pkg.api.errors.StatusError.ty) := by
  intro h
  cases d <;> simp only [deepTy, reduceCtorEq, Option.some.injEq, go.GoType.PointerType.injEq] at h <;>
    (simp only [github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty,
        github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList.ty,
        k8s_io.apiserver.pkg.storage.StorageError.ty, _root_.Perennial.errors.errorString.ty,
        k8s_io.apimachinery.pkg.api.errors.StatusError.ty, go.GoType.Named.injEq] at h;
      exact absurd h.1 (by decide))

end types

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]

/-- An interface value holds the dynamic type `t` (`none`: it is nil). -/
def tyRep (x : GoInterface) : Option go.GoType → Prop
  | none => x = GoInterface.nil
  | some T => ∃ p : Loc, x = interface.mkOk T #p

include sem in
theorem mkOk_loc_inj (T1 T2 : go.GoType) (p1 p2 : Loc)
    (h : interface.mkOk T1 #p1 = interface.mkOk T2 #p2) : T1 = T2 ∧ p1 = p2 := by
  have h' := GoInterfaceOk.mk.inj (GoInterface.ok.inj h)
  exact ⟨h'.1, go.intoVal_inj h'.2⟩

include sem in
theorem tyRep_agree (x : GoInterface) (t1 t2 : Option go.GoType) (h1 : tyRep x t1) (h2 : tyRep x t2) :
    t1 = t2 := by
  cases t1 <;> cases t2 <;> simp only [tyRep] at h1 h2
  · rfl
  · obtain ⟨p, h⟩ := h2; rw [h1] at h; cases h
  · obtain ⟨p, h⟩ := h1; rw [h2] at h; cases h
  · obtain ⟨p, rfl⟩ := h1
    obtain ⟨q, h⟩ := h2
    rw [(mkOk_loc_inj (sem := sem) _ _ _ _ h).1]

/-- **A deep value's interface holds its dynamic type.** -/
theorem deepRep_ty (dq : DFrac) (x : GoInterface) (d : DeepV) :
    deepRep (GF := GF) dq x d ⊢
      ⌜tyRep x (deepTy d)⌝ := by
  cases d <;> simp only [deepRep, deepTy, tyRep]
  · iintro %h; ipureintro; exact h
  · iintro ⟨%p, %h, -⟩; ipureintro; exact ⟨p, h⟩
  · iintro ⟨%p, %sl, %rp, %h, -⟩; ipureintro; exact ⟨p, h⟩
  · iintro ⟨%p, %e, %h, -⟩; ipureintro; exact ⟨p, h⟩
  · iintro ⟨%p, %h, -⟩; ipureintro; exact ⟨p, h⟩

/-- **An interface value has one deep value.** -/
theorem deepRep_agree (dq1 dq2 : DFrac) : ∀ (d1 d2 : DeepV) (x : GoInterface),
    deepRep (GF := GF) dq1 x d1 ∗ deepRep dq2 x d2 ⊢ ⌜d1 = d2⌝ := by
  intro d1
  induction d1 with
  | nil =>
    intro d2 x
    iintro ⟨H1, H2⟩
    ihave %t1 := deepRep_ty dq1 x .nil $$ H1
    ihave %t2 := deepRep_ty dq2 x d2 $$ H2
    have hc := deepTy_ctor _ _ (tyRep_agree (sem := sem) x _ _ t1 t2)
    cases d2 <;> simp only [deepCtor] at hc <;> first | omega | skip
    ipureintro; rfl
  | obj o =>
    intro d2 x
    iintro ⟨H1, H2⟩
    ihave %t1 := deepRep_ty dq1 x (.obj o) $$ H1
    ihave %t2 := deepRep_ty dq2 x d2 $$ H2
    have hc := deepTy_ctor _ _ (tyRep_agree (sem := sem) x _ _ t1 t2)
    cases d2 <;> simp only [deepCtor] at hc <;> first | omega | skip
    rename_i o2
    simp only [deepRep]
    icases H1 with ⟨%p1, %h1, H1⟩
    icases H2 with ⟨%p2, %h2, H2⟩
    obtain ⟨-, rfl⟩ := mkOk_loc_inj (sem := sem) _ _ _ _ (h1.symm.trans h2)
    icombine H1 H2 gives %h
    ipureintro; rw [h]
  | list its rv cont rem =>
    intro d2 x
    iintro ⟨H1, H2⟩
    ihave %t1 := deepRep_ty dq1 x (.list its rv cont rem) $$ H1
    ihave %t2 := deepRep_ty dq2 x d2 $$ H2
    have hc := deepTy_ctor _ _ (tyRep_agree (sem := sem) x _ _ t1 t2)
    cases d2 <;> simp only [deepCtor] at hc <;> first | omega | skip
    rename_i its2 rv2 cont2 rem2
    simp only [deepRep]
    icases H1 with ⟨%p1, %sl1, %rp1, %h1, H1, Hi1, Hr1⟩
    icases H2 with ⟨%p2, %sl2, %rp2, %h2, H2, Hi2, Hr2⟩
    obtain ⟨-, rfl⟩ := mkOk_loc_inj (sem := sem) _ _ _ _ (h1.symm.trans h2)
    icombine H1 H2 gives %h
    simp only [github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    ihave %hi : ⌜its = its2⌝ $$ [Hi1 Hi2]
    · cases its <;> cases its2 <;> simp only [itemsRep]
      · ipureintro; trivial
      · icases Hi1 with %e1; icases Hi2 with ⟨%e2, -⟩; exact absurd e1 e2
      · icases Hi1 with ⟨%e1, -⟩; icases Hi2 with %e2; exact absurd e2 e1
      · icases Hi1 with ⟨-, Hs1⟩; icases Hi2 with ⟨-, Hs2⟩
        ihave %e := ownSlice_agree _ _ _ _ _ $$ Hs1 Hs2
        ipureintro; rw [e]
    ihave %hr : ⌜rem = rem2⌝ $$ [Hr1 Hr2]
    · cases rem <;> cases rem2 <;> simp only [remRep]
      · ipureintro; trivial
      · icases Hr1 with %e1
        ihave %hn := typedPointsto_not_null _ _ _ $$ Hr2
        exact absurd e1 hn
      · icases Hr2 with %e2
        ihave %hn := typedPointsto_not_null _ _ _ $$ Hr1
        exact absurd e2 hn
      · icombine Hr1 Hr2 gives %e
        ipureintro; rw [e]
    ipureintro; rw [hi, hr]
  | storageErr code key rv inner ih =>
    intro d2 x
    iintro ⟨H1, H2⟩
    ihave %t1 := deepRep_ty dq1 x (.storageErr code key rv inner) $$ H1
    ihave %t2 := deepRep_ty dq2 x d2 $$ H2
    have hc := deepTy_ctor _ _ (tyRep_agree (sem := sem) x _ _ t1 t2)
    cases d2 <;> simp only [deepCtor] at hc <;> first | omega | skip
    rename_i code2 key2 rv2 inner2
    simp only [deepRep]
    icases H1 with ⟨%p1, %e1, %h1, H1, Hn1⟩
    icases H2 with ⟨%p2, %e2, %h2, H2, Hn2⟩
    obtain ⟨-, rfl⟩ := mkOk_loc_inj (sem := sem) _ _ _ _ (h1.symm.trans h2)
    icombine H1 H2 gives %h
    simp only [k8s_io.apiserver.pkg.storage.StorageError.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    ihave %hi := ih inner2 e1 $$ [Hn1 Hn2]
    · iframe
    ipureintro; rw [hi]
  | errString s =>
    intro d2 x
    iintro ⟨H1, H2⟩
    ihave %t1 := deepRep_ty dq1 x (.errString s) $$ H1
    ihave %t2 := deepRep_ty dq2 x d2 $$ H2
    have hc := deepTy_ctor _ _ (tyRep_agree (sem := sem) x _ _ t1 t2)
    cases d2 <;> simp only [deepCtor] at hc <;> first | omega | skip
    rename_i s2
    simp only [deepRep]
    icases H1 with ⟨%p1, %h1, H1⟩
    icases H2 with ⟨%p2, %h2, H2⟩
    obtain ⟨-, rfl⟩ := mkOk_loc_inj (sem := sem) _ _ _ _ (h1.symm.trans h2)
    icombine H1 H2 gives %h
    simp only [_root_.Perennial.errors.errorString.mk.injEq] at h
    ipureintro; rw [h]

/-- **An error value has one view**, outside `RErr.other`. -/
theorem errRep_agree (x : GoInterface) (e1 e2 : RErr) (h1 : e1 ≠ .other) (h2 : e2 ≠ .other) :
    errRep (GF := GF) x e1 ∗ errRep x e2 ⊢ ⌜e1 = e2⌝ := by
  iintro ⟨H1, H2⟩
  cases e1 with
  | other => exact absurd rfl h1
  | deep d1 =>
    cases e2 with
    | other => exact absurd rfl h2
    | deep d2 =>
      simp only [errRep, deepRO]
      ihave %h := deepRep_agree DFrac.discard DFrac.discard d1 d2 x $$ [H1 H2]
      · iframe
      ipureintro; rw [h]
    | tooLarge dl =>
      simp only [errRep, deepRO]
      ihave %t1 := deepRep_ty DFrac.discard x d1 $$ H1
      icases H2 with ⟨-, %l, %st, %dv, %h, -⟩
      have t2 : tyRep x (some (go.GoType.PointerType k8s_io.apimachinery.pkg.api.errors.StatusError.ty)) :=
        ⟨l, h.1⟩
      exact absurd (tyRep_agree (sem := sem) x _ _ t1 t2) (statusError_ne_deepTy d1)
  | tooLarge dl1 =>
    cases e2 with
    | other => exact absurd rfl h2
    | deep d2 =>
      simp only [errRep, deepRO]
      ihave %t2 := deepRep_ty DFrac.discard x d2 $$ H2
      icases H1 with ⟨-, %l, %st, %dv, %h, -⟩
      have t1 : tyRep x (some (go.GoType.PointerType k8s_io.apimachinery.pkg.api.errors.StatusError.ty)) :=
        ⟨l, h.1⟩
      exact absurd (tyRep_agree (sem := sem) x _ _ t2 t1) (statusError_ne_deepTy d2)
    | tooLarge dl2 =>
      simp only [errRep]
      icases H1 with ⟨-, %l1, %st1, %dv1, %h1, #Hl1, #Hd1⟩
      icases H2 with ⟨-, %l2, %st2, %dv2, %h2, #Hl2, #Hd2⟩
      obtain ⟨-, rfl⟩ := mkOk_loc_inj (sem := sem) _ _ _ _ (h1.1.symm.trans h2.1)
      icombine Hl1 Hl2 gives %hs
      simp only [k8s_io.apimachinery.pkg.api.errors.StatusError.mk.injEq] at hs
      subst hs
      icombine Hd1 Hd2 gives %hd
      subst hd
      ipureintro; rw [← h1.2.2, ← h2.2.2]

/-- **A `Response` has one view**, outside `RErr.other`. -/
theorem respRep_agree (ro : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Response)
    (r1 r2 : RResp) (h1 : r1.err ≠ .other) (h2 : r2.err ≠ .other) :
    respRep (GF := GF) ro r1 ∗ respRep ro r2 ⊢ ⌜r1 = r2⌝ := by
  iintro ⟨H1, H2⟩
  iunfold respRep at H1 H2
  icases H1 with ⟨Ho1, He1⟩
  icases H2 with ⟨Ho2, He2⟩
  ihave %ho := deepRep_agree DFrac.discard DFrac.discard r1.obj r2.obj ro.Object' $$ [Ho1 Ho2]
  · iframe
  ihave %he := errRep_agree ro.Err' r1.err r2.err h1 h2 $$ [He1 He2]
  · iframe
  ipureintro
  cases r1; cases r2
  simp only at ho he
  rw [ho, he]

end defs

end k8s_correctness
end EtcdGrove
end Perennial
