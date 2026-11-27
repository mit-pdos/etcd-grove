/-
`errors.Is` of an error grpc accepts (`statusErrOk`), against an `EtcdError` value, a pointer error
or `deadlineExceededError{}`, proved over Perennial's `errors.Is` at comparable targets. It was a
trust-boundary axiom until #45 (2026-11-25).

The tree is the error alone (`statusErrOk`: a leaf). Its `Is` method, if it has one, answers
`true` only for a target with the same description (`grpcErrMethodsOk`'s `Is` clause, at the
descriptions the caller fixes or at some descriptions of the two). The target is comparable with
it (`errors.ComparableErr`): an `EtcdError` by its two fields (`etcdError_comparable`), a pointer
error, `deadlineExceededError{}` (`deadlineExceededError_comparable`), each with the error's
typing (`stTypedErr`). Go's walk answers `true` only at the error if it is the target or its `Is`
said so (`errors.isWalkL_true_mem`).
-/
module

public import Spec.errors.IsStatusErr
public import Perennial.Spec.errors.Is
public import Proof.errors.CtxErr
public import Proof.errors.EtcdErrorCmp

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.errors.Assumptions]
variable [ctx_sem : _root_.Perennial.context.Assumptions]
variable [ta : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.TypeAssumptions]
variable [tc : _root_.Perennial.google_golang_org.grpc.codes.Code.TypeAssumptions]

/-- The three targets of `errors.IsStatusErr.spec` are comparable with a tree of typed errors. -/
theorem statusErr_comparableTarget (S : GoError → Prop) (target : GoInterface)
    (htgt : (∃ x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError,
        target = interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x) ∨
      (∃ tii, target = GoInterface.ok tii ∧ _root_.Perennial.errors.IsPointerError tii) ∨
      target = interface.mkOk _root_.Perennial.context.deadlineExceededError.ty
        #(zero_val _root_.Perennial.context.deadlineExceededError))
    (hS : ∀ ii, S (interface.ok ii) → stTypedErr ii) :
    _root_.Perennial.errors.ComparableTarget (GF := GF) S target := by
  intro tii ht
  rcases htgt with ⟨x, rfl⟩ | ⟨tii', rfl, hp⟩ | rfl
  · cases ht
    exact etcdError_comparable S x (fun ii hSi hty => (hS ii hSi).1 hty)
  · cases ht
    apply _root_.Perennial.errors.comparableErr_pointer _ _ hp
    intro ii tjj hSi htj hty
    cases htj
    obtain ⟨T, l, hT, -⟩ := hp
    exact (hS ii hSi).2.2 T (hty.trans hT)
  · cases ht
    exact deadlineExceededError_comparable S (fun ii hSi hty => (hS ii hSi).2.1 hty)

theorem errors.IsStatusErr.wp_proof
    (wp_Is : _root_.Perennial.errors.Is.spec (GF := GF) (hG := hG)) :
    errors.IsStatusErr.spec (GF := GF) (hG := hG) := by
  intro err target dm htgt
  iintro %Φ ⟨#Hinit, #Hse, #Hds, ⟨%mt, #Hmt⟩⟩ HΦ
  have htnil : target ≠ GoInterface.nil := by
    rcases htgt with ⟨x, rfl⟩ | ⟨tii, rfl, -⟩ | rfl <;> simp [interface.mkOk]
  cases err with
  | nil =>
    -- `errors.Is(nil, target)` is `nil == target`: `false`
    have hcmp := statusErr_comparableTarget (GF := GF) (· = GoInterface.nil) target htgt
      (fun ii h => by cases h)
    ihave #Htree : _root_.Perennial.errors.errorIsTree (GF := GF) (· = GoInterface.nil)
        (fun _ => False) target $$ []
    · iintro !> %ii %h
      cases h
    wp_apply +noauto wp_Is (· = GoInterface.nil) _ _ GoInterface.nil target hcmp
      $$ [$Hinit $Htree] as %b ⟨%Hnil, -⟩
    · ipureintro; rfl
    iapply HΦ
    ipureintro
    intro hb
    have h := Hnil (Or.inl rfl)
    rw [hb] at h
    exact absurd (of_decide_eq_true h.symm).symm htnil
  | ok e =>
    ihave ⟨%me, #Hme⟩ := statusErrOk_descIs (GoInterface.ok e) $$ Hse
    iunfold statusErrOk at Hse
    icases Hse $$ %e %rfl with ⟨-, %hleaf, #Hg, -, %hty⟩
    -- what an `Is` method's `true` means: the descriptions the caller fixes agree
    let M : GoInterfaceOk → Prop := fun ii =>
      (∀ m m', dm = some (m, m') → m = m') ∧
        methodSet ii.ty !! go!"Is" = some (go.Signature [go.error] false [go.bool])
    have hcmp := statusErr_comparableTarget (GF := GF) (· = GoInterface.ok e) target htgt
      (fun ii h => by cases h; exact hty)
    ihave #Htree : _root_.Perennial.errors.errorIsTree (GF := GF) (· = GoInterface.ok e) M
        target $$ []
    · iintro !> %ii %h
      cases h
      obtain ⟨-, hU1, hU2⟩ := hleaf
      unfold _root_.Perennial.errors.errorWalkNode
      simp only [hU1, hU2, ↓reduceIte]
      isplitl
      · by_cases hIs : methodSet e.ty !! go!"Is" = some (go.Signature [go.error] false [go.bool])
        · simp only [hIs, ↓reduceIte]
          unfold grpcErrMethodsOk
          icases Hg with ⟨-, HIs⟩
          ihave #HIs' := HIs $$ %hIs
          iintro !> %Ψ - HΨ
          cases dm with
          | none =>
            iapply HIs' $$ %target %me %mt %Ψ Hme Hmt
            inext
            iintro %b %-
            iapply HΨ
            ipureintro
            intro _
            exact ⟨fun m m' h => (by cases h), hIs⟩
          | some p =>
            obtain ⟨m, m'⟩ := p
            iunfold isDescs at Hds
            icases Hds with ⟨#Hd1, #Hd2⟩
            iapply HIs' $$ %target %m %m' %Ψ Hd1 Hd2
            inext
            iintro %b %hb
            iapply HΨ
            ipureintro
            intro h
            exact ⟨fun _ _ hs => by cases hs; exact hb h, hIs⟩
        · simp only [hIs, ↓reduceIte]
          ipureintro
          intro h
          cases h
      · ipureintro
        intro _ h
        cases h
    wp_apply +noauto wp_Is (· = GoInterface.ok e) _ _ (GoInterface.ok e) target hcmp
      $$ [$Hinit $Htree] as %b ⟨-, %Hw⟩
    · ipureintro; rfl
    iapply HΦ
    ipureintro
    intro hb
    subst hb
    obtain ⟨ii, hii, hor⟩ := _root_.Perennial.errors.isWalkL_true_mem (Hw (by simp) htnil)
      (fun e' he => by rw [List.mem_singleton.mp he])
    cases hii
    refine ⟨fun m m' hdm => ?_, fun hx e' he hnis => ?_⟩
    · rcases hor with heq | hM
      · exact .inl heq
      · exact .inr (hM.1 m m' hdm)
    · cases he
      rcases hor with heq | hM
      · obtain ⟨x, rfl⟩ := hx
        simp only [interface.mkOk] at heq
        injection heq with heq
        rw [heq]
      · exact absurd hM.2 hnis

end proof

end EtcdGrove
end Perennial
