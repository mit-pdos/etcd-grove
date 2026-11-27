/-
`rpctypes.EtcdError` as a target of Go's `errors.Is`: a struct of a `codes.Code` and a `string`,
whose `==` compares the two fields (`go_eq_struct`), so it is comparable with the errors of a tree
whose errors of its type hold `EtcdError` values (`errors.ComparableErr`).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3.v3rpc.rpctypes

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [ta : EtcdError.TypeAssumptions]
variable [tc : _root_.Perennial.google_golang_org.grpc.codes.Code.TypeAssumptions]

/-- Two `EtcdError`s are equal when their fields are. -/
theorem etcdError_eq_iff (x y : EtcdError) : x = y ↔ x.code' = y.code' ∧ x.desc' = y.desc' := by
  cases x; cases y; simp

instance etcdError_decEq : DecidableEq EtcdError :=
  fun x y => decidable_of_iff _ (etcdError_eq_iff x y).symm

omit tc in
include ta in
/-- `#` is injective on `EtcdError`: its fields read back (`get_code`, `get_desc`). -/
theorem etcdError_intoVal_inj : Function.Injective (intoVal (V := EtcdError)) := by
  intro x y h
  have kc := (EtcdError.TypeAssumptions.get_code x).isGoStep_det_internal.isGoStep_pure_det
  have kc' := (EtcdError.TypeAssumptions.get_code y).isGoStep_det_internal.isGoStep_pure_det
  have kd := (EtcdError.TypeAssumptions.get_desc x).isGoStep_det_internal.isGoStep_pure_det
  have kd' := (EtcdError.TypeAssumptions.get_desc y).isGoStep_det_internal.isGoStep_pure_det
  have h' : (#x : val) = #y := h
  rw [h'] at kc kd
  have ec := congrFun (kc.symm.trans kc') (Val #(x.code'))
  have ed := congrFun (kd.symm.trans kd') (Val #(x.desc'))
  simp only [eq_iff_iff, true_iff] at ec ed
  have fc : (#(x.code') : val) = #(y.code') := by injection ec.symm
  have fd : (#(x.desc') : val) = #(y.desc') := by injection ed.symm
  exact (etcdError_eq_iff x y).2 ⟨go.intoVal_inj fc, go.intoVal_inj fd⟩

/-- `EtcdError`'s `==` is defined: its fields' types are comparable (`codes.Code` through its
underlying `uint32`; the struct rule asks it of each field type with the tag `under`, a label of the
instance, `IsGoStepPureDetTagged`, over the same step). -/
theorem etcdError_checkComparable : ⟦CheckComparable EtcdError.ty, #()⟧ ⤳ #() := by
  haveI : ⟦CheckComparable _root_.Perennial.google_golang_org.grpc.codes.Code.ty, #()⟧ ⤳[under] #() :=
    ⟨inferInstance⟩
  haveI : ⟦CheckComparable (go.StructType EtcdError.fields), #()⟧ ⤳[under] #() := by
    rw [show EtcdError.fields = EtcdError.fieldsUnsealed from by unfold EtcdError.fields; rfl]
    infer_instance
  infer_instance

/-- `EtcdError`'s `==` evaluates to the equality of the two values (field by field). -/
theorem etcdError_eq_pureWp (x y : EtcdError) :
    PureWp (GF := GF) True (App (Val (GoInstruction (GoOp GoEquals EtcdError.ty))) (Val (PairV #x #y)))
      (Val #(decide (x = y))) := by
  have hd : decide (x = y) = decide (x.code' = y.code' ∧ x.desc' = y.desc') :=
    decide_eq_decide.2 (etcdError_eq_iff x y)
  rw [hd]
  refine pure_wp_val _ _ _ fun s E Φ _ => ?_
  -- the first step: `go_eq_struct`, to the comparison of the fields
  refine .trans ?_ ((pure_wp_go_step_det (GF := GF) _ _ _).pure_wp_wp s E Φ [] rfl)
  iintro H
  inext
  iintro Hlc
  ihave H := H $$ Hlc
  simp only [Iris.ProgramLogic.fill, List.foldl]
  wp_auto
  by_cases hc : x.code' = y.code'
  · simp only [hc, decide_true]
    wp_auto
    by_cases hd2 : x.desc' = y.desc'
    · simp [hd2]
      iexact H
    · simp [hd2]
      iexact H
  · simp [hc]
    wp_auto
    iexact H

/-- An `EtcdError` target is comparable with the errors of a tree whose errors of its type hold
`EtcdError` values (Go's typing). -/
theorem etcdError_comparable (S : GoError → Prop) (x : EtcdError)
    (htyped : ∀ ii : GoInterfaceOk, S (interface.ok ii) → ii.ty = EtcdError.ty →
      ∃ v : EtcdError, ii.v = #v) :
    _root_.Perennial.errors.ComparableErr (GF := GF) S ⟨EtcdError.ty, #x⟩ :=
  ⟨EtcdError, inferInstance, etcdError_intoVal_inj (GF := GF) (hlc := hlc),
    etcdError_checkComparable (GF := GF) (hlc := hlc),
    fun v1 v2 => etcdError_eq_pureWp (GF := GF) v1 v2, ⟨x, rfl⟩, htyped⟩

end lemmas

end EtcdGrove
end Perennial
