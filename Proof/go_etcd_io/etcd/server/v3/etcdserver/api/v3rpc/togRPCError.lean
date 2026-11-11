/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.togRPCError
public import Spec.errors.Is
public import Spec.errors.IsDeadlineExceeded
public import Spec.google_golang_org.grpc.status.Error

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.togRPCError.wp_proof
    (hIs : errors.Is.spec (GF := GF) (hG := hG))
    (hDE : errors.IsDeadlineExceeded.spec (GF := GF) (hG := hG))
    (hErr : status.Error.spec (GF := GF) (hG := hG)) :
    v3rpc.togRPCError.spec (GF := GF) (hG := hG) := by
  intro P err
  wp_start as ⟨#Herr, #HP⟩
  iunfold v3rpc.srvErrIs at Herr
  icases Herr with ⟨%Hnn, #HIs, %Hsafe, %ei, %Hei, -⟩
  ihave #HSe := applyErrIs_srvErrOk err $$ HIs
  ihave #Perr : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Pst : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status $$ []
  · iPkgInit
  ihave #Hinit : (go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.v3rpcInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨#Hmap, -, -, #Hcanc, -⟩
  iunfold go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.grpcErrMap at Hmap
  icases Hmap with ⟨%mp, %Mg, %kf, %kc, #Hmp, #HM, #HF, #HC, #HMS, #HMK, %HMv⟩
  ihave #Hctx : (_root_.Perennial.context.isInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Pctx
  icases Hctx with ⟨-, -, -, ⟨%de, #Hde, -⟩, -⟩
  iunfold go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ctxCanceledPtr at Hcanc
  icases Hcanc with ⟨%ec, #Hec, %Hecp⟩
  wp_auto
  ihave #HIsT := applyErrIs_tree err $$ HIs
  ihave ⟨%S, %M, #Htree, %HS⟩ := HIsT $$ %(GoInterface.ok ec)
  have hTT := HS.2 (fun tii h => by cases h; exact Hecp)
  -- (k8s etcd3 7c-2 part 2, G1-a′) a leaf without `Is` is a tree of itself alone, so that
  -- `errors.Is`'s witness says it is the target
  ihave ⟨%S0, %M0, #Htree0, %HS0⟩ : iprop(∃ (S0 : GoInterface → Prop) (M0 : GoInterfaceOk → Prop),
      _root_.Perennial.errors.errorIsTree (GF := GF) S0 M0 (GoInterface.ok ec) ∗
      ⌜S0 err ∧ _root_.Perennial.errors.TreeTyped S0 (GoInterface.ok ec) ∧
        ((∃ ei : GoInterfaceOk, err = GoInterface.ok ei ∧ _root_.Perennial.errors.isLeafError ei ∧ methodSet ei.ty !! go!"Is" ≠ some (go.Signature [go.error] false [go.bool])) → ∀ ii, S0 (GoInterface.ok ii) →
          (GoInterface.ok ii = GoInterface.ok ec ∨ M0 ii) → err = GoInterface.ok ec)⌝) $$ []
  · by_cases hL : (∃ ei : GoInterfaceOk, err = GoInterface.ok ei ∧ _root_.Perennial.errors.isLeafError ei ∧ methodSet ei.ty !! go!"Is" ≠ some (go.Signature [go.error] false [go.bool]))
    · obtain ⟨ei, hei, hl, hIs'⟩ := hL
      iexists (fun x : GoInterface => x = GoInterface.ok ei), (fun _ : GoInterfaceOk => False)
      isplitl
      · iapply _root_.Perennial.errors.errorIsTree_leaf ei _ _ hl hIs'
      ipureintro
      refine ⟨hei, ?_, ?_⟩
      · intro ii tii hS0 ht hty
        exact hTT ii tii (by rw [hS0, ← hei]; exact HS.1) ht hty
      · intro _ ii hS0 hor
        rcases hor with h | h
        · rw [hei, ← hS0]; exact h
        · exact h.elim
    · iexists S, M
      iframe Htree
      ipureintro
      exact ⟨HS.1, hTT, fun h => absurd h hL⟩
  wp_apply hIs S0 M0 err (GoInterface.ok ec) (fun tii h => by cases h; exact Hecp)
    HS0.2.1 $$ [$Htree0] as %b1 ⟨-, -, %Hw1⟩
  · iframe #; ipureintro; exact HS0.1
  wp_if_destruct
  rotate_left
  · iapply HΦ
    isplitr
    · ipureintro; exact Hnn
    iframe HSe
    iunfold v3rpc.grpcErrOut
    iexists mp, Mg, kf, kc
    iframe #
    isplitr
    · ipureintro; exact HMv
    ileft
    isplitr
    · ipureintro; rfl
    iunfold v3rpc.ctxPassed
    iintro !> %ei %Hl
    ileft
    obtain ⟨ii, hS0, hor⟩ := Hw1 ec rfl Hecp Hnn (by first | rfl | assumption | simp_all)
    have hE := HS0.2.2 ⟨ei, Hl.1, Hl.2.1, Hl.2.2⟩ ii hS0 hor
    rw [hE]
    iexact Hec
  ihave ⟨%S', %M', #Htree', %HS'⟩ := HIsT $$ %de
  ihave ⟨%S1, %M1, #Htree1, %HS1⟩ : iprop(∃ (S1 : GoInterface → Prop) (M1 : GoInterfaceOk → Prop),
      _root_.Perennial.errors.errorIsTree (GF := GF) S1 M1 de ∗
      ⌜S1 err ∧ ((∃ ei : GoInterfaceOk, err = GoInterface.ok ei ∧ _root_.Perennial.errors.isLeafError ei ∧ methodSet ei.ty !! go!"Is" ≠ some (go.Signature [go.error] false [go.bool])) → ∀ ii, S1 (GoInterface.ok ii) →
          (GoInterface.ok ii = de ∨ M1 ii) → err = de)⌝) $$ []
  · by_cases hL : (∃ ei : GoInterfaceOk, err = GoInterface.ok ei ∧ _root_.Perennial.errors.isLeafError ei ∧ methodSet ei.ty !! go!"Is" ≠ some (go.Signature [go.error] false [go.bool]))
    · obtain ⟨ei, hei, hl, hIs'⟩ := hL
      iexists (fun x : GoInterface => x = GoInterface.ok ei), (fun _ : GoInterfaceOk => False)
      isplitl
      · iapply _root_.Perennial.errors.errorIsTree_leaf ei _ _ hl hIs'
      ipureintro
      refine ⟨hei, ?_⟩
      intro _ ii hS1 hor
      rcases hor with h | h
      · rw [hei, ← hS1]; exact h
      · exact h.elim
    · iexists S', M'
      iframe Htree'
      ipureintro
      exact ⟨HS'.1, fun h => absurd h hL⟩
  wp_apply hDE S1 M1 err de $$ [$Htree1] as %b2 %Hw2
  · iframe #; ipureintro; exact HS1.1
  wp_if_destruct
  rotate_left
  · iapply HΦ
    isplitr
    · ipureintro; exact Hnn
    iframe HSe
    iunfold v3rpc.grpcErrOut
    iexists mp, Mg, kf, kc
    iframe #
    isplitr
    · ipureintro; exact HMv
    ileft
    isplitr
    · ipureintro; rfl
    iunfold v3rpc.ctxPassed
    iintro !> %ei %Hl
    iright
    obtain ⟨ii, hS1, hor⟩ := Hw2 (by first | rfl | assumption | simp_all)
    have hE := HS1.2 ⟨ei, Hl.1, Hl.2.1, Hl.2.2⟩ ii hS1 hor
    rw [hE]
    iexact Hde
  haveI := Hsafe
  wp_apply wp_map_lookup2 $$ HM as -
  cases hk : Mg !! err with
  | some v =>
    simp only [Option.getD_some, Option.isSome_some, decide_true]
    wp_auto
    iapply HΦ
    isplitr
    · ipureintro; exact go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.grpcErrMapOk_ne HMv err v hk
    isplitr
    · iapply go_etcd_io.etcd.cache.v3.srvErrOk_of_statusErrOk
      iapply HMS; ipureintro; exact hk
    iunfold v3rpc.grpcErrOut
    iexists mp, Mg, kf, kc
    iframe #
    isplitr
    · ipureintro; exact HMv
    iright; ileft
    ipureintro; exact hk
  | none =>
    simp only [Option.getD_none, Option.isSome_none]
    wp_auto
    subst Hei
    iunfold v3rpc.errMsgP at HP
    icases HP with ⟨%ei', %Hei', #HPM⟩
    cases Hei'
    wp_apply HPM as %msg %Hmsg
    wp_bind (App (App (Val #(functions google_golang_org.grpc.status.Error [])) (Val #(W32 2))) (Val #msg))
    iapply (hErr (W32 2) msg) $$ [] 
    · iframe #
      ipureintro
      simp only [google_golang_org.grpc.codes.OK]
      exact fun h => absurd (go.intoVal_inj h) (by decide)
    inext
    iintro %e ⟨%He, #Hse, %Hd, -⟩
    wp_auto
    iapply HΦ
    isplitr
    · ipureintro; exact He
    ihave #Hse' := go_etcd_io.etcd.cache.v3.srvErrOk_of_statusErrOk _ $$ Hse
    iframe Hse'
    iunfold v3rpc.grpcErrOut
    iexists mp, Mg, kf, kc
    iframe #
    isplitr
    · ipureintro; exact HMv
    iright; iright
    ipureintro; exact ⟨hk, by rw [Hd]; exact Hmsg⟩

end proof

end EtcdGrove
end Perennial
