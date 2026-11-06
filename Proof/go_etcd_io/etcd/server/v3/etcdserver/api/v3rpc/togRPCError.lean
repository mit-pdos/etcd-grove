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
  wp_apply hIs S M err (GoInterface.ok ec) (fun tii h => by cases h; exact Hecp)
    (HS.2 (fun tii h => by cases h; exact Hecp))
    $$ [$Htree] as %b1 -
  · iframe #; ipureintro; exact HS.1
  wp_if_destruct
  rotate_left
  · iapply HΦ
    isplitr
    · ipureintro; exact Hnn
    iframe HSe
    iunfold v3rpc.grpcErrOut
    iexists mp, Mg, kf, kc
    iframe #
    ipureintro; exact ⟨HMv, Or.inl rfl⟩
  ihave ⟨%S', %M', #Htree', %HS'⟩ := HIsT $$ %de
  wp_apply hDE S' M' err de $$ [$Htree'] as %b2 -
  · iframe #; ipureintro; exact HS'.1
  wp_if_destruct
  rotate_left
  · iapply HΦ
    isplitr
    · ipureintro; exact Hnn
    iframe HSe
    iunfold v3rpc.grpcErrOut
    iexists mp, Mg, kf, kc
    iframe #
    ipureintro; exact ⟨HMv, Or.inl rfl⟩
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
    ipureintro; exact ⟨HMv, Or.inr (Or.inl hk)⟩
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
    iintro %e ⟨%He, #Hse, %Hd⟩
    wp_auto
    iapply HΦ
    isplitr
    · ipureintro; exact He
    ihave #Hse' := go_etcd_io.etcd.cache.v3.srvErrOk_of_statusErrOk _ $$ Hse
    iframe Hse'
    iunfold v3rpc.grpcErrOut
    iexists mp, Mg, kf, kc
    iframe #
    ipureintro; exact ⟨HMv, Or.inr (Or.inr ⟨hk, by rw [Hd]; exact Hmsg⟩)⟩

end proof

end EtcdGrove
end Perennial
