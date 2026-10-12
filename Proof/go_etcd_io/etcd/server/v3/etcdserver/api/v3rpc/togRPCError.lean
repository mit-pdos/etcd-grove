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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.togRPCError.wp_proof
    (hIs : errors.Is.spec (GF := GF) (hG := hG))
    (hDE : errors.IsDeadlineExceeded.spec (GF := GF) (hG := hG))
    (hErr : status.Error.spec (GF := GF) (hG := hG)) :
    v3rpc.togRPCError.spec (GF := GF) (hG := hG) := by
  intro err
  wp_start as #Herr
  iunfold v3rpc.srvErrIs at Herr
  icases Herr with ⟨%Hnn, #HIs, %Hsafe, %ei, %Hei, #HErrM⟩
  ihave #Perr : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Pst : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status $$ []
  · iPkgInit
  ihave #Hinit : (go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.v3rpcInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨#Hmap, -, -, #Hcanc⟩
  ihave #Hctx : (_root_.Perennial.context.isInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Pctx
  icases Hctx with ⟨-, -, -, ⟨%de, #Hde, -⟩, -⟩
  iunfold go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ctxCanceledPtr at Hcanc
  icases Hcanc with ⟨%ec, #Hec, %Hecp⟩
  wp_auto
  iunfold applyErrIs at HIs
  ihave ⟨%S, %M, #Htree, %HS⟩ := HIs $$ %(GoInterface.ok ec)
  wp_apply hIs S M err (GoInterface.ok ec) (fun tii h => by cases h; exact Hecp) HS.2
    $$ [$Htree] as %b1 -
  · iframe #; ipureintro; exact HS.1
  wp_if_destruct
  rotate_left
  · iapply HΦ
    ipureintro; exact Hnn
  ihave ⟨%S', %M', #Htree', %HS'⟩ := HIs $$ %de
  wp_apply hDE S' M' err de $$ [$Htree'] as %b2 -
  · iframe #; ipureintro; exact HS'.1
  wp_if_destruct
  rotate_left
  · iapply HΦ
    ipureintro; exact Hnn
  iunfold go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.grpcErrMap at Hmap
  icases Hmap with ⟨%mp, %M, #Hmp, #HM, %HMv⟩
  wp_auto
  haveI := Hsafe
  wp_apply wp_map_lookup2 $$ HM as -
  cases hk : M !! err with
  | some v =>
    simp only [Option.getD_some, Option.isSome_some, decide_true]
    wp_auto
    iapply HΦ
    ipureintro; exact HMv err v hk
  | none =>
    simp only [Option.getD_none, Option.isSome_none]
    wp_auto
    subst Hei
    wp_apply HErrM as %msg _
    simp only [google_golang_org.grpc.codes.Unknown]
    wp_bind (App (App (Val #(functions google_golang_org.grpc.status.Error [])) (Val #(W32 2))) (Val #msg))
    iapply (hErr (W32 2) msg) $$ [] 
    · iframe #
      ipureintro
      simp only [google_golang_org.grpc.codes.OK]
      exact fun h => absurd (go.intoVal_inj h) (by decide)
    inext
    iintro %e ⟨%He, -⟩
    wp_auto
    iapply HΦ
    ipureintro; exact He

end proof

end EtcdGrove
end Perennial
