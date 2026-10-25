/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/streamReader__close.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamReader__close
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Error
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String_ptr

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

theorem rafthttp.streamReader.close.wp_proof
    (hCloseAny : http.RespCloseAny_spec (GF := GF))
    (hWarn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hZString : zap.String.spec (GF := GF) (hG := hG))
    (hZError : zap.Error.spec (GF := GF) (hG := hG))
    (hIDStringPtr : types.ID.String_ptr.spec (GF := GF) (hG := hG)) :
    rafthttp.streamReader.close.spec (GF := GF) (hG := hG) := by
  intro Rh lid pid γd cr c
  wp_start as ⟨#Hf, Hcl, Hc⟩
  iunfold srFixed at Hf
  icases Hf with ⟨%lg, %tr, %ps, %rc, %pc, %γr, %γp, %ctx, %cd, #Hlg, %Hlgnn, #Hpid, #Htr,
    #Hlid, -, -, -, -, -, -, -, -, -⟩
  wp_auto
  icases Hc with (%Hc | #Hc)
  · subst Hc
    wp_auto
    iapply HΦ
    iframe
  · cases c with
    | nil => wp_auto; iapply HΦ; iframe
    | ok ci =>
      wp_auto
      wp_apply hCloseAny (GoInterface.ok ci) ci rfl $$ [] as %err #Herr
      · iexact Hc
      cases err with
      | nil => wp_auto; iapply HΦ; iframe
      | ok ei =>
        wp_auto
        wp_if_destruct
        · exact absurd rfl Hlgnn
        wp_apply hIDStringPtr _ DFrac.discard lid $$ [] as %ls -
        · iframe #
        wp_apply hZString as %f1 -
        wp_apply hIDStringPtr _ DFrac.discard pid $$ [] as %ps' -
        · iframe #
        wp_apply hZString as %f2 -
        wp_apply hZError as %f3 -
        wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2, f3]
        isplitr
        · ipureintro; rfl
        iintro %fsl ⟨-, -⟩
        (try wp_auto)
        wp_apply hWarn lg _ _ $$ []
        · iframe #; ipureintro; exact Hlgnn
        (try wp_auto)
        iapply HΦ
        iframe

end proof

end EtcdGrove
end Perennial
