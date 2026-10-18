/-
Proof of `Spec/go_etcd_io/etcd/client/v3/canceledByCaller.lean` (item 1, the client lease).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.canceledByCaller
public import Spec.errors.IsStatusErr
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.read.Init

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)]

set_option maxHeartbeats 0 in
theorem canceledByCaller.wp_proof (wp_Is : errors.IsStatusErr.spec (GF := GF) (hG := hG)) :
    canceledByCaller.spec (GF := GF) (hG := hG) := by
  intro sc scd err
  wp_start as ⟨#Hce, #Hse⟩
  ihave #Hctxp : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Herrp : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  ihave ⟨#HC, #HD⟩ := EtcdGrove.ContextReadErrs.errs $$ Hctxp
  iunfold EtcdGrove.errVarLeaf at HC
  icases HC with ⟨%ec, #Hec, %Hlc, -⟩
  icases HD with ⟨%ed, #Hed, %Hld, -⟩
  wp_auto
  iunfold ctxErrClient at Hce
  ihave #HU := Hce $$ %Broadcast.Unknown
  wp_apply HU $$ [] as %e0 - %- -
  cases e0 with
  | nil =>
    wp_auto
    iapply HΦ; itrivial
  | ok e0i =>
    wp_auto
    cases err with
    | nil =>
      wp_auto
      iapply HΦ; itrivial
    | ok erri =>
      wp_auto
      wp_apply (wp_Is (GoInterface.ok erri) (GoInterface.ok ec)
        (Or.inr (Or.inl ⟨ec, rfl, Hlc.1⟩))) $$ [] as %b1 -
      · iframe #
      cases b1
      · wp_auto
        wp_apply (wp_Is (GoInterface.ok erri) (GoInterface.ok ed)
          (Or.inr (Or.inr ⟨ed, rfl, Hld.2.2.2⟩))) $$ [] as %b2 -
        · iframe #
        (try wp_auto)
        iapply HΦ; itrivial
      · (try wp_auto)
        iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
