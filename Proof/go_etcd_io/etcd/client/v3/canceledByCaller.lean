/-
Proof of `Spec/go_etcd_io/etcd/client/v3/canceledByCaller.lean` (item 1, the client lease).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.canceledByCaller
public import Spec.errors.IsStatusErr

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

set_option maxHeartbeats 0 in
theorem canceledByCaller.wp_proof (wp_Is : errors.IsStatusErr.spec (GF := GF) (hG := hG)) :
    canceledByCaller.spec (GF := GF) (hG := hG) := by
  intro sc scd err
  wp_start as ⟨#Hce, #Htg, #Hse⟩
  ihave #Hctxp : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Herrp : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  iunfold ctxErrTargets at Htg
  icases Htg with ⟨⟨%ec, #Hec, %Hlc⟩, ⟨%ed, #Hed, %Hld⟩⟩
  wp_auto
  iunfold ctxErrClient at Hce
  ihave #HU := Hce $$ %Broadcast.Unknown
  wp_apply HU $$ [] as %e0 - %- - -
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
        (Or.inr (Or.inl ⟨ec, rfl, Hlc⟩))) $$ [] as %b1 -
      · iframe #
      cases b1
      · wp_auto
        wp_apply (wp_Is (GoInterface.ok erri) (GoInterface.ok ed)
          (Or.inr (Or.inr ⟨ed, rfl, Hld⟩))) $$ [] as %b2 -
        · iframe #
        (try wp_auto)
        iapply HΦ; itrivial
      · (try wp_auto)
        iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
