/-
Proof of `Spec/go_etcd_io/etcd/client/v3/WithChannelKey.lean` (PR #21765).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.WithChannelKey

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem WithChannelKey.wp_proof
    (wp_WithValue : context.WithValue.spec (GF := GF) (hG := hG)) :
    WithChannelKey.spec (GF := GF) (hG := hG) := by
  intro ctx cd key
  wp_start as #Hctx
  ihave #HctxPkg : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  wp_auto
  wp_apply (wp_WithValue ctx ⟨go_etcd_io.etcd.client.v3.channelKeyContextKey.ty,
      #(zero_val go_etcd_io.etcd.client.v3.channelKeyContextKey)⟩ (interface.mkOk go.string #key))
    $$ [] as %c ⟨-, -, -, %c', %vs, %Hc, -, #Hic, -, -, #Hk, -⟩
  · iframe #; ipureintro; right; right; right; right; right; rfl
  subst Hc
  ihave #Hctx' := Hic $$ %cd Hctx
  ihave #Hk' : clientv3.ctxChannelKeyIs (GF := GF) (GoInterface.ok c') (some key) $$ []
  · iapply Hk
    ipureintro; rfl
  iapply HΦ
  iexists c', vs
  iframe Hctx' Hk'
  ipureintro; rfl

end proof

end EtcdGrove
end Perennial
