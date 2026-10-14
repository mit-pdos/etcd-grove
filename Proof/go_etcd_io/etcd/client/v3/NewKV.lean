/-
Proof of `Spec/go_etcd_io/etcd/client/v3/NewKV.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.NewKV
public import Spec.go_etcd_io.etcd.client.v3.RetryKVClient

@[expose] public section

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

theorem NewKV.wp_proof (wp_RetryKVClient : RetryKVClient.spec (GF := GF) (hG := hG)) :
    NewKV.spec (GF := GF) (hG := hG) := by
  intro cl K
  wp_start as #Hcl
  iunfold clientKVAt at Hcl
  icases Hcl with ⟨%Hne, %conn, %sl, #Hconn, #Hkc, #Hcopts, #Hok⟩
  wp_auto
  wp_apply wp_RetryKVClient cl conn $$ [] as %v ⟨%rkv, %Hv, #Hrkv⟩
  · iexact Hconn
  subst Hv
  iStructNamed «$r0»
  ipersist remote
  simp only [decide_eq_false Hne]
  iapply wp_fupd
  wp_auto
  ipersist callOpts
  imodintro
  iapply HΦ
  iexists _
  isplitl []
  · ipureintro; rfl
  unfold kvObjAt
  iexists rkv, conn, sl
  iframe #

end proof

end EtcdGrove
end Perennial
