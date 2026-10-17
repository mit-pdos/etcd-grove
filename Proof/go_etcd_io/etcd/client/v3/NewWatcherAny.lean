/-
Proof of `Spec/go_etcd_io/etcd/client/v3/NewWatcherAny.lean` (pr-verify etcd#21714). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.NewWatcherAny
public import Spec.go_etcd_io.etcd.client.v3.NewWatchFromWatchClientAny
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.NewWatchClient

@[expose] public section

set_option linter.unusedSectionVars false

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

theorem NewWatcherAny.wp_proof
    (wp_NewWatchClient : NewWatchClient.spec (GF := GF) (hG := hG))
    (wp_NewWatchFromWatchClientAny : NewWatchFromWatchClientAny.spec (GF := GF) (hG := hG)) :
    NewWatcherAny.spec (GF := GF) (hG := hG) := by
  intro c
  wp_start as #Hc
  iunfold clientConnAt at Hc
  icases Hc with ⟨%cl, #Hfix, #Hconn⟩
  wp_auto
  wp_apply wp_NewWatchClient as %v -
  wp_apply wp_NewWatchFromWatchClientAny v c $$ [] as %wi -
  · iframe #
    unfold clientConnAt
    iexists cl
    iframe #
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
