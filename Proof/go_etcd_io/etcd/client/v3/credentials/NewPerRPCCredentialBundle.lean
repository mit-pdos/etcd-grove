/-
Proof of `Spec/go_etcd_io/etcd/client/v3/credentials/NewPerRPCCredentialBundle.lean` (the auth
plan's E2d). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.credentials.NewPerRPCCredentialBundle

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.credentials.Assumptions]

theorem credentials.NewPerRPCCredentialBundle.wp_proof :
    credentials.NewPerRPCCredentialBundle.spec (GF := GF) (hG := hG) := by
  wp_start as -
  wp_auto
  wp_alloc b as Hb
  iStructNamed Hb
  ipersist rc
  wp_auto
  iapply HΦ
  unfold tokenBundleAt
  iexists b, «$v0_ptr»
  iframe rc
  ipureintro; rfl

end proof

end EtcdGrove
end Perennial
