/-
Proof of the spec of the same name (revoke-open pass 2, 2026-11-06): the auth-off branch of
`WithRoot`, over the caller's `IsAuthEnabled` contract. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__WithRoot

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.authStore.WithRoot.wp_proof :
    auth.authStore.WithRoot.spec (GF := GF) (hG := hG) := by
  intro st RD ctx
  wp_start as ⟨HRD, #HIE⟩
  wp_method_call; wp_call
  (try wp_auto)
  wp_method_call
  wp_apply HIE $$ HRD as %b ⟨HRD, %Hb⟩
  subst Hb
  (try wp_auto)
  iapply HΦ; iexact HRD

end proof

end EtcdGrove
end Perennial
