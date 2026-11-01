/-
Proof of `Spec/go_etcd_io/etcd/server/v3/auth/authStore__BcryptCost.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__BcryptCost

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

theorem auth.authStore.BcryptCost.wp_proof :
    auth.authStore.BcryptCost.spec (GF := GF) (hG := hG) := by
  intro st c
  wp_start as #Hc
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
