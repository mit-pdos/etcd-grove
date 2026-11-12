/-
`newTokenProviderNop`'s proof (the auth plan's E2g, 2026-10-25): an allocation.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.newTokenProviderNop

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.newTokenProviderNop.wp_proof : auth.newTokenProviderNop.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_alloc p as Hp
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
