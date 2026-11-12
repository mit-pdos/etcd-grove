/-
`schema.NewMembershipBackend(lg, be)` (`membership.go`): proved from its body (translated in D22
receiver epochs, S8c, 2026-10-24). Lean-first (no Rocq counterpart); for `applySnapshot`'s
`cluster.SetBackend`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.NewMembershipBackend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

theorem schema.NewMembershipBackend.wp_proof : schema.NewMembershipBackend.spec (GF := GF) (hG := hG) := by
  intro lg be
  wp_start
  iapply wp_fupd
  wp_auto
  irename «$r0» => Hl
  generalize «$r0_ptr» = l at *
  iStructNamed Hl
  ipersist lg
  ipersist be
  imodintro
  iapply HΦ
  iframe #

end proof

end EtcdGrove
end Perennial
