/-
`schema.NewAuthBackend(lg, be)` (`auth.go`): proved from its body (translated with its struct's fields at N4c, 2026-10-17; names-only before). Lean-first (no Rocq counterpart); the
server-construction unit, stage N0 (2026-10-16), for `NewServer`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.NewAuthBackend

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

theorem schema.NewAuthBackend.wp_proof : schema.NewAuthBackend.spec (GF := GF) (hG := hG) := by
  intro lg be
  wp_start
  wp_auto
  wp_alloc l as Hl
  iStructNamed Hl
  ipersist lg
  ipersist be
  wp_auto
  iapply HΦ
  iexists l
  iframe #
  ipureintro; rfl

end proof

end EtcdGrove
end Perennial
