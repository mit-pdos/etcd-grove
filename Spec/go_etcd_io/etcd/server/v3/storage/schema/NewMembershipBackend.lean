/-
`schema.NewMembershipBackend(lg, be)` (`membership.go`). Lean-first (no Rocq counterpart); D22
receiver epochs, S8c (2026-10-24), for `applySnapshot`'s `cluster.SetBackend`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvServer

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `NewMembershipBackend(lg, be)` returns a fresh `*membershipBackend`
wrapping `be` (its fields `lg`, `be`, persistent: no method writes them). -/
abbrev schema.NewMembershipBackend.spec : Prop :=
  ∀ (lg : Loc) (be : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.schema.NewMembershipBackend)) (Val #lg))
      (Val #be))
  {{ (l : Loc), RET #l;
      structFieldRef go_etcd_io.etcd.server.v3.storage.schema.membershipBackend go!"lg" l ↦□ lg ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.schema.membershipBackend go!"be" l ↦□ be }}

end spec

end EtcdGrove
end Perennial
