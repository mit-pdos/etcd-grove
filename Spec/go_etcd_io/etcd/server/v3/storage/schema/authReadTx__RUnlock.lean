/-
`(*authReadTx).RUnlock()` (`auth.go`): the transaction's `tx.RUnlock()`. The auth plan's S1 (2026-10-23; `notes/auth-plan.md`; the contracts: `Proof/go_etcd_io/etcd/server/v3/etcdserver/InvAuthBackend.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvAuthBackend

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- An `authReadTx` whose `tx` is the transaction `rt` over the auth buckets for `R`: the token
of a snapshot becomes `R` again. -/
abbrev schema.authReadTx.RUnlock.spec : Prop :=
  ∀ (atx : Loc) (rt : GoInterfaceOk) (R : IProp GF) (Held : schema.AuthData → IProp GF)
    (D : schema.AuthData),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ schema.atxF go!"tx" atx ↦□ (GoInterface.ok rt : GoInterface) ∗ schema.authRTx rt R Held ∗ Held D }}
    (App (Val (atx @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authReadTx.ty @!! go!"RUnlock")) (Val #()))
  {{ RET #(); R }}

end spec

end EtcdGrove
end Perennial
