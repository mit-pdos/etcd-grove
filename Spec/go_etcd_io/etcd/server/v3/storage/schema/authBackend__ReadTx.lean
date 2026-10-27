/-
`(*authBackend).ReadTx()` (`auth.go`): an `authReadTx` over the backend's `ReadTx()` with the
backend's logger, as an `auth.AuthReadTx`. The auth plan's S1 (2026-10-23; `notes/auth-plan.md`; the contracts: `Proof/go_etcd_io/etcd/server/v3/etcdserver/InvAuthBackend.lean`). Lean-first (no Rocq counterpart).
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

/-- An `authBackend` over the backend `bi` (`authBE`: its read transactions are over the auth
buckets for `R`) with the logger `lg`: returns a new `*authReadTx` over such a transaction. -/
abbrev schema.authBackend.ReadTx.spec : Prop :=
  ∀ (abe : Loc) (bi : GoInterfaceOk) (lg : Loc) (R : IProp GF) (Held : schema.AuthData → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ schema.abeF go!"be" abe ↦□ (GoInterface.ok bi : GoInterface) ∗ schema.abeF go!"lg" abe ↦□ lg ∗
      schema.authBE bi R Held }}
    (App (Val (abe @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBackend.ty @!! go!"ReadTx")) (Val #()))
  {{ (tx : GoInterface), RET #tx; ∃ (l : Loc) (rt : GoInterfaceOk),
      ⌜tx = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authReadTx.ty) #l⌝ ∗
      schema.atxF go!"tx" l ↦□ (GoInterface.ok rt : GoInterface) ∗ schema.atxF go!"lg" l ↦□ lg ∗
      schema.authRTx rt R Held }}

end spec

end EtcdGrove
end Perennial
