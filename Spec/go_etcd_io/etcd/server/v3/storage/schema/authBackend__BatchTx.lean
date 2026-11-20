/-
`(*authBackend).BatchTx()` (`auth.go`): `&authBatchTx{tx: abe.be.BatchTx(), lg: abe.lg}`. auth-schema-srv A5 (2026-11-17; the contracts: `Proof/go_etcd_io/etcd/server/v3/etcdserver/InvAuthBackend.lean`). Lean-first (no Rocq counterpart).
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

/-- An `authBackend` over the backend `bi` with the logger `lg`: given `bi.BatchTx()`'s triple, returning
a transaction `t` with `C t`, returns a new `*authBatchTx` over such a transaction (its fields
read-only). -/
abbrev schema.authBackend.BatchTx.spec : Prop :=
  ∀ (abe : Loc) (bi : GoInterfaceOk) (lg : Loc) (C : GoInterfaceOk → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ schema.abeF go!"be" abe ↦□ (GoInterface.ok bi : GoInterface) ∗ schema.abeF go!"lg" abe ↦□ lg ∗
      {{ True }} (App (Val #(methods bi.ty go!"BatchTx" bi.v)) (Val #()))
        {{ (tx : GoInterface), RET #tx; ∃ t : GoInterfaceOk, ⌜tx = GoInterface.ok t⌝ ∗ C t }} }}
    (App (Val (abe @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBackend.ty @!! go!"BatchTx")) (Val #()))
  {{ (tx : GoInterface), RET #tx; ∃ (l : Loc) (t : GoInterfaceOk),
      ⌜tx = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.ty) #l⌝ ∗
      schema.abtF go!"tx" l ↦□ (GoInterface.ok t : GoInterface) ∗ schema.abtF go!"lg" l ↦□ lg ∗ C t }}

end spec

end EtcdGrove
end Perennial
