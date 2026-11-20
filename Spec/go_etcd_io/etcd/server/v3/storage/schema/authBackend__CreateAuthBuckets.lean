/-
`(*authBackend).CreateAuthBuckets()` (`auth.go`): `tx := abe.be.BatchTx()`, `tx.LockOutsideApply()`, a
deferred `tx.Unlock()`, and `UnsafeCreateBucket` of `Auth`, `AuthUsers`, `AuthRoles`. auth-schema-srv A5 (2026-11-17; the contracts: `Proof/go_etcd_io/etcd/server/v3/etcdserver/InvAuthBackend.lean`). Lean-first (no Rocq counterpart).
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

/-- An `authBackend` over the backend `bi`: `bi.BatchTx()` returns a transaction `t`, and five calls of
`t`: `LockOutsideApply()`, `UnsafeCreateBucket` of the buckets the variables `schema.Auth`,
`schema.AuthUsers`, `schema.AuthRoles` hold, `Unlock()`: given their triples, from `R` through
`L 0`, ..., `L 3` to `Q`, it goes from `R` to `Q`. -/
abbrev schema.authBackend.CreateAuthBuckets.spec : Prop :=
  ∀ (abe : Loc) (bi : GoInterfaceOk) (R : IProp GF) (L : Nat → IProp GF) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ schema.abeF go!"be" abe ↦□ (GoInterface.ok bi : GoInterface) ∗ R ∗
      {{ True }} (App (Val #(methods bi.ty go!"BatchTx" bi.v)) (Val #()))
        {{ (tx : GoInterface), RET #tx; ∃ t : GoInterfaceOk, ⌜tx = GoInterface.ok t⌝ ∗
          ({{ R }} (App (Val #(methods t.ty go!"LockOutsideApply" t.v)) (Val #())) {{ RET #(); L 0 }}) ∗
          (∀ b : GoInterface, {{ L 0 ∗ globalAddr go_etcd_io.etcd.server.v3.storage.schema.Auth ↦□ b }}
            (App (Val #(methods t.ty go!"UnsafeCreateBucket" t.v)) (Val #b)) {{ RET #(); L 1 }}) ∗
          (∀ b : GoInterface, {{ L 1 ∗ globalAddr go_etcd_io.etcd.server.v3.storage.schema.AuthUsers ↦□ b }}
            (App (Val #(methods t.ty go!"UnsafeCreateBucket" t.v)) (Val #b)) {{ RET #(); L 2 }}) ∗
          (∀ b : GoInterface, {{ L 2 ∗ globalAddr go_etcd_io.etcd.server.v3.storage.schema.AuthRoles ↦□ b }}
            (App (Val #(methods t.ty go!"UnsafeCreateBucket" t.v)) (Val #b)) {{ RET #(); L 3 }}) ∗
          ({{ L 3 }} (App (Val #(methods t.ty go!"Unlock" t.v)) (Val #())) {{ RET #(); Q }}) }} }}
    (App (Val (abe @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBackend.ty @!! go!"CreateAuthBuckets")) (Val #()))
  {{ RET #(); Q }}

end spec

end EtcdGrove
end Perennial
