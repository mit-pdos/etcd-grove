/-
`(*authBatchTx).UnsafePutUser(user)` (`auth_users.go`): `proto.Marshal(user)` (a panic on its error),
then `tx.UnsafePut(AuthUsers, user.Name, b)`. auth-schema-srv A5 (2026-11-17; the contracts: `Proof/go_etcd_io/etcd/server/v3/etcdserver/InvAuthBackend.lean`). Lean-first (no Rocq counterpart).
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

/-- An `authBatchTx` whose `tx` is `t`: with the message at `p` holding the record `x` (`ownUser`),
every role valid UTF-8 (else `proto.Marshal` fails and the method panics,
`nonissues/etcd-auth-putuser-invalid-utf8-role.md`), it makes one call of `t`, `UnsafePut` into the
bucket `bk` the variable `schema.AuthUsers` holds of the key the record's name (the message's `Name`
slice) and the value the record's encoding (`auth.userEncode x`, a fresh slice the method does not
touch again), both read-only for good (the backend keeps them): given that put's triple from `R` to
`Q`, it goes from `R` to `Q`, the message still holding `x`. -/
abbrev schema.authBatchTx.UnsafePutUser.spec : Prop :=
  ∀ (atx : Loc) (t : GoInterfaceOk) (lg : Loc) (p : Loc) (x : auth.UserRec) (R Q : IProp GF),
  (∀ r ∈ x.roles, utf8Valid r) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ schema.abtF go!"tx" atx ↦□ (GoInterface.ok t : GoInterface) ∗ schema.abtF go!"lg" atx ↦□ lg ∗ auth.ownUser p x ∗ R ∗
      □ (∀ (bk : GoInterface) (key val : GoSlice),
        {{ globalAddr go_etcd_io.etcd.server.v3.storage.schema.AuthUsers ↦□ bk ∗ key ↦*□ x.name ∗ val ↦*□ auth.userEncode x ∗ R }}
          (App (App (App (Val #(methods t.ty go!"UnsafePut" t.v)) (Val #bk)) (Val #key)) (Val #val))
        {{ RET #(); Q }}) }}
    (App (Val (atx @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.ty @!! go!"UnsafePutUser")) (Val #p))
  {{ RET #(); auth.ownUser p x ∗ Q }}

end spec

end EtcdGrove
end Perennial
