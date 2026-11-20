/-
`(*authBatchTx).UnsafeSaveAuthRevision(rev)` (`auth.go`): `rev` big-endian into a fresh 8-byte slice
(`binary.BigEndian.PutUint64`), then `tx.UnsafePut(Auth, AuthRevisionKeyName, revBytes)`. auth-schema-srv A5 (2026-11-17; the contracts: `Proof/go_etcd_io/etcd/server/v3/etcdserver/InvAuthBackend.lean`). Lean-first (no Rocq counterpart).
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

/-- An `authBatchTx` whose `tx` is `t`: one call of `t`, `UnsafePut` into the bucket `bk` the variable
`schema.Auth` holds of the key `authRevision` and the value `rev`'s 8 big-endian bytes (`u64Be`, a
fresh slice the method does not touch again; both read-only for good): given that put's triple
from `R` to `Q`, it goes from `R` to `Q`. -/
abbrev schema.authBatchTx.UnsafeSaveAuthRevision.spec : Prop :=
  ∀ (atx : Loc) (t : GoInterfaceOk) (rev : w64) (R Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ schema.abtF go!"tx" atx ↦□ (GoInterface.ok t : GoInterface) ∗ R ∗
      □ (∀ (bk : GoInterface) (key val : GoSlice),
        {{ globalAddr go_etcd_io.etcd.server.v3.storage.schema.Auth ↦□ bk ∗ key ↦*□ schema.authRevisionKey ∗ val ↦*□ u64Be rev ∗ R }}
          (App (App (App (Val #(methods t.ty go!"UnsafePut" t.v)) (Val #bk)) (Val #key)) (Val #val))
        {{ RET #(); Q }}) }}
    (App (Val (atx @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.ty @!! go!"UnsafeSaveAuthRevision")) (Val #rev))
  {{ RET #(); Q }}

end spec

end EtcdGrove
end Perennial
