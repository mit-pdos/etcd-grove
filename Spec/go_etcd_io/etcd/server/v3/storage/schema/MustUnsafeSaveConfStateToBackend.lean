/-
`schema.MustUnsafeSaveConfStateToBackend(lg, tx, confState)` (`server/storage/schema/
confstate.go`, translated names-only). The trust boundary. Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/storage/InvHooks.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.InvHooks

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- `MustUnsafeSaveConfStateToBackend(lg, tx, confState)` encodes `*confState` as JSON
(`json.Marshal`, which reads the struct and cannot fail on a `ConfState`: so the `lg.Panic`
branch is not taken) and puts it into `Meta` under the key `confState`
(`tx.UnsafePut(Meta, MetaConfStateName, bytes)`, its one call of `tx`): given that put's triple
from `R` to `Q`, for any bytes (a fresh slice, which the function does not touch again), it goes
from `R` to `Q`. The struct `*confState` is read without a resource: its one caller
(`BackendHooks.OnPreCommitUnsafe`) passes `SetConfState`'s clone, which no one writes after it is
made (and `ConfState`, a protobuf-go v2 message, is an axiomatized type here). -/
abbrev schema.MustUnsafeSaveConfStateToBackend.spec : Prop :=
  ∀ (lg : Loc) (tx : GoInterfaceOk) (cs : Loc) (R Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      R ∗
      □ (∀ (b : GoInterface) (key val : GoSlice) (vb : GoString),
        {{ globalAddr schema.Meta ↦□ b ∗ key ↦*□ schema.confStateKeyBytes ∗ val ↦*□ vb ∗ R }}
          (App (App (App (Val #(methods tx.ty go!"UnsafePut" tx.v)) (Val #b)) (Val #key))
            (Val #val))
        {{ RET #(); Q }}) }}
    (App (App (App (Val (@! schema.MustUnsafeSaveConfStateToBackend)) (Val #lg))
      (Val #(GoInterface.ok tx))) (Val #cs))
  {{ RET #(); Q }}

end spec

end EtcdGrove
end Perennial
