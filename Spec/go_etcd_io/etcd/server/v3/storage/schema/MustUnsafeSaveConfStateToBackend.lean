/-
## `schema.MustUnsafeSaveConfStateToBackend(lg, tx, confState)`: assumed (names only)

**Users.** `BackendHooks.OnPreCommitUnsafe` (`storage/hooks.go:50`, 2e: the pending configuration,
the batch lock held). Snippet: `examples/specreq/schema/schema.go` (`ReqSaveThenRead`).

**Assumed** (`confstate.go:26-38`): `json.Marshal(confState)` (a `raftpb.ConfState`: slices of
`uint64` and a `bool`, never an error, so `lg.Panic` is unreachable), `tx.UnsafePut(Meta, confState,
bytes)` (`txWr`).

**Changes.** From `specs-ref`'s `MustUnsafeSaveConfStateToBackend.lean`: over the contract.

**Margin.** The stored bytes are not described (their reader, `UnsafeConfStateFromBackend`, is
not translated).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.Api
public import GeneratedProof.go_etcd_io.raft.v3.raftpb

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Schema

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- **Stores the configuration** under `Meta`'s `confState`. -/
def MustUnsafeSaveConfStateToBackend.spec : Prop :=
  ∀ (lg : Loc) (tx : GoInterface) (S : Scope) (R : View → IProp GF) (V : View) (m : BData)
    (cs : Loc) (dq : DFrac) (c : Proto.Content),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ txWr tx S R ∗ R V ∗ ⌜S.has .metaB confStateKey ∧ V .metaB = some m⌝ ∗
      Proto.msgAt go_etcd_io.raft.v3.raftpb.ConfState.ty cs dq c }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.schema.MustUnsafeSaveConfStateToBackend)) (Val #lg)) (Val #tx)) (Val #cs))
  {{ RET #(); Proto.msgAt go_etcd_io.raft.v3.raftpb.ConfState.ty cs dq c ∗
      ∃ bs : GoString, R (V.put .metaB confStateKey bs) }}

end spec
end Schema
end EtcdGrove
end Perennial
