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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- `MustUnsafeSaveConfStateToBackend(lg, tx, confState)` encodes `*confState` as JSON
(`json.Marshal`, which reads the struct and cannot fail on a `ConfState`: so the `lg.Panic`
branch is not taken) and puts it into `Meta` under the key `confState`
(`tx.UnsafePut(Meta, MetaConfStateName, bytes)`, its one call of `tx`): given that put's triple
from `R` to `Q`, for any bytes of at most `25 * n + 128` (a fresh slice, which the function does
not touch again), it goes from `R` to `Q`. The struct `*confState` is nil or read-only for good,
with at most `n` ids (`csOkN n`: its one caller, `BackendHooks.OnPreCommitUnsafe`, passes
`SetConfState`'s clone). **The length bound** (stage S1b of `notes/bbolt-integration-plan.md`,
2026-11-17, the ledger's entry of that date; a statement about `encoding/json`'s output, true): the
JSON of a `ConfState` is `null` for nil, or an object of the four id lists and `auto_leave`
(`raft.pb.go`'s tags `voters`, `learners`, `voters_outgoing`, `learners_next`, `auto_leave`, all
`omitempty`: at most 86 bytes of names and punctuation), each id a decimal `uint64` of at most 20
digits and a comma. -/
abbrev schema.MustUnsafeSaveConfStateToBackend.spec : Prop :=
  ∀ (lg : Loc) (tx : GoInterfaceOk) (cs : Loc) (n : Nat) (R Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      storage.csOkN n cs ∗ R ∗
      □ (∀ (b : GoInterface) (key val : GoSlice) (vb : GoString),
        {{ globalAddr schema.Meta ↦□ b ∗ key ↦*□ schema.confStateKeyBytes ∗ val ↦*□ vb ∗
            ⌜vb.length ≤ 25 * n + 128⌝ ∗ R }}
          (App (App (App (Val #(methods tx.ty go!"UnsafePut" tx.v)) (Val #b)) (Val #key))
            (Val #val))
        {{ RET #(); Q }}) }}
    (App (App (App (Val (@! schema.MustUnsafeSaveConfStateToBackend)) (Val #lg))
      (Val #(GoInterface.ok tx))) (Val #cs))
  {{ RET #(); Q }}

end spec

end EtcdGrove
end Perennial
