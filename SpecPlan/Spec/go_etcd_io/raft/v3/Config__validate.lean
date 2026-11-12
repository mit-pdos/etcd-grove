/-
## `Config.validate()`

**Users.** `newRaft` (`raft.go:440`: panics on an error). R1's `ConfigOk` is the success condition
plus the scope restrictions.

**Proof sketch.** The checks in order; the defaults (`MaxUncommittedEntriesSize`,
`MaxCommittedSizePerReady`, `MaxInflightBytes`) and a `nil` logger replaced by `getLogger()`
(`getLogger.spec`); the errors are fresh `errors.New` values (non-nil).

**Changes** (from `specs-ref`'s `Config__validate.lean`): the post states the defaults and the
logger's contract (was the success case only, under `ConfigOk`). **Margin.** On an error, the fields
are partly defaulted; the error's text is not stated.
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.ApiCore

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Raft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- What `validate` accepts (`ReadOnlyLeaseBased` is `1`). -/
def Config.valid (cv : go_etcd_io.raft.v3.Config) : Prop :=
  cv.ID' ≠ W64 0 ∧ isLocalTarget cv.ID' = false ∧
  0 < sint.Z cv.HeartbeatTick' ∧ sint.Z cv.HeartbeatTick' < sint.Z cv.ElectionTick' ∧
  cv.Storage' ≠ interface.nil ∧ 0 < sint.Z cv.MaxInflightMsgs' ∧
  (cv.MaxInflightBytes' = W64 0 ∨ uint.nat cv.MaxSizePerMsg' ≤ uint.nat cv.MaxInflightBytes') ∧
  (cv.ReadOnlyOption' = W64 1 → cv.CheckQuorum' = true)

/-- **Validates `c`**: `nil` exactly when the configuration is valid, then defaulted. -/
def Config.validate.spec : Prop :=
  ∀ (c : Loc) (cv : go_etcd_io.raft.v3.Config),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗ (⌜cv.Logger' = interface.nil⌝ ∨ loggerOk cv.Logger') }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.raft.v3.Config.ty @!! go!"validate")) (Val #()))
  {{ (err : GoInterface), RET #err; ∃ cv' : go_etcd_io.raft.v3.Config, c ↦ cv' ∗
      ((⌜err = interface.nil ∧ Config.valid cv ∧ cv' = Config.defaulted cv cv'.Logger' ∧
          (cv.Logger' ≠ interface.nil → cv'.Logger' = cv.Logger')⌝ ∗ loggerOk cv'.Logger') ∨
       ⌜err ≠ interface.nil ∧ ¬ Config.valid cv⌝) }}

end spec
end Raft
end EtcdGrove
end Perennial
