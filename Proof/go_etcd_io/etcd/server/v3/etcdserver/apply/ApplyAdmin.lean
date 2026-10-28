/-
**`a.Apply(r, shouldApplyV3)` on an admitted admin request in the mode `on`** (the auth plan's
E2o, 2026-10-26; `notes/decisions.md`, "E2o of the auth plan"). Lean-first (no Rocq counterpart).

A second triple of `apply.uberApplier.Apply` (`uber_applier.go`), beside its spec
(`Spec/.../apply/uberApplier__Apply.lean`), for the requests the mode `on` admits by their shape
(`adminKindOk`): the current applier's `Apply` (the chain's `applierTriples` clause, which takes
any `applyFunc` with a triple of its own) runs `dispatch` through its admin triple
(`dispatch.adminSpec`, `DispatchAdmin.lean`), whose admin triples of the current applier come from
the base applier's and the current applier's shape (`applierAdmin_curG`). The auth layer's admin
check either passes (the request's admin outcome, `adminDone`) or rejects the request (the
authority, its receipt and `W` back). The current chain is unchanged (`dispatch` keeps it).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.uberApplier__Apply
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.DispatchAdmin

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The admin outcome of `Apply`'s result** `ar` for the outcome `out` (the auth plan's E2o):
a dispatched request's `adminDone` (its step or the model's refusal); a rejected or skipped one
ran nothing, and the authority with its fuel and the unspent receipt come back. -/
def apply.adminOut (Own : auth.AuthNames → List auth.AuthState → IProp GF) (γa : auth.AuthNames) (M : auth.AuthMode)
    (hs : List auth.AuthState) (rq : apply.IRRModel) (v3 : Bool) (ar : Loc) :
    apply.ApplyOut → IProp GF
  | .dispatched _ _ => apply.adminDone Own γa M hs rq v3 ar
  | _ => iprop(Own γa hs ∗ ⧗ 1)

variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **`a.Apply(r, shouldApplyV3)` on an admitted admin request in the mode `on γa`** (see the
file header): `Apply.spec`'s precondition but for the KV floor, the store's write token, the rest
buckets and the certificates (which an admin request does not use), with `adminKindOk rq` in place
of `rqOk`, the auth store's admin step facts (`isAuthSteps`, for the base applier's admin triples),
the authority with its fuel, a time receipt (the admin step's cost) and the store's write
resource `W`; its postcondition is `Apply.spec`'s but for the rest buckets (which an admin request
leaves, `restAfter_other`), with `W` back and the admin outcome (`adminOut`). -/
abbrev apply.uberApplier.Apply.adminSpec : Prop :=
  ∀ (E : apply.AEnv GF) (p : Loc) (opts : go_etcd_io.etcd.server.v3.etcdserver.apply.ApplierOptions)
    (x : apply.ApplyKV) (r : Loc) (rq : apply.IRRModel) (skip v3 : Bool)
    (Pre Q Post : IProp GF) (W : IProp GF) (γa : auth.AuthNames) (hs : List auth.AuthState)
    (Own : auth.AuthNames → List auth.AuthState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.uberIs E p opts ∗
      apply.irrWrapperIs r rq skip ∗ apply.uberOwn E p x.chain ∗ apply.kvOwn E x.log ∗
      apply.cPre v3 E.P E.f Pre Q Post ∗
      (∃ base : GoInterface, structFieldRef uberApplier go!"applyV3base" p ↦□ base ∗
        apply.applierAdmin E (apply.baseChain E.authOn) base W Own) ∗
      ⌜E.authMode = .on γa ∧ apply.adminKindOk rq ∧ apply.dispatchOk E.authOn rq ∧
        receiptBound GF ≤ 2 ^ 48⌝ ∗ ⌜skip = true → rq.txn.isSome = true⌝ ∗
      Own γa hs ∗ ⧗ 1 ∗ W ∗ (if v3 then apply.adminExtra E γa rq Pre else iprop(True)) }}
    (App (App (Val (p @!! go.GoType.PointerType uberApplier.ty @!! go!"Apply")) (Val #r)) (Val #v3))
  {{ (ar : Loc), RET #ar; ∃ (x' : apply.ApplyKV) (out : apply.ApplyOut),
      apply.uberOwn E p x'.chain ∗ apply.kvOwn E x'.log ∗ apply.cPost v3 Pre Post ∗
      ⌜apply.applyStep rq v3 x x' out ∧ (out = .rejected ∨ ∃ o, out = .dispatched o skip)⌝ ∗
      apply.resTrace ar ∗ apply.applyResultIs rq v3 x.log ar out ∗
      apply.applyAuthRes E.authMode x.chain rq v3 out ∗ W ∗
      apply.adminOut Own γa E.authMode hs rq v3 ar out }}

end defs

/-- An admitted admin request is not a KV request. -/
theorem apply.adminKindOk_nonKV (rq : apply.IRRModel) (h : apply.adminKindOk rq) :
    apply.isKVKind (apply.dispatchKind rq) = false := by
  unfold apply.adminKindOk at h
  split at h <;> simp_all [apply.isKVKind]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

theorem apply.uberApplier.Apply.wp_admin
    (hD : apply.uberApplier.dispatch.adminSpec (GF := GF) (hG := hG)) :
    apply.uberApplier.Apply.adminSpec (GF := GF) (hG := hG) := by
  -- (C1's A2) phase 1 of the spec-first stage: the proof (at 2040bccc8a) is redone in phase 2
  sorry

end proof

end EtcdGrove
end Perennial
