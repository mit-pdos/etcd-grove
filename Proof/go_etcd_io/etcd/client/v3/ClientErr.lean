/-
`clientErr`: what an error etcd's client returns is, as Go's `errors.AsType` needs it (moved from
`cache/v3/InvEtcdTxnOwn.lean` in unit C1, 2026-10-14, so that `rpctypes.Error`'s spec, which
imports less, can state that it keeps it). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Proof.errors
public import Code.go_etcd_io.etcd.api.v3.v3rpc.rpctypes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.etcd.api.v3

section clientErr
variable [GooseExts] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]

/-- **The dynamic types of the errors etcd's client returns** (k8s 7e-1, 2026-11-10, approved by
etcd-grove-81): a gRPC status error (`*status.Error`, grpc's `internal/status`: `toRPCErr`,
`status.Error`, `status.FromContextError`), an `rpctypes.EtcdError` (`rpctypes.Error`), an
`*errors.errorString` (`io.EOF`, `context.Canceled`) and `context.deadlineExceededError`
(`context.DeadlineExceeded`). Checked, for the errors `kubernetes.Client` returns (after
`ContextError` and `rpctypes.Error` have converted the attempt's error), by `examples/k8s/etcd3`'s
`TestClientErrorTypes` (gates 9c: partitions, deadlines, a closed client); the attempt-level types
`grpcInvokerOk` states rest on the attack programs of `examples/k8s7e1attack` (`InvGrpc.lean`). True of
grpc-go v1.84 under etcd's configuration only: a per-RPC credentials error carrying a status (or
wrapping one with `%w`), and a service-config retry policy's `"max retries exhausted"` error, are of
other types; `perRPCCredsOk` requires credentials that return no error, and `grpcResolverAt` a
service config without a retry policy (`notes/k8s-etcd3-plan.md`, "Soundness finding in the trust
base"). -/
def clientErrTys : List go.GoType :=
  [go.GoType.PointerType google_golang_org.grpc.internal.status.Error.ty,
   v3rpc.rpctypes.EtcdError.ty,
   go.GoType.PointerType _root_.Perennial.errors.errorString.ty,
   _root_.Perennial.context.deadlineExceededError.ty]

/-- **An error etcd's client returns** (a gRPC status error, an `rpctypes.EtcdError`, a context
error): a leaf of an error tree, without `Unwrap` or `As` methods (`errors.isLeafError`), whose
dynamic type is one of `clientErrTys` (since k8s 7e-1), whose
value, if its dynamic type is `rpctypes.EtcdError`, is an `EtcdError` (Go's typing, which the model
lacks: `errors.AsTypeTyped`); and `rpctypes.EtcdError` implements `error` (its method set has
`Error() string`, `func (e EtcdError) Error() string`: `errors.AsTarget`, a method-set fact, which
the model also lacks, since method sets are uninterpreted). What `errors.AsType[rpctypes.EtcdError](err)`
needs is the leaf and typing facts (`ContextError`, `isSafeRetryImmutableRPC`, `leasingKV.acquire`:
`errors.wp_AsType`, Perennial's proved spec). The `AsTarget` conjunct is what `errors.As(err,
&serverErr)` needed until etcd-grove#29 moved those calls to `AsType` (Go's `As` panics for a target
whose element type is neither an interface nor implements `error`); no proof uses it now, and it is
kept (proved: `rpctypesEtcdError_asTarget`) so that the statements written with `clientErr` are
unchanged. -/
def clientErr (err : GoInterface) : Prop :=
  errors.AsTarget v3rpc.rpctypes.EtcdError.ty ∧
  ∀ ii, err = GoInterface.ok ii → errors.isLeafError ii ∧
    errors.AsTypeTyped v3rpc.rpctypes.EtcdError v3rpc.rpctypes.EtcdError.ty ii ∧
    ii.ty ∈ clientErrTys

/-- **An `*errors.errorString` error is a pointer** (k8s 7f-5, 2026-11-16, ledger "the client watch's
element"): what a comparison with another `*errorString` (`err == context.Canceled`) needs, `GoEquals`
comparing pointers. Every `errors.New` value is one; weaker than `errCellOk` (which also fixes the
message): a watch's close error may be an `errors.New` of a server's cancel reason. -/
def errPtrOk (err : GoInterface) : Prop :=
  ∀ ii, err = GoInterface.ok ii →
    ii.ty = go.GoType.PointerType _root_.Perennial.errors.errorString.ty → ∃ x : Loc, ii.v = #x

theorem errPtrOk_nil : errPtrOk GoInterface.nil := by
  intro ii h; cases h

theorem errPtrOk_of_ty (e : GoInterfaceOk)
    (h : e.ty ≠ go.GoType.PointerType _root_.Perennial.errors.errorString.ty) :
    errPtrOk (GoInterface.ok e) := by
  intro ii he ht; injection he with he; subst he; exact absurd ht h

theorem errPtrOk_ptr (x : Loc) :
    errPtrOk (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) := by
  intro ii he _; injection he with he; subst he; exact ⟨x, rfl⟩

/-- **A watch's close error is a client error** (pure; k8s 7f-5): `nil`, or a client error
(`clientErr`) that, if an `*errors.errorString`, is a pointer (`errPtrOk`). -/
def closeErrP (err : GoInterface) : Prop :=
  (err ≠ GoInterface.nil → clientErr err) ∧ errPtrOk err

theorem closeErrP_nil : closeErrP GoInterface.nil :=
  ⟨fun h => absurd rfl h, errPtrOk_nil⟩

end clientErr

section closeErr
open Iris Iris.BI
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : Iris.HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **An error a client watch may close with** (persistent; k8s 7f-5, 2026-11-16, ledger "the client
watch's element"): one grpc's `status` accepts (`statusErrOk`) and a client error, a pointer if an
`*errors.errorString` (`closeErrP`). -/
def closeErrOk (err : GoInterface) : IProp GF :=
  iprop(go_etcd_io.etcd.cache.v3.statusErrOk err ∗ ⌜closeErrP err⌝)

instance closeErrOk_persistent (err : GoInterface) : Persistent (closeErrOk (GF := GF) err) := by
  unfold closeErrOk; infer_instance

open Iris.ProofMode in
theorem closeErrOk_nil : ⊢ closeErrOk (GF := GF) GoInterface.nil := by
  unfold closeErrOk
  isplitl
  · iapply go_etcd_io.etcd.cache.v3.statusErrOk_nil
  · ipureintro; exact closeErrP_nil

open Iris.ProofMode in
theorem closeErrOk_status (err : GoInterface) :
    closeErrOk (GF := GF) err ⊢ go_etcd_io.etcd.cache.v3.statusErrOk err := by
  unfold closeErrOk; iintro ⟨H, -⟩; iexact H

open Iris.ProofMode in
theorem closeErrOk_pure (err : GoInterface) : closeErrOk (GF := GF) err ⊢ ⌜closeErrP err⌝ := by
  unfold closeErrOk; iintro ⟨-, %H⟩; ipureintro; exact H

open Iris.ProofMode in
theorem closeErrOk_intro (err : GoInterface) (h : closeErrP err) :
    go_etcd_io.etcd.cache.v3.statusErrOk (GF := GF) err ⊢ closeErrOk err := by
  unfold closeErrOk; iintro #H; iframe H; ipureintro; exact h

open Iris.ProofMode in
/-- An error no caller's `errors.New` value (`errCellOk`) is a pointer if an `*errorString`. -/
theorem errPtrOk_of_cell (err : GoInterface) :
    go_etcd_io.etcd.cache.v3.errCellOk (GF := GF) err ⊢ ⌜errPtrOk err⌝ := by
  iintro #H
  cases err with
  | nil => ipureintro; exact errPtrOk_nil
  | ok e =>
  by_cases ht : e.ty = go.GoType.PointerType _root_.Perennial.errors.errorString.ty
  · unfold go_etcd_io.etcd.cache.v3.errCellOk
    ihave ⟨%x, %m, %hx, -⟩ := H $$ %e %(And.intro rfl ht)
    ipureintro
    intro ii he _
    injection he with he; subst he; exact ⟨x, hx.1⟩
  · ipureintro; exact errPtrOk_of_ty e ht

end closeErr

end EtcdGrove
end Perennial
