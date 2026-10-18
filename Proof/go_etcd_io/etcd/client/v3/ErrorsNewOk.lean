/-
**`errors.New`'s errors are client errors grpc's `status` accepts** (2026-10-18; until then the
watcher's premise `errorsNewOk`). Lean-first (no Rocq counterpart).

`errorsNewOk_of`: from Perennial's `errors.New` (a fresh `*errorString` whose `Error()` returns the
message, `mvcc.wp_New_errorString`) and the method-set facts of `*errorString`, which the
semantics leaves uninterpreted (premises, as Perennial's `context.ErrorStringIsError`): it is a
leaf without `Is` (`ErrorStringLeaf`) and has no `GRPCStatus` method
(`ErrorStringNoGRPCStatus`: Go's `errors` package defines only `Error`); and `rpctypes.EtcdError`
implements `error` (`hAs`, the client's KV premise).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvWatch
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Errorf
public import Proof.errors.NewVar

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

/-- The method set of `*errors.errorString` has no `GRPCStatus` method (Go's `errors` package
gives it only `Error`; grpc's `status.FromError` would call it). -/
class ErrorStringNoGRPCStatus [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions] : Prop where
  noGRPCStatus : methodSet (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) !!
      go!"GRPCStatus" ≠
    some (go.Signature [] false
      [go.GoType.PointerType google_golang_org.grpc.internal.status.Status.ty])

namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3

section proofs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [errors_sem : _root_.Perennial.errors.Assumptions] [fmt_sem : _root_.Perennial.fmt.Assumptions]
variable [rp_sem : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]

/-- **`errorsNewOk` holds** (see the file header). -/
theorem errorsNewOk_of [ErrorStringLeaf] [ErrorStringNoGRPCStatus]
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) :
    ⊢ errorsNewOk (GF := GF) := by
  unfold errorsNewOk
  iintro !> %msg %Φ HΦ
  iapply (mvcc.wp_New_errorString (GF := GF) msg) $$ [] [HΦ]
  · itrivial
  inext
  iintro %x #Herr
  iapply HΦ
  · ipureintro
    refine ⟨by simp, hAs, fun ii h => ?_⟩
    cases h
    refine ⟨ErrorStringLeaf.leaf _, ?_⟩
    unfold errors.AsTypeTyped
    have hu : underlying go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty =
        go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.underlying := go.is_underlying
    rw [hu]
    simp only [go.isInterfaceType]
    intro h
    simp [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty] at h
  unfold statusErrOk
  iintro !> %e %he
  cases he
  isplitr
  · unfold errorStringSpec
    iintro !> %Ψ HΨ
    iapply Herr
    inext
    iapply HΨ
  isplitr
  · ipureintro; exact ErrorStringLeaf.leaf _
  unfold grpcErrMethodsOk
  isplitl
  · iintro %h
    exact absurd h ErrorStringNoGRPCStatus.noGRPCStatus
  · iintro %h
    exact absurd h ErrorStringLeaf.noIs

end proofs

end client
end EtcdGrove
end Perennial
