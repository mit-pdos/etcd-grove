/-
`status.Code` of an error grpc accepts returns its code: proved over grpc's translated `status`
(status-bodies, 2026-11-25; until then a trust-boundary axiom). See
`Spec/google_golang_org/grpc/status/Code.lean`.
-/
module

public import Spec.google_golang_org.grpc.status.Code
public import Spec.google_golang_org.grpc.status.FromError
public import Proof.google_golang_org.grpc.internal.status.Methods

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [status_sem : google_golang_org.grpc.status.Assumptions]

/-- `status.Code(err)` (`status/status.go:139-146`): `OK` for `nil`, else `Convert(err).Code()`,
`FromError`'s status's code. -/
theorem status.Code.wp_triple (err : GoInterface) (c : w32)
    (wp_FromError : ∀ m, status.FromError.triple (GF := GF) err m c) :
    status.Code.triple (GF := GF) err c := by
  wp_start as ⟨#Hok, #Hc⟩
  ihave ⟨%m, #Hd⟩ := statusErrOk_descIs err $$ Hok
  cases err with
  | nil =>
    wp_auto
    ihave %hc := statusCodeIs_nil_eq c $$ Hc
    subst hc
    iapply HΦ
    iclear «$res0»; itrivial
  | ok e =>
    wp_auto
    wp_func_call
    wp_call
    wp_auto
    wp_apply (wp_FromError m) $$ [Hok Hd Hc] as %s %ok ⟨-, #HC, -⟩
    · iframe Hok Hd Hc
    wp_apply HC
    iapply HΦ
    iclear ∗; itrivial

/-- `status.Code` of every error, over `FromError`'s spec. -/
theorem status.Code.wp_proof
    (wp_FromError : status.FromError.spec (GF := GF) (hG := hG)) :
    status.Code.spec (GF := GF) (hG := hG) :=
  fun err c => status.Code.wp_triple err c (fun m => wp_FromError err m c)

/-- `status.Code` of an error that is no `EtcdError` value, over `FromError.specNE`. -/
theorem status.Code.wp_proofNE
    (wp_FromError : status.FromError.specNE (GF := GF) (hG := hG)) :
    status.Code.specNE (GF := GF) (hG := hG) :=
  fun err c hne => status.Code.wp_triple err c (fun m => wp_FromError err m c hne)

end proof

end EtcdGrove
end Perennial
