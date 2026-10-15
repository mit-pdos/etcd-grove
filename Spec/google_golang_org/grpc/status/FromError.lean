/-
`status.FromError(err)` (grpc, not translated: names only), and the `Code()` and `Message()` of
its result. The trust boundary (an axiom, `Proof/google_golang_org/grpc/status/FromError.lean`),
for `client/v3/leasing`'s `acquire`, the client's `ContextError`, `rpctypes.Error`/`ErrorDesc`. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3


section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `status.FromError(err)` of an error grpc's `status` accepts (`statusErrOk`: `nil`, or a leaf
error whose `Error()` and `GRPCStatus()` (if it has one) return; it calls both, and `errors.As`)
returns some `*Status` `s` and a boolean, `true` for `nil`; `s.Code()` and `s.Message()` return
(some code, some string: grpc's `*Status` methods accept a `nil` receiver).

(2026-10-14, unit P3a) It had no premise, which is false: for an `err` whose `Error()` or
`GRPCStatus()` panics, `FromError` panics; nothing said the result's `Message()` returns either
(`rpctypes.Error` and `ErrorDesc` call it). -/
abbrev status.FromError.spec : Prop :=
  ∀ (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status ∗ statusErrOk err }}
    (App (Val (@! google_golang_org.grpc.status.FromError)) (Val #err))
  {{ (s : Loc) (ok : Bool), RET (PairV #s #ok);
      ⌜err = GoInterface.nil → ok = true⌝ ∗
      □ (∀ Φ : val → IProp GF, ▷ (∀ c : w32, Φ #c) -∗
        WP (App (Val (s @!! go.GoType.PointerType google_golang_org.grpc.status.Status.ty @!! go!"Code"))
          (Val #())) {{ Φ }}) ∗
      □ (∀ Φ : val → IProp GF, ▷ (∀ msg : GoString, Φ #msg) -∗
        WP (App (Val (s @!! go.GoType.PointerType google_golang_org.grpc.status.Status.ty @!! go!"Message"))
          (Val #())) {{ Φ }}) }}

end spec

end EtcdGrove
end Perennial
