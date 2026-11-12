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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The gRPC status code of an error** (opaque): what `status.FromError(err).Code()` returns.
grpc's `FromError` reads the status embedded in the error value (`GRPCStatus()`, or `Unknown` for
an error that has none, `OK` for `nil`), so the code is a function of the error; nothing more is
said of it. (The watch slice's unit W-C: `isHaltErr` compares it.) -/
opaque statusCode [GooseExts] : GoInterface → w32

/-- `status.FromError(err)` of an error grpc's `status` accepts (`statusErrOk`: `nil`, or a leaf
error whose `Error()` and `GRPCStatus()` (if it has one) return; it calls both, and `errors.As`)
returns some `*Status` `s` and a boolean, `true` for `nil`; `s.Code()` returns the error's code
(`statusCode err`) and `s.Message()` some string (grpc's `*Status` methods accept a `nil`
receiver). (2026-10-15, the watch slice's unit W-C) The code was any code, which is weaker than
grpc: the status is embedded in the error value, so the code is a function of the error; it is
now `statusCode err`, an opaque function (a refinement grpc meets).

(2026-10-14, unit P3a) It had no premise, which is false: for an `err` whose `Error()` or
`GRPCStatus()` panics, `FromError` panics; nothing said the result's `Message()` returns either
(`rpctypes.Error` and `ErrorDesc` call it).

(2026-10-21, D29) `s.Message()` returns the error's description (`errDesc err`; it returned some
string), and when the error is not a status error (`ok = false`) its `Error()` returns the
description too: grpc's `FromError` builds `Unknown` with `err.Error()` as the message for an error
without a status. A refinement grpc meets, as `statusCode` was.
(fromerror-stable, 2026-11-06) That refinement was false: `statusErrOk` asked only that `Error()`
return some string on each call, and `FromError` calls it again on each call, so an error whose
`Error()` reads mutable state has no one description (`examples/axiomcx/flipdesc`, branch
`axiom/invoker-filled`: a program that panics in Go, proved not to; `notes/axiom-review/
invoker-filled.md`); likewise for the code, through a `GRPCStatus()` that reads state. The premise
now asks for a stable `Error()` (`errorMsgIs`: one string `m`) and a stable `GRPCStatus()` (one
`*Status`, which grpc never mutates), and the post says the description is that `m`
(`⌜errDesc err = m⌝`, for any `m` `Error()` stably returns), which is true of grpc: the description
is what `Message()` returns, `err.Error()` for an error without a status.
The description and the code are fixed Lean functions of the error value, which for a pointer error
is its location: within an execution this agrees with Go (locations are not reused, and the premise
makes `Error()` and `GRPCStatus()` stable); across executions one location may hold another error,
and the axiom is justified per execution, not as one triple for all of them (`notes/decisions.md`,
"`status.FromError`: an error's description from a stable `Error()`"). -/
abbrev status.FromError.spec : Prop :=
  ∀ (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status ∗ statusErrOk err }}
    (App (Val (@! google_golang_org.grpc.status.FromError)) (Val #err))
  {{ (s : Loc) (ok : Bool), RET (PairV #s #ok);
      ⌜err = GoInterface.nil → ok = true⌝ ∗
      □ (∀ Φ : val → IProp GF, ▷ Φ #(statusCode err) -∗
        WP (App (Val (s @!! go.GoType.PointerType google_golang_org.grpc.status.Status.ty @!! go!"Code"))
          (Val #())) {{ Φ }}) ∗
      □ (∀ Φ : val → IProp GF, ▷ Φ #(errDesc err) -∗
        WP (App (Val (s @!! go.GoType.PointerType google_golang_org.grpc.status.Status.ty @!! go!"Message"))
          (Val #())) {{ Φ }}) ∗
      □ (∀ e : GoInterfaceOk, ⌜ok = false ∧ err = GoInterface.ok e⌝ → ∀ Φ : val → IProp GF,
        ▷ Φ #(errDesc err) -∗
        WP (App (Val #(methods e.ty go!"Error" e.v)) (Val #())) {{ Φ }}) ∗
      □ (∀ (e : GoInterfaceOk) (m : GoString), ⌜ok = false ∧ err = GoInterface.ok e⌝ →
        errorMsgIs e m -∗ ⌜errDesc err = m⌝) }}

end spec

end EtcdGrove
end Perennial
