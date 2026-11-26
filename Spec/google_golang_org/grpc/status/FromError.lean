/-
`status.FromError(err)` (grpc, not translated: names only), and the `Code()` and `Message()` of
its result. The trust boundary (an axiom, `Proof/google_golang_org/grpc/status/FromError.lean`),
for `client/v3/leasing`'s `acquire`, the client's `ContextError`, `rpctypes.Error`/`ErrorDesc`. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Proof.google_golang_org.grpc.status.StatusRO

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
"`status.FromError`: an error's description from a stable `Error()`").
(fromerror-wand, 2026-11-18, the user's fix via etcd-grove-03) That post's `m` was chosen by a persistent
wand `errorMsgIs e m -∗ ⌜errDesc err = m⌝`, usable after the call: false, since `errorMsgIs` is a
partial-correctness WP and an `Error()` that diverges after the call satisfies it for every `m`
(`notes/fromerror-wand.md`, `examples/axiomcx/fromerrorflip`). Now `m` is a parameter fixed before the call,
`errorMsgIs e m` is in the precondition, and the post says `⌜ok = false → errDesc err = m⌝`: Go's
`FromError` calls `err.Error()` during this call, and by the soundness (adequacy) of the precondition's WP
at the call that call returns `m` if it returns at all (if not, `FromError` does not return and the post
is vacuous); `errorMsgIs` is never read as total correctness. (incomingof T8) A leaf error without grpc's
`GRPCStatus() *Status` gives `ok = false` (grpc v1.84.0 `status.go:96-127`: both `true` returns are guarded
by that method, and `errors.As` on a leaf checks only the error itself;
`examples/axiomcx/incomingof-real` `TestFromErrorNoGRPCStatus`). The `Message()` conjunct rests on `s`
being unwritable: a fresh `*Status` no ownership of which is given out when `ok = false`, the error's own
read-only status (`status.statusAt`) when `ok = true`. (errdesc stage 2a, 2026-11-20) `Code()` returns the
code `c` the precondition relates to the error (`statusCodeIs err c`; `statusErrOk_code` gives some), not
the pure `statusCode err`: a fixed function of the value, which no implementation can meet for the errors
it allocates (`notes/errdesc-ghost-plan.md`). (errdesc stage 2b, 2026-11-21) Likewise the message:
`Message()` returns the description `m` the precondition relates to the error (`descIs err m`;
`statusErrOk_descIs` gives some), not the pure `errDesc err`; for an error without a status, the
`Error()` the precondition's `descIs` makes stable (its `errorMsgIs`, or an `EtcdError`'s `desc`),
which `FromError` calls during the call (the fromerror-wand reading above), so the former conjunct
`ok = false → errDesc err = m` is the precondition itself.
(grpc-trusted-T, T3, 2026-11-24; interim, retired by the `status-bodies` stage) An error whose dynamic
type has `GRPCStatus() *Status` (`hasGRPCStatus`) gives `ok = true`: `FromError`'s type assertion
`err.(grpcstatus)` succeeds on it, and its `GRPCStatus()` returns the non-nil read-only status
`statusErrOk` gives (`statusAt`, `s ≠ null`), which `FromError` returns with `true` (grpc v1.84.0
`status/status.go:96-127`, `models/grpc/status/status.go` `FromError`'s first branch). With the
conjunct before it, `ok` is now known of every error the precondition admits. -/
abbrev status.FromError.triple (err : GoInterface) (m : GoString) (c : w32) : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status ∗ statusErrOk err ∗
      descIs err m ∗ statusCodeIs err c }}
    (App (Val (@! google_golang_org.grpc.status.FromError)) (Val #err))
  {{ (s : Loc) (ok : Bool), RET (PairV #s #ok);
      ⌜err = GoInterface.nil → ok = true⌝ ∗
      □ (∀ Φ : val → IProp GF, ▷ Φ #c -∗
        WP (App (Val (s @!! go.GoType.PointerType google_golang_org.grpc.status.Status.ty @!! go!"Code"))
          (Val #())) {{ Φ }}) ∗
      □ (∀ Φ : val → IProp GF, ▷ Φ #m -∗
        WP (App (Val (s @!! go.GoType.PointerType google_golang_org.grpc.status.Status.ty @!! go!"Message"))
          (Val #())) {{ Φ }}) ∗
      □ (∀ e : GoInterfaceOk, ⌜ok = false ∧ err = GoInterface.ok e⌝ → ∀ Φ : val → IProp GF,
        ▷ Φ #m -∗
        WP (App (Val #(methods e.ty go!"Error" e.v)) (Val #())) {{ Φ }}) ∗
      -- (incomingof T8, 2026-11-18) a leaf error without grpc's `GRPCStatus() *Status` is no status
      -- error
      ⌜∀ e : GoInterfaceOk, err = GoInterface.ok e →
        methodSet e.ty !! go!"GRPCStatus" ≠
          some (go.Signature [] false
            [go.GoType.PointerType google_golang_org.grpc.internal.status.Status.ty]) →
        ok = false⌝ ∗
      -- (grpc-trusted-T, T3, 2026-11-24) and one with it is a status error
      ⌜hasGRPCStatus err → ok = true⌝ }}

/-- The spec: `triple` of every error. -/
abbrev status.FromError.spec : Prop :=
  ∀ (err : GoInterface) (m : GoString) (c : w32), status.FromError.triple (GF := GF) err m c

/-- (status-bodies, 2026-11-25) The spec of an error that is no `rpctypes.EtcdError` value: what a
program without etcd's `rpctypes` uses (gRPC's robustness driver), whose proof needs no fact of
`EtcdError`'s `Error()` (a method of a package it does not translate). -/
abbrev status.FromError.specNE : Prop :=
  ∀ (err : GoInterface) (m : GoString) (c : w32),
    (∀ x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError,
      err ≠ interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x) →
    status.FromError.triple (GF := GF) err m c

end spec

end EtcdGrove
end Perennial
