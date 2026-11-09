/-
`metadata.FromOutgoingContext(ctx)` (grpc-go, assumed: `metadata/metadata.go`).

Users: the client's `WithRequireLeader`, `withVersion`, `streamKeyFromCtx` (W0, 1b, 1c).

Why true: it reads `ctx.Value(mdOutgoingKey{})` (the context's metadata, `outMD`) and returns a
fresh copy merged with the appended pairs, lowercased; `false` (and a `nil` map, which reads as
empty) when there is none.

Changes: from `specs-ref/Spec/google_golang_org/grpc/metadata/FromOutgoingContext.lean`.
verify-round (A6 F3): the map is `nil` when `ok` is `false` (`metadata.go:331-335`), non-`nil`
otherwise (a fresh `make`); `MD.Set` now takes a non-`nil` map, so a caller that writes without
copying first must test `ok` (a write to the `nil` map panics). `mdAt` of the `nil` map is still
given: it reads as empty (`Get`, `Copy`, a lookup on a `nil` map do not panic).
Re-review (R-A6 N1): that `mdAt` of the `nil` map was contradictory (`mdAt_ownMap` makes it an
`ownMap`, a heap points-to, never `nil`), so every caller's `ok = false` branch was vacuous; the
`nil` case is now outside `mdAt` (`mdAtN true`: `m = null ∧ md = []`), and `MD.Copy`/`MD.Get` take
either case.
Recheck (RR1): a gated row, `ctxNoMeta ctx -∗ ⌜ok = false⌝`: a context whose
`Value(mdOutgoingKey{})` is `nil` has no metadata attached, and grpc returns `nil, false` exactly
then (`metadata.go:325-328`); `outMD ctx []` alone cannot tell it from an attached empty `MD`, for
which `ok` is `true`.

Margin: `ok` is `false` exactly when no metadata was attached; the spec says only `md = []` then.
-/
module

public import Spec.google_golang_org.grpc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Grpc

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.grpc.metadata.Assumptions]

/-- `metadata.FromOutgoingContext(ctx)`: a fresh copy of the context's outgoing metadata. -/
def FromOutgoingContext.spec : Prop :=
  ∀ (ctx : GoInterface) (md : MD),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.metadata ∗ Context.ctxOk ctx ∗ outMD ctx md }}
    (App (Val (@! google_golang_org.grpc.metadata.FromOutgoingContext)) (Val #ctx))
  {{ (m : Loc) (ok : Bool), RET (PairV #m #ok); mdAtN (!ok) m (DFrac.own 1) md ∗
      ⌜ok = true → m ≠ null⌝ ∗ (Context.ctxNoMeta ctx -∗ ⌜ok = false⌝) }}

end spec

end Grpc
end EtcdGrove
end Perennial
