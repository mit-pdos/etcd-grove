/-
`status.Code(err)` (grpc, names only; unit P3a): the retry interceptor's `isContextError`, the gRPC
driver's ctx-canceled and close sections.
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

/-- `status.Code(err)` of an error grpc's `status` accepts (`statusErrOk`: it calls
`errors.As` and the error's `GRPCStatus()`) returns the error's code `c` (`statusCodeIs err c`).
(grpc-trusted-T, T2, 2026-11-24; interim, retired by the `status-bodies` stage) It returned some code.
`c` is fixed before the call, in the precondition, as `status.FromError`'s (`FromError.lean`, the
fromerror-wand reading): `statusCodeIs` reads `GRPCStatus()` through a partial-correctness WP, so a
post that related the result to every `c'` with `statusCodeIs err c'` would let a `GRPCStatus()` that
diverges after the call give any code. True of grpc v1.84.0 (`status/status.go:139-146`, as in `models/grpc`): `nil` gives `OK`;
otherwise `Convert(err).Code()`, `FromError`'s status: the error's own stably returned, read-only one
(`statusAt s c m`) when it has `GRPCStatus() *Status`, else `New(Unknown, err.Error())`. A caller with
only `statusErrOk err` gets its `c` from `statusErrOk_code`. -/
abbrev status.Code.spec : Prop :=
  ∀ (err : GoInterface) (c : w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status ∗ statusErrOk err ∗
      statusCodeIs err c }}
    (App (Val (@! google_golang_org.grpc.status.Code)) (Val #err))
  {{ RET #c; True }}

end spec

end EtcdGrove
end Perennial
