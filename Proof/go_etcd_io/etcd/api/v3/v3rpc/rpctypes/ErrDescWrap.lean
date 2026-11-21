/-
**A `*fmt.wrapError`'s description** (fmtmodel, 2026-11-20): the trust boundary that
`fmt.ErrorfWrap`'s description conjunct rests on, now that Perennial's `fmt.Errorf` returns Go's
`*fmt.wrapError` for one `%w`. Lean-first (no Rocq counterpart).
-/
module

public import Proof.google_golang_org.grpc.status.ErrDesc
public import Perennial.Proof.fmt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section axioms
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A `*fmt.wrapError`'s description is its message** (an axiom; D29): `errDesc` is what
`rpctypes.ErrorDesc(err)` returns (`api/v3/v3rpc/rpctypes/error.go:274-279`: `s.Message()` if
`status.FromError(err)` is ok, else `err.Error()`). grpc's `FromError` (grpc v1.84.0,
`status/status.go:96-127`) gives a status whose message is `err.Error()` on every path for an
error without a `GRPCStatus` method (`*fmt.wrapError` has only `Error` and `Unwrap`,
`fmt/errors.go:75-81`): `New(codes.Unknown, err.Error())`, or, when `errors.As` finds a wrapped
`GRPCStatus`, that status with `p.Message = err.Error()`. And `(*wrapError).Error()` is
`return e.msg`. So the description is the `msg` field, which the cell holds for good. A fact of the
description's definition, which `errDesc`, opaque, cannot state by itself (as
`rpctypes.errDesc_etcdError`). -/
axiom rpctypes.errDesc_wrapError (l : Loc) (m : GoString) :
  (l.[_root_.Perennial.fmt.wrapError, go!"msg"] ↦□ m : IProp GF) ⊢
    ⌜errDesc (GoInterface.ok ⟨go.GoType.PointerType _root_.Perennial.fmt.wrapError.ty, #l⟩) = m⌝

end axioms

end EtcdGrove
end Perennial
