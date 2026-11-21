/-
`rpctypes.Error(err)` (`api/v3rpc/rpctypes/error.go`), called by `clientv3.WatchResponse.Err`,
`clientv3.ContextError` and the client's retry interceptor (`shouldRefreshToken`). Translated
(unit P3a, 2026-10-14; it was an axiom): its callees grpc's `status.FromError` and the `*Status`'s
`Message`/`Code` are the trust boundary (`Spec/google_golang_org/grpc/status/FromError.lean`), the
map `errStringToError` a package-init fact (`cache/v3/Base.lean`, `rpctypesInit`). Lean-first (no
Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Proof.go_etcd_io.etcd.client.v3.ClientErr

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
variable [package_sem : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]

/-- `rpctypes.Error(err)` for a non-nil `err` that grpc's `status` accepts (`statusErrOk`:
`ErrorDesc` and `status.FromError` call its `Error()` and `GRPCStatus()`) returns a non-nil error
(`err` itself, or the `EtcdError` its gRPC description maps to) that grpc's `status` accepts too
(an `EtcdError` is a leaf error without `GRPCStatus`, whose `Error` returns its description);
and (2026-10-14, unit C1: `ContextError` passes the result to `errors.As`) a client error gives a
client error (`clientErr`: the result is `err` itself, or an `EtcdError` value, a leaf error).
Nothing about which error, nor about a nil `err` (for which it returns `nil`), except (incomingof
Part B, 2026-11-18) for an error without `GRPCStatus` whose `Error()` stably returns `m` at the call (a
parameter, as `status.FromError.spec`'s): it comes back unchanged (`m` no key of `errStringToError`), or as
an `EtcdError` of description `m`. (errdesc stage 2b, 2026-11-21) `m` is the error's description
(`descIs err m`, a parameter fixed by the caller; until then `errorMsgIs`, with the pure `errDesc`
kept), for every error: the result has description `m` and is `err` or an `EtcdError` of `desc` `m`.

(2026-10-14, unit P3a) It was an axiom with the premise `err ≠ nil` only and the postcondition
`□ (errStrOk err -∗ errStrOk err')`, which is false: `ErrorDesc` calls `err.Error()` (when
`status.FromError` fails) and `FromError` calls `err.Error()` and `err.GRPCStatus()`, either of
which may panic. -/
abbrev rpctypes.Error.spec : Prop :=
  ∀ (err : GoError) (m : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes ∗
      ⌜err ≠ interface.nil⌝ ∗ statusErrOk err ∗ descIs err m }}
    (App (Val (@! go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Error)) (Val #err))
  {{ (err' : GoError), RET #err'; ⌜err' ≠ interface.nil⌝ ∗ statusErrOk err' ∗
      ⌜clientErr err → clientErr err'⌝ ∗
      -- (2026-10-21, D29) the description kept (errdesc stage 2b: the precondition's `m`)
      descIs err' m ∗
      -- (2026-10-23, D37) no caller's `errors.New` value if `err` is none: `err` itself or an
      -- `EtcdError` value
      □ (errCellOk err -∗ errCellOk err') ∗
      -- (k8s 7f-5, 2026-11-16) a pointer if an `*errors.errorString`, if `err` is (`err` itself or
      -- an `EtcdError` value)
      ⌜errPtrOk err → errPtrOk err'⌝ ∗
      -- (incomingof Part B, (2), 2026-11-18; errdesc stage 2b, of every error) `err` itself, or an
      -- `EtcdError` value of description `m`
      ⌜err' = err ∨ ∃ x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError,
        err' = interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x ∧ x.desc' = m⌝ }}

end spec

end EtcdGrove
end Perennial
