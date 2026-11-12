/-
`rpctypes.Error(err)` (`api/v3rpc/rpctypes/error.go:256`).

Users: the client's `ContextError` (every client call's error), the retry interceptor's
`shouldRefreshToken` and `isSafeRetry*` (1c), `WatchResponse.Err` (1b), the package's own client-side
variables (`init.spec`). Snippets: `examples/specreq/clientv3kv/errors.go` (W0).

Proof sketch: `nil` returns `nil`. Else `ErrorDesc(err)` (its spec: the description `msg` of the
view), the map lookup in `errStringToError` (the package's initialized map: its keys are the mapped
descriptions, its values the `ErrGRPC*` status errors, `init.spec`'s variables; a law of the map's
initialization, from `ErrorDesc` of each status); a miss returns `err`; a hit `ErrGRPC_e` goes
through `status.FromError` (a status: `ok`), `Message()` (`desc e`), `Code()` (`code e`), and the
result is `EtcdError{code e, desc e}` = `errVal e` (`errVal_fields`).

Over W0's `callErr` (`callErr_view`): `.etcd e` gives `errVal e`; `.other` and `.notSent` give
`err` itself.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/api/v3/v3rpc/rpctypes/Error.lean`: the result exactly
(it was "some client error with the same description"), over `errView` (was `statusErrOk`).

Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Rpctypes

open Iris Iris.BI EtcdModel ClientV3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]

/-- `rpctypes.Error(err)` of an error seen as (`c`, `msg`, `ok`): `nil` for `nil`; `errVal e` when
`msg` is the mapped description of `e`; else `err` itself. -/
def Error.spec : Prop :=
  ∀ (err : GoInterface) (c : w32) (msg : GoString) (ok : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes ∗ Grpc.errView err c msg ok }}
    (App (Val (@! go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Error)) (Val #err))
  {{ (err' : GoInterface), RET #err';
      ⌜(err = GoInterface.nil ∧ err' = GoInterface.nil) ∨
       (err ≠ GoInterface.nil ∧ ∃ e, mapped e = true ∧ msg = desc e ∧ err' = errVal e) ∨
       (err ≠ GoInterface.nil ∧ (∀ e, mapped e = true → msg ≠ desc e) ∧ err' = err)⌝ }}

end spec

end Rpctypes
end EtcdGrove
end Perennial
