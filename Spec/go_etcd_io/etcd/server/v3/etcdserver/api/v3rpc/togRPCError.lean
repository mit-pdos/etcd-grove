/-
`v3rpc.togRPCError` (`server/etcdserver/api/v3rpc/`).

Users: every handler of this package (after a server call), 2b's watch handler.

Proof sketch: `errors.Is` against the context's errors (Go's `errors`, Perennial's); the lookup in `toGRPCErrorMap` (the package's initialized map: its keys the server errors `srvErrOf` names, each to `e`'s `ErrGRPC*`, or for `.tooManyRequests`/`.memberNotEnoughStarted` to `errVal e`, `nonissues/etcd-v3rpc-togrpcerror-etcderror-unknown-code.md`; a law of the package's initialization); a miss: `status.Error(codes.Unknown, err.Error())` (`errMsg`).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/togRPCError.lean`: over 2c's `srvErrOf` and grpc's `sentStatus` (it was the client-facing `srvErrOk`).

Margin: the code is `e`'s gRPC code except for the two errors mapped to `EtcdError`s (sent `Unknown`); the spec says some code. A wrapped context error (`errors.Is` true for a non-context value) is not specified: no caller returns one.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3rpc

open Iris Iris.BI EtcdModel EtcdWire ClientV3 Grpc Proto EtcdServer

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `togRPCError(err)`: a context's error unchanged; a server error of `e` to what is sent with
`e`'s description; any other error to an `Unknown` status with its message. -/
def togRPCError.spec : Prop :=
  ∀ (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ (context.isCtxErr err ∨
       ((context.isCtxErr err -∗ False) ∗ ((∃ e, ⌜srvErrOf err e⌝) ∨
         (∃ m, errMsg err m ∗ ⌜∀ e, ¬ srvErrOf err e⌝)))) }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.togRPCError)) (Val #err))
  {{ (err' : GoInterface), RET #err';
      (context.isCtxErr err ∗ ⌜err' = err⌝) ∨
      (∃ e, ⌜srvErrOf err e⌝ ∗ ∃ c, sentStatus err' c (Rpctypes.desc e)) ∨
      (∃ m, errMsg err m ∗ ⌜∀ e, ¬ srvErrOf err e⌝ ∗ statusErr err' cUnknown m) }}

end spec

end V3rpc
end EtcdGrove
end Perennial
