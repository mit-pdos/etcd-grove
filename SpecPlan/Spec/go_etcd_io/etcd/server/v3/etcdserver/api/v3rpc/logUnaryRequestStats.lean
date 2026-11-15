/-
`v3rpc.logUnaryRequestStats` (`server/etcdserver/api/v3rpc/`).

Users: `newLogUnaryInterceptor` (deferred; round 1: also after a failed handler, whose reply is `nil` or a typed `nil`, provability F5).

Proof sketch: the logger's level (W0's `Zap`), `peer.FromContext` (grpc's), the type switch on the reply and request, `proto.Size` of each (`Proto.Size.spec`: both nest less than `depthMax`, the request decoded, the reply by `unaryOut`), the loggable request's `String()` (3h's generated stringers), `lg.Debug`/`lg.Warn`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/logUnaryRequestStats.lean`.

Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Api
public import SpecPlan.Spec.go_uber_org.zap.Api

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

/-- `logUnaryRequestStats(...)` of a run's request and reply (messages read, given back): returns. -/
def logUnaryRequestStats.spec : Prop :=
  ∀ (ctx : GoInterface) (md : MD) (lg : Loc) (warn : w64) (info : Loc) (start : val)
    (reqT repT : go.GoType) (q : Loc) (dq : DFrac) (c : Content) (rv : GoInterface) (Rr : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ Zap.isLogger lg ∗ rpcCtx ctx md ∗ (∃ fm : GoString, info.[google_golang_org.grpc.UnaryServerInfo, go!"FullMethod"] ↦□ fm) ∗
      msgAt reqT q dq c ∗ ⌜depth c < depthMax⌝ ∗ Rr ∗
      (⌜rv = GoInterface.nil ∨ rv = msgVal repT null⌝ ∨
       □ (Rr -∗ ∃ (r : Loc) (dr : DFrac) (c' : Content), ⌜rv = msgVal repT r ∧ depth c' < depthMax⌝ ∗
          msgAt repT r dr c' ∗ (msgAt repT r dr c' -∗ Rr))) }}
    (App (App (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.logUnaryRequestStats)) (Val #ctx)) (Val #lg))
      (Val #warn)) (Val #info)) (Val start)) (Val #(msgVal reqT q))) (Val #rv))
  {{ RET #(); msgAt reqT q dq c ∗ Rr }}

end spec

end V3rpc
end EtcdGrove
end Perennial
