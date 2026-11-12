/-
`v3rpc.logUnaryRequestStats` (`v3rpc/interceptor.go`, names-only: the trust boundary of unit
P3b). Lean-first (no Rocq counterpart); the vocabulary is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/InvQuota.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvQuota

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`logUnaryRequestStats(ctx, lg, warn, info, start, req, resp)` returns** (the log
interceptor's deferred call): with a non-nil logger (`lg.Core().Enabled`, `lg.Debug`/`Warn`) and
the call's `info` (`FullMethod`, read-only), it measures the call's duration, and if the logger
is at debug level or the call was slow, logs the peer (`peer.FromContext`), the method and the
request's and response's sizes and contents (`proto.Size`, the messages' stringers). It reads
`req` and `resp` (a decoded request, the response the handler returned, as `any`), which the
messages' predicates do not cover field by field (the protobuf runtime's reflection, the size
cache): after the handler both are read-only, which the wire models trust (as the runtime's own
marshaling of the response, `notes/decisions.md`, "A generic gRPC specification"). -/
abbrev v3rpc.logUnaryRequestStats.spec : Prop :=
  ∀ (ctx : GoInterface) (lg : Loc) (warn : w64) (info : Loc) (start : time.Time)
    (req resp : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      ⌜lg ≠ null⌝ ∗ srvInfoIs info }}
    (App (App (App (App (App (App (App (Val (@! v3rpc.logUnaryRequestStats)) (Val #ctx))
      (Val #lg)) (Val #warn)) (Val #info)) (Val #start)) (Val #req)) (Val #resp))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
