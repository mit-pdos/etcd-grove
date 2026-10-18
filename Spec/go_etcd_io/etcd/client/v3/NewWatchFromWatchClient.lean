/-
`clientv3.NewWatchFromWatchClient(wc, c)` (`client/v3/watch.go`; (the watch slice's unit W-C). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvWatcherCore

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- `NewWatchFromWatchClient(wc, c)` of the stub `wc` (on the connection `V.conn`) and a client `c`
(its call options, its logger): a watcher (`isClientWatcherCore`, with the client's logger) as a
`Watcher`. No fact about the server (D19f): construction only allocates; `isClientWatcher_of_core`
adds them. -/
abbrev NewWatchFromWatchClient.spec : Prop :=
  ∀ (V : WEnv GF) (c : Loc) (callSl : GoSlice) (vs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ v3rpc.watchStubAt V.wc V.conn ∗
      ⌜c ≠ null⌝ ∗ structFieldRef go_etcd_io.etcd.client.v3.Client go!"callOpts" c ↦□ callSl ∗
      callSl ↦*□ vs ∗ callOptsOk vs ∗ isClientLogger c ∗ ⌜threadBound GF ≤ 2 ^ 31⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.NewWatchFromWatchClient)) (Val #(wcIface V.wc)))
      (Val #c))
  {{ (wi : GoInterface), RET #wi; ∃ (w lg : Loc),
      ⌜wi = GoInterface.ok (watcherIfaceOf w)⌝ ∗ isClientWatcherCore { V with lg := lg } w }}

end spec

end EtcdGrove
end Perennial
