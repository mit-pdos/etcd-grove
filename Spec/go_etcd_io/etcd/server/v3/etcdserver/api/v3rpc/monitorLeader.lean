/-
`v3rpc.monitorLeader` (`v3rpc/interceptor.go`; the watch slice's unit W-W, 2026-10-15).
Lean-first (no Rocq counterpart); the vocabulary is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/InvStreamInterceptor.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvStreamInterceptor
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvGoAttach
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead

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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`monitorLeader(s)`** returns a fresh `*streamsMap` (`streamsMapIs`: empty, under its mutex)
and starts, through `s.GoAttach`, the leader monitor: every election timeout (`TickMs ×
ElectionTicks` milliseconds, any value: the product wraps, `time.After` takes any duration) it
reads `s.Leader()`, and after `maxNoLeaderCnt` timeouts without a leader it cancels the streams
in the map (none: it stays empty, `InvStreamInterceptor.lean`) and replaces it by an empty one;
it returns when `s.StoppingNotify()` is closed. Premises: `GoAttach`'s (the goroutine slot and
thread token, the logger's reader slot: returned), the server's `lead`, its `stopping` channel
(closed once, never sent on), the two configuration fields. -/
abbrev v3rpc.monitorLeader.spec : Prop :=
  ∀ (s ch : Loc) (tm et : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvGoRes s ∗ srvLgReader s ∗ srvLeadInv s ∗
      srvStoppingAddr s ↦□ ch ∗ stopChan ch ∗
      cfgTickMsAddr (srvCfgAddr s) ↦□ tm ∗ cfgElectionTicksAddr (srvCfgAddr s) ↦□ et }}
    (App (Val (@! v3rpc.monitorLeader)) (Val #s))
  {{ (smap : Loc), RET #smap; v3rpc.streamsMapIs smap ∗ srvGoRes s ∗ srvLgReader s }}

end spec

end EtcdGrove
end Perennial
