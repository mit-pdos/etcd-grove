/-
`s.HardStop()` (`server/etcdserver/server.go`; the restart plan's R2a, 2026-11-02): stop the
server without a leadership transfer. It signals `run` to stop and waits for `run`'s deferred
shutdown: the scheduler stopped, the server's goroutines waited for (`s.wg`), the raft node and the
transport stopped (`raftNode.stop`), `Cleanup` (the lessor, the KV store, the auth store, the
backend and the compactor closed), `done` closed. Lean-first (no Rocq counterpart).

**The triple:** from the right to stop the server (`srvStopRight`, which `Start` gives: `start`
makes the channels `stop` and `done`) and the stop request it sends (`srvStopReq`, R2c-2): evidence
that the server applied the cluster's bootstrap log (`srvBootApplied`: the image needs it, R2c
review F4; R2b-2 review F2), the server's configuration in the stop's scope (`srvStop.scope`: auth
off, no compaction mode; the user's Q2 (b): until then `run.specStop`'s premises) and its data
directory with no dedicated WAL directory (`srvDataDir`), `HardStop` returns with member `id`'s data directory as its
stop left it (`srvDiskImage`, R2c), at the request names `ρ` the right records, from which the
member can be started again. It sends a stop request on `stop` (or finds `done` already closed),
waits for `done`, and takes the image `run`'s shutdown escrowed there with the right's claim
(`srvDoneInv`). The server's other resources are not given back: the next incarnation has its own,
and goroutines of this one may still hold some (an `http.Serve` handler in flight). (R2b-2,
2026-11-02: until then, in the R2a draft, also the request view `isServerReq`, for "`Start` was
called"; a `HardStop` of a server never started blocks forever, which partial correctness allows,
and the right now comes from `Start`.)
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRestart

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- See the file header. -/
abbrev EtcdServer.HardStop.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (γ : SrvRaft) (ρ : ReqNames) (id : w64) (dd : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvStopRight s E γ ρ id dd ∗ srvStopReq s E ρ dd }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"HardStop")) (Val #()))
  {{ RET #(); srvDiskImage γ ρ id dd }}

end spec

end EtcdGrove
end Perennial
