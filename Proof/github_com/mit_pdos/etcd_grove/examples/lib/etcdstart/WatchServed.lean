/-
**etcd's KV calls and its watch server registered at a served member's address** (k8s 7f-6 E,
2026-11-17). Lean-first (no Rocq counterpart).

`kv_served` (`Served.lean`) with the watch side: from `v3rpc.Server`'s and `Listen`'s results
(`grpcUp`), the member's serving stocks and its serve facts, the right to serve, etcd's KV calls at
the address (`etcdKVAt`), and the member's watch registration (`watchRegAt`): the `Watch` stream at
the address (`v3rpc.etcd_watch_served_chain`), the watch server, and the laws of the server's watch
facts (`srvWOf`, from `srvWOk_of_up`). Unlike `etcd_watch.wk_served_nd` (`watchAddrFacts`, a client
of this one member), it takes no watch condition (`srvOnce`): a cluster's watcher gets it later,
from the instance's invariant (`watchConnFacts_of_members`'s member facts), once the invariant
exists. What a `k`-member start keeps of each member, for a watcher over the members' bridges.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.WatchSrv
public import Proof.go_etcd_io.etcd.client.v3.InvWatch
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcdstart

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section served
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **A member's watch registration at `addr`** (persistent): the `Watch` stream there at its watch
server `R` and the server's watch facts (`srvWOf E γr false`), the watch server, the laws of those
facts, and `R` the server's (`s`, `E`). The watch condition (`srvOnce`) is not here: see the file
header. -/
def watchRegAt (addr : GoString) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames)
    (R : v3rpc.WSrv GF) : IProp GF :=
  iprop(isGrpcStreamMd (Req := v3rpc.pbWatchRequest) (Rep := v3rpc.pbWatchResponse) addr
      go!"/etcdserverpb.Watch/Watch" (v3rpc.watchUp R)
      (fun md => v3rpc.watchSpec R (srvWOf E γr false) (auth.mdTokenOf md)) ∗
    (∃ pw : Loc, v3rpc.isWatchServer pw R) ∗ client.srvWLaws (srvWOf E γr false) ∗
    ⌜R.s = s ∧ R.E = E⌝)

instance watchRegAt_persistent (addr : GoString) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames)
    (R : v3rpc.WSrv GF) : Persistent (watchRegAt addr s E γr R) := by
  unfold watchRegAt; infer_instance

end served

end etcdstart
end EtcdGrove
end Perennial
