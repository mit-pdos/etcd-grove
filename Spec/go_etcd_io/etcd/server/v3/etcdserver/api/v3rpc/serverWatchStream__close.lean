/-
`v3rpc.serverWatchStream.close` (`watch.go`). Lean-first (no Rocq counterpart); the
vocabulary is `v3rpc/InvWatchStream.lean` and `v3rpc/InvWatch.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvWatch

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

/-- **`sws.close()`**: closes the mvcc watch stream (its open token), `closec`, and waits for the
send loop (the wait group's adder). -/
abbrev v3rpc.serverWatchStream.close.spec : Prop :=
  ∀ (sws : Loc) (r : v3rpc.WRun GF) (n : w32) (P : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ v3rpc.swsIs sws r ∗ mvcc.watchStreamOpen r.γo ∗
      ownBroadcastChan r.cc r.γcc iprop(True) .Pending ∗
      sync.join.ownAdder (v3rpc.swsF sws go!"wg") n P }}
    (App (Val (sws @!! go.GoType.PointerType v3rpc.serverWatchStream.ty @!! go!"close")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
