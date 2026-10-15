/-
`read.NewRead(server, raft)` (read.go). Lean-first (no Rocq counterpart); the request path's unit 4a, see
`Proof/go_etcd_io/etcd/server/v3/etcdserver/read/Inv.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.read.Inv

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.read

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.read.Assumptions]

/-- `NewRead(srv, rf)` with the server's `Done()` (`srvDoneOk`, what `LinearizableReadNotify` needs)
and the read names' notifier meets the read contract (`isRead`) and returns the reader slots of
`r.mux` (`readReader`, as many as Perennial's `RWMutex` admits); the loop's precondition
(`isReadLoopPre`) follows from the server's and raft's contracts, given later (2026-10-13, the
request path's unit 4c: the server's `start` calls `NewRead` before it sets `s.leaderChanged`,
which `isReadServer`'s `LeaderChanged()` reads; until then they were `NewRead`'s premises). -/
abbrev read.NewRead.spec : Prop :=
  ∀ (srv rf : GoInterface) (γr : ReadNames) (x : Loc × GName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read ∗
      srvDoneOk srv ∗ context.isClosedchanInit ∗ ghostVar γr.notifier 1 x }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.read.NewRead)) (Val #srv)) (Val #rf))
  {{ (r : Loc), RET #r; isRead r γr ∗
      (□ ∀ (RQ : w64 → w64 → IProp GF) (LR NR : IProp GF),
        isReadServer srv γr LR NR -∗ isReadRaft rf γr RQ -∗ isReadLoopPre r γr RQ LR NR) ∗
      [∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), readReader r γr }}

end spec

end EtcdGrove
end Perennial
