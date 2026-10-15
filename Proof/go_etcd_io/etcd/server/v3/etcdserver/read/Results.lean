/-
The results of etcd's linearizable read loop (`server/v3/etcdserver/read`; the request path's unit
4a), restated at top level, with the trust base of each printed in the build log (`#print
axioms`).

**The chain.** A client calls `LinearizableReadNotify(ctx)` knowing a lower bound `c` of the
cluster's committed index (`committedAtLeast γr c`). It reads the current notifier `nc` under the
read lock and deposits `c` in `nc`'s need (`read_deposit`: the read invariant keeps a committed
bound at least the need). The loop swaps `nc` out under the write lock and freezes its need at `n`
with a committed bound `n` (`read_swap`), then issues `ReadIndex` at `n`: every read state that
answers one of its requests has an index at least `n` (`isReadRaft`, `readStateOk`), so the
confirmed index `ci ≥ n` (`requestCurrentIndex`). It waits until the applied index reaches `ci`
(`AppliedIndex`, `ApplyWait`), then closes `nc` with `nil`, which tells the waiters the frozen need
and an applied index at least it (`frozenOk`). So a `nil` from `LinearizableReadNotify` means the
applied index has passed a `ReadIndex` issued after the call began, hence at least `c`
(`readIndexOk γr c`, `read_frozenOk_readIndexOk`).

**The contracts** (`read/Inv.lean`): the `server` interface (`isReadServer srv γr LR NR`) and the
`raftInterface` (`isReadRaft rf γr RQ`), which the request path's unit 4b discharges for
`*EtcdServer` and its `raftNode`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.read.Link

@[expose] public section

-- `#print axioms` prints the axioms by their full names (shortening them is slow).
set_option pp.fullNames true

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace read

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.read

section results
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.read.Assumptions]

/-- **`NewRead`'s result meets the read contract** (`Spec/go_etcd_io/etcd/server/v3/etcdserver/read/
NewRead.lean`): given the server's `Done()`, `NewRead(srv, rf)` returns `r` with `isRead r γr`
(the contract the server's `Range`/`Txn` take: `LinearizableReadNotify` returns `nil` only with
`readIndexOk γr c`), the reader slots of `r.mux`, and the loop's precondition from the server's
and raft's contracts. -/
theorem read_new : NewRead.spec (GF := GF) (hG := hG) := wp_NewRead

/-- **The read loop** (`Spec/go_etcd_io/etcd/server/v3/etcdserver/read/Read__LinearizableReadLoop.lean`):
it keeps the read invariant; a notifier is closed with `nil` only after its frozen need was
confirmed by a read index the applied index reached. -/
theorem read_loop : Read.LinearizableReadLoop.spec (GF := GF) (hG := hG) :=
  Read.wp_LinearizableReadLoop

/-- **`LinearizableReadNotify`** (`Spec/go_etcd_io/etcd/server/v3/etcdserver/read/
Read__LinearizableReadNotify.lean`): `nil` only once the applied index reached an index at least
the committed index `c` the caller knew of. -/
theorem read_notify : Read.LinearizableReadNotify.spec (GF := GF) (hG := hG) :=
  Read.wp_LinearizableReadNotify

end results

#print axioms read_new
#print axioms read_loop
#print axioms read_notify

end read
end EtcdGrove
end Perennial
