/-
## `(*Read).requestCurrentIndex(leaderChangedNotifier)` (internal helper)

**Users.** `LinearizableReadLoop` (`read.go:117`), once per round, with the round's longest lower
bound `l` (ghost).

**Proof sketch.** `NextRequestID()` (`idFresh γi id`), registered with raft by `readEnv`'s
registration (`readCtx rγ (be64 id) (readLbQ l)`), the map `requestIDs` holding exactly the ids so
registered; `sendReadIndex(id)`; the timers (`time.NewTimer`); the loop's `select`: a read state
from `ReadState()` (`readStateVal`: its context's bytes `c` and `readState rγ c i`) whose 8-byte
context decodes to a registered id (then `c = be64 id`: the decode is injective on 8 bytes) is
returned with that id's `readCtx`; a leader change, the error timer, `Stopping()`, a failed resend:
an error (`readErr`); the retry timer and a first commit in the term resend under a fresh id.

**Changes.** The old spec returned raft's read witness for the round's deposited update; restated
over R1's `readState` and the registered context.

**Margin.** None.

Changes: verify-round: takes and gives back the goroutine's `threadTok` (`GoAttach` gives it one; its environment's `Logger`, `LeaderChanged`, `FirstCommitInTermNotify` take a read lock: A7-provability F6).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.read.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Read

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.read.Assumptions]

/-- **A read index for the lower bound `l`**: a read state of a context registered with
`readLbQ l`, or a read path error. -/
def Read.requestCurrentIndex.spec : Prop :=
  ∀ (r : Loc) (srv rf : GoInterface) (rγ : Raft.Cluster) (γi : IdUtil.IdSpace)
    (A : Nat → IProp GF) (lc : Loc) (l : List Raft.LogEntry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read ∗
      r.[go_etcd_io.etcd.server.v3.etcdserver.read.Read, go!"server"] ↦□ srv ∗
      r.[go_etcd_io.etcd.server.v3.etcdserver.read.Read, go!"raft"] ↦□ rf ∗
      readEnv srv rf rγ γi A ∗ recvAny lc ∗ Raft.committedLb rγ l ∗ threadTok }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.read.Read.ty @!!
      go!"requestCurrentIndex")) (Val #lc))
  {{ (i : w64) (err : GoInterface), RET (PairV #i #err); threadTok ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ c : List w8, Raft.readState rγ c i ∗ Raft.readCtx rγ c (readLbQ l)) ∨
      readErr err) }}

end spec
end Read
end EtcdGrove
end Perennial
