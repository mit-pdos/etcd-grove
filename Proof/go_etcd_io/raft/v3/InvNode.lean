/-
# Raft's node API: the sealed predicates and their laws (2026-10-27; the API module since 2026-10-28)

What a client of raft's `node` states its proofs in: the predicates of the specs in
`Spec/go_etcd_io/raft/v3/<fn>.lean` (`StartNode`, `RestartNode`, `node.Propose`, ...), each sealed
(`@[no_expose]`) over its definition in the internal `InvApi.lean`/`InvApiDyn.lean` (namespace
`ApiImpl`), and the laws a client proves with. (Until 2026-10-28 `NodeApiDraft.lean`, namespace
`Draft`, which also held the specs; this module's name was the older sealed node API's, now
`InvNodeChan.lean`.)

The statements decided with the user on 2026-10-27 (`notes/decisions.md`, "Raft's node API over an
abstract log"; memory "spec state principles"):

- **The abstract state** is the committed log as a client sees it: a list of `LogEntry` (term, type,
  data). The index is the position (not stored); the term is raft's choice (stored, since `Ready`
  shows it).
- **Two views of it:** the client owns the entries it requested, `ownCommittedOps γ ops` (exclusive:
  `opsOf` of the committed log, which leaves out the fillers raft appends itself, `isFiller`), and
  knows the full log through `isCommittedLogLb γ l` (persistent, a lower bound, fillers included) and
  the `Ready`s; plain laws relate them (no invariant, no mask). So a client gives an update only for
  the entries it requests.
- **Proposals are atomic updates only:** `Propose` and `ProposeConfChange` take an update appending
  their entry; raft keeps no registry of the client's operations (no `propIs`, `propFresh`,
  `deposited`, `prop_collect`, `entDataIs`, `reCCOk`). The update's `COMM` is `True`: whatever the
  client needs, the update puts into the client's own invariant.
- **The namespace is the caller's:** a cluster is allocated in a namespace `N` the caller picks; every
  update's mask is `⊤ \ ↑N`; raft divides `N` privately.

**Implemented (2026-10-27):** every predicate is sealed (`@[no_expose]`) over its definition in
`InvApi.lean` and `InvApiDyn.lean` (namespace `ApiImpl`), every law proved there, every spec in its
function's proof file: nothing here is `sorry`.
Marked **(open)**: premises carried over unchanged from today's specs, for the items not yet
redesigned (the storage contract, the term budget, the static/dynamic modes, the rest of a `Ready`).

**What the key-value store needs (2026-10-27, `examples/kv` ported onto this draft):** the static
cluster (`isStaticCluster`, `cluster_alloc_static`, `RestartNode`), the rest of a `Ready`
(`readyRest`, `readySnap`), `Advance`, `Step` (`sentMsg`, `msgCredits`, `stepIn`), `Tick`
(`tickCredit`), `TransferLeadership` (`leaderTransferOn`) and the snapshots' certificates
(`snapshotCert`, `storageCertInv`, `storageCertLink`). The storage contract itself (`StorageModel`,
`isStorageD`, `appendRight`, `readyOut`, `advReceipt`, `storFloor`) and `MemoryStorage`'s specs and
predicates are raft's storage API, carried over unchanged (not redesigned here).
-/
module

public import Proof.go_etcd_io.raft.v3.InvNodeCtx
public import Perennial.Proof.context
public import Proof.go_etcd_io.raft.v3.InvMemstorage
public import Proof.go_etcd_io.raft.v3.NodeApiVocab
-- the implementation (`InvApi.lean`, `InvApiDyn.lean`), not exported
import Proof.go_etcd_io.raft.v3.InvApi
import Proof.go_etcd_io.raft.v3.InvApiView
import Proof.go_etcd_io.raft.v3.InvStatus

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section api
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-! ## The abstract state -/

/-- A cluster's ghost names (opaque to clients). -/
@[no_expose] def Cluster : Type 1 := ApiImpl.Cluster

/-- **The cluster's network may duplicate a `MsgProp`** (2026-10-29, S1): chosen by the client at
allocation (`cluster_alloc`; `false` for the other allocations). In such a cluster a proposal's
update is persistent (`node.Propose`'s `□?γ.dup`), and so are a `MsgProp`'s credits
(`msgCredits_copy`). -/
@[no_expose] def Cluster.dup (γ : Cluster) : Bool := γ.raft.dup

/-- **The committed requested entries, the client's** (exclusive): `opsOf` of the committed log.
Raft changes it only by firing an update the client gave it, when the requested entry commits;
fillers commit without changing it. -/
@[no_expose] def ownCommittedOps (γ : Cluster) (ops : List LogEntry) : IProp GF :=
  ApiImpl.ownCommittedOps γ ops

/-- **A lower bound of the committed log**, fillers included (persistent): the committed log extends
`l`. -/
@[no_expose] def isCommittedLogLb (γ : Cluster) (l : List LogEntry) : IProp GF :=
  ApiImpl.isCommittedLogLb γ l

instance ownCommittedOps_timeless (γ : Cluster) (ops : List LogEntry) :
    Timeless (ownCommittedOps (GF := GF) γ ops) := by
  unfold ownCommittedOps; exact ApiImpl.ownCommittedOps_timeless γ ops
instance isCommittedLogLb_persistent (γ : Cluster) (l : List LogEntry) :
    Persistent (isCommittedLogLb (GF := GF) γ l) := by
  unfold isCommittedLogLb; exact ApiImpl.isCommittedLogLb_persistent γ l
instance isCommittedLogLb_timeless (γ : Cluster) (l : List LogEntry) :
    Timeless (isCommittedLogLb (GF := GF) γ l) := by
  unfold isCommittedLogLb; exact ApiImpl.isCommittedLogLb_timeless γ l

omit [StorageModel GF] sem package_sem in
/-- The committed requested entries are those of a committed log. (2026-10-27, for kv: the
client's resource kept, which a persistent conclusion alone does not give back.) -/
theorem ownCommittedOps_get_lb (γ : Cluster) (ops : List LogEntry) :
    ownCommittedOps (GF := GF) γ ops ⊢
      ownCommittedOps γ ops ∗ ∃ l, isCommittedLogLb γ l ∗ ⌜opsOf l = ops⌝ := by
  unfold ownCommittedOps isCommittedLogLb; exact ApiImpl.ownCommittedOps_get_lb_impl γ ops

omit [StorageModel GF] sem package_sem in
/-- The requested entries of a committed log are a prefix of those committed now. -/
theorem ownCommittedOps_lb_prefix (γ : Cluster) (ops l : List LogEntry) :
    ownCommittedOps (GF := GF) γ ops ∗ isCommittedLogLb γ l ⊢ ⌜opsOf l <+: ops⌝ := by
  unfold ownCommittedOps isCommittedLogLb; exact ApiImpl.ownCommittedOps_lb_prefix_impl γ ops l

omit [StorageModel GF] sem package_sem in
/-- Every committed log extends the empty one. -/
theorem isCommittedLogLb_nil (γ : Cluster) : ⊢ isCommittedLogLb (GF := GF) γ [] := by
  unfold isCommittedLogLb; exact ApiImpl.isCommittedLogLb_nil_impl γ

omit [StorageModel GF] sem package_sem in
theorem isCommittedLogLb_mono (γ : Cluster) (l1 l2 : List LogEntry) :
    l1 <+: l2 → isCommittedLogLb (GF := GF) γ l2 ⊢ isCommittedLogLb γ l1 := by
  unfold isCommittedLogLb; exact ApiImpl.isCommittedLogLb_mono_impl γ l1 l2

omit [StorageModel GF] sem package_sem in
theorem isCommittedLogLb_agree (γ : Cluster) (l1 l2 : List LogEntry) :
    isCommittedLogLb (GF := GF) γ l1 ∗ isCommittedLogLb γ l2 ⊢ ⌜l1 <+: l2 ∨ l2 <+: l1⌝ := by
  unfold isCommittedLogLb; exact ApiImpl.isCommittedLogLb_agree_impl γ l1 l2

/-! ## The cluster and its nodes -/

/-! ## Read contexts -/

/-- **The read contexts, the client's** (exclusive): `U` is the finite set of the contexts committed
so far (`readCtx_commit`); any other context is unused and may be committed. A new cluster gives it
at `∅`. (The authority-over-used-keys pattern of a ghost map; a client whose readers run
concurrently shares it through its own invariant.) -/
@[no_expose] def ownReadCtxs (γ : Cluster) (U : GSet (List w8)) : IProp GF :=
  ApiImpl.ownReadCtxs γ U

instance ownReadCtxs_timeless (γ : Cluster) (U : GSet (List w8)) :
    Timeless (ownReadCtxs (GF := GF) γ U) := by
  unfold ownReadCtxs; exact ApiImpl.ownReadCtxs_timeless γ U

/-- **The read context `c` is committed to `Q`** (persistent): every read with context `c` takes
effect at a moment when the committed requested entries are some `ops`, and gives `□ Q ops`
(`readStateOk_ctx`). A client may retry a read with the same context. -/
@[no_expose] def isReadCtx (γ : Cluster) (N : Namespace) (c : List w8)
    (Q : List LogEntry → IProp GF) : IProp GF :=
  ApiImpl.isReadCtx γ N c Q

instance isReadCtx_persistent (γ : Cluster) (N : Namespace) (c : List w8)
    (Q : List LogEntry → IProp GF) : Persistent (isReadCtx (GF := GF) γ N c Q) := by
  unfold isReadCtx; exact ApiImpl.isReadCtx_persistent γ N c Q

omit [StorageModel GF] sem package_sem in
/-- **Committing an unused context `c` to `Q`**, once: with an update that, at the moment a read
takes effect, proves `□ Q ops` of the committed requested entries `ops` (leaving them unchanged). A
client that wants its read to see what it knew to be committed (`isCommittedLogLb γ l0`) chooses
`Q ops := ⌜opsOf l0 <+: ops⌝ ∗ …`. -/
theorem readCtx_commit (γ : Cluster) (N : Namespace) (U : GSet (List w8)) (c : List w8)
    (Q : List LogEntry → IProp GF) :
    c ∉ U →
    ownReadCtxs (GF := GF) γ U ∗
      □ AU <{ ∃∃ (ops : List LogEntry), ownCommittedOps γ ops }> @ ⊤ \ ↑N, ∅
           <{ ownCommittedOps γ ops, COMM □ Q ops }> ⊢
    |==> (ownReadCtxs γ (insert c U) ∗ isReadCtx γ N c Q) := by
  unfold ownReadCtxs isReadCtx ownCommittedOps; exact ApiImpl.readCtx_commit_impl γ N U c Q

/-- **A read state** (persistent): a `Ready`'s `ReadState{Index: idx, RequestCtx: c}`. -/
@[no_expose] def readStateOk (γ : Cluster) (N : Namespace) (c : List w8) (idx : w64) : IProp GF :=
  ApiImpl.readStateOk γ N c idx

instance readStateOk_persistent (γ : Cluster) (N : Namespace) (c : List w8) (idx : w64) :
    Persistent (readStateOk (GF := GF) γ N c idx) := by
  unfold readStateOk; exact ApiImpl.readStateOk_persistent γ N c idx

/-- **What a read state tells the client** of a context it committed: a read with context `c` took
effect when the committed log was `l`, of length `idx`, and gave `Q` of its requested entries. A
ghost update within `N`, given a committed log `l'` at least `idx` long (raft hands the read state out
before the client knows the log committed that far: it waits until it has applied `idx` entries);
the result under two laters (the read's deposit and the context's predicate are both saved
predicates). (2026-10-27: changed from the first draft's pure entailment, which raft cannot prove:
`ApiImpl.readStateOk_ctx_impl`.) -/
theorem readStateOk_ctx (γ : Cluster) (N : Namespace) (c : List w8) (idx : w64)
    (Q : List LogEntry → IProp GF) (l' : List LogEntry) (E : CoPset) :
    ↑N ⊆ E → uint.nat idx ≤ l'.length →
    ⊢ readStateOk (GF := GF) γ N c idx -∗ isReadCtx γ N c Q -∗ isCommittedLogLb γ l' ={E}=∗
      ∃ l, ⌜l.length = uint.nat idx⌝ ∗ isCommittedLogLb γ l ∗ ▷ ▷ □ Q (opsOf l) := by
  intro HE Hle
  unfold readStateOk isReadCtx isCommittedLogLb
  exact ApiImpl.readStateOk_ctx_impl γ N c idx Q l' E HE Hle

omit [StorageModel GF] sem package_sem in
/-- **A read state's context was committed** (`readCtx_commit`): a read is requested only with a
committed context (`node.ReadIndex`). (2026-10-27, for kv: the applier tells its own reader's
context from another's by it.) -/
theorem readStateOk_used (γ : Cluster) (N : Namespace) (c : List w8) (idx : w64) (U : GSet (List w8)) :
    readStateOk (GF := GF) γ N c idx ∗ ownReadCtxs γ U ⊢ ⌜c ∈ U⌝ := by
  unfold readStateOk ownReadCtxs; exact ApiImpl.readStateOk_used_impl γ N c idx U

/-! ## The bootstrap log's length (2026-10-29, U9: the static cluster's section, `isStaticCluster`,
`cluster_alloc`, `cluster_alloc_static`, deleted; one cluster, `isCluster`, `InvNodeRule.lean`) -/

/-- The length of the bootstrap log the cluster was started from (sealed). -/
@[no_expose] def Cluster.bootLen (γ : Cluster) : Nat := γ.raft.reBoot.length

/-- **The indices raft hands out fit `MemoryStorage.Append`'s bound** (persistent; 2026-10-27, the
server port's addition): the receipts' bound past the bootstrap log is at most `2 ^ 61`. Every
index raft hands out is within its log, whose last index has a record keeping a time receipt
(`lastRec_receipt`), so below the receipts' bound past the bootstrap log; so is every committed log
(`isCommittedLogLb_length`, `readyRest_fits`). What `cluster_alloc` and `dynamicCluster_alloc` give
under that premise; what etcd's raft loop needs to call `MemoryStorage.Append` (which checks no
bound, unlike the key-value example's `fits`). -/
@[no_expose] def readyFits (γ : Cluster) (_N : Namespace) : IProp GF :=
  iprop(⌜receiptBound GF + γ.bootLen ≤ 2 ^ 61⌝)

instance readyFits_persistent (γ : Cluster) (N : Namespace) :
    Persistent (readyFits (GF := GF) γ N) := by
  unfold readyFits; infer_instance

/-- **A running node** `n` of id `id` in the cluster `γ` (persistent). -/
@[no_expose] def isNode (n : Loc) (γ : Cluster) (N : Namespace) (id : w64) : IProp GF :=
  ApiImpl.isNode n γ N id

instance isNode_persistent (n : Loc) (γ : Cluster) (N : Namespace) (id : w64) :
    Persistent (isNode (GF := GF) n γ N id) := by
  unfold isNode; exact ApiImpl.isNode_persistent n γ N id

/-- The node's `Ready` channel `ch` (persistent). -/
@[no_expose] def isReadyChan (n : Loc) (γ : Cluster) (N : Namespace) (ch : Loc) : IProp GF :=
  ApiImpl.isReadyChan n γ N ch

instance isReadyChan_persistent (n : Loc) (γ : Cluster) (N : Namespace) (ch : Loc) :
    Persistent (isReadyChan (GF := GF) n γ N ch) := by
  unfold isReadyChan; exact ApiImpl.isReadyChan_persistent n γ N ch

/-- **The `Ready` loop's token** (exclusive): one per node, at the loop's state `st`. -/
@[no_expose] def nodeDriver (n : Loc) (γ : Cluster) (N : Namespace) (st : NodeDriverState) : IProp GF :=
  ApiImpl.nodeDriver n γ N st

/-- (2026-10-29, stage U9a) **The node runs** (fractional; the whole, `q = 1`, is what `node.Stop`
takes): the client's share of the node's liveness, from `StartNode` and `RestartNode` in a cluster
with reconfiguration (`StartNode.dynamicSpec`, `RestartNode.spec`). In a cluster with
reconfiguration it excludes `nodeStopped` (`nodeRunning_stopped`): its holder refutes the stopped
answers. -/
@[no_expose] def nodeRunning (n : Loc) (γ : Cluster) (N : Namespace) (q : Qp) : IProp GF :=
  ApiImpl.nodeRunning n γ N q

instance nodeRunning_fractional (n : Loc) (γ : Cluster) (N : Namespace) :
    Fractional (nodeRunning (GF := GF) n γ N) where
  fractional p q := by unfold nodeRunning; exact ApiImpl.nodeRunning_split_impl n γ N p q

instance nodeRunning_as_fractional (n : Loc) (γ : Cluster) (N : Namespace) (q : Qp) :
    AsFractional (nodeRunning (GF := GF) n γ N q) ioΦ (nodeRunning n γ N) ioq q where
  as_fractional := .rfl
  as_fractional_fractional := nodeRunning_fractional n γ N

/-- (2026-10-29, stage U9a) **The node stopped** (persistent): its `run` returned, its `done`
closed (`node.Stop`'s post; the stopped case of `node.Advance` and `node.ApplyConfChange`). In a
cluster with reconfiguration it excludes `nodeRunning` (`nodeRunning_stopped`). -/
@[no_expose] def nodeStopped (n : Loc) (γ : Cluster) (N : Namespace) : IProp GF :=
  ApiImpl.nodeStopped n γ N

instance nodeStopped_persistent (n : Loc) (γ : Cluster) (N : Namespace) :
    Persistent (nodeStopped (GF := GF) n γ N) := by
  unfold nodeStopped; exact ApiImpl.nodeStopped_persistent n γ N

/-- (raft-final, 2026-10-29, K5: the user's decision overriding the design's A9) **The error of a
`node` call that hands a message to `run`, the stopped answer carrying `nodeStopped`** (persistent):
`nil`, `ErrStopped` with the node stopped, or the context's. A holder of `nodeRunning` refutes the
second (`nodeRunning_stopped`). `nodeErrS_nodeErr` forgets the stop (until then the posts' plain
`nodeErr`). -/
def nodeErrS (n : Loc) (γ : Cluster) (N : Namespace) (cd : context.ContextDesc (IProp GF))
    (err : GoInterface) : IProp GF :=
  iprop(⌜err = interface.nil⌝ ∨ (errStopped err ∗ nodeStopped n γ N) ∨ ctxErr cd err)

instance nodeErrS_persistent (n : Loc) (γ : Cluster) (N : Namespace)
    (cd : context.ContextDesc (IProp GF)) (err : GoInterface) :
    Persistent (nodeErrS (GF := GF) n γ N cd err) := by
  unfold nodeErrS; infer_instance

theorem nodeErrS_nodeErr (n : Loc) (γ : Cluster) (N : Namespace)
    (cd : context.ContextDesc (IProp GF)) (err : GoInterface) :
    nodeErrS (GF := GF) n γ N cd err ⊢ nodeErr cd err := by
  unfold nodeErrS nodeErr
  iintro (%H | ⟨#H, -⟩ | #H)
  · ileft; ipureintro; exact H
  · iright; ileft; iexact H
  · iright; iright; iexact H

/-- (raft-final, 2026-10-29, K5) **A proposal's error, the stopped answer carrying `nodeStopped`**:
`nodeErrS`, or the proposal's result from `run` (`stepErr`). -/
def propErrS (n : Loc) (γ : Cluster) (N : Namespace) (cd : context.ContextDesc (IProp GF))
    (err : GoInterface) : IProp GF :=
  iprop(nodeErrS n γ N cd err ∨ stepErr err)

instance propErrS_persistent (n : Loc) (γ : Cluster) (N : Namespace)
    (cd : context.ContextDesc (IProp GF)) (err : GoInterface) :
    Persistent (propErrS (GF := GF) n γ N cd err) := by
  unfold propErrS; infer_instance

theorem propErrS_propErr (n : Loc) (γ : Cluster) (N : Namespace)
    (cd : context.ContextDesc (IProp GF)) (err : GoInterface) :
    propErrS (GF := GF) n γ N cd err ⊢ propErr cd err := by
  unfold propErrS propErr
  iintro (H | #H)
  · ileft; iapply nodeErrS_nodeErr $$ H
  · iright; iexact H

/-- (2026-10-29, stage U7) **A `Status` value's memory is the caller's** (`node.Status`'s post):
heap ownership only, of its `*pb.HardState` (read-only), its configuration's maps and a leader's
progress copy (each progress with its own `Inflights`), or the zero `Status{}` of a stopped node.
No fact ties the values to the cluster. (`AutoLeave` of the copy is always `false`: `Config.Clone`
drops it, `issues/raft-config-clone-autoleave.md`.) Laws to read it come with a client that needs
them. -/
@[no_expose] def statusOwn (st : Status) : IProp GF :=
  statusOwnRaw st


/-! ## Snapshots' certificates -/

/-- **The snapshot `k` is certified** for the cluster (persistent; today `raftSnapCertD`): its
configuration the cluster's at its index, its data what the client vouches for of the committed log
up to it. -/
@[no_expose] def snapshotCert (γ : Cluster) (N : Namespace) (k : SnapTrip) : IProp GF :=
  ApiImpl.snapshotCert γ N k

instance snapshotCert_persistent (γ : Cluster) (N : Namespace) (k : SnapTrip) :
    Persistent (snapshotCert (GF := GF) γ N k) := by
  unfold snapshotCert; exact ApiImpl.snapshotCert_persistent γ N k

/-! ## Messages and the term budget (open: carried over) -/

/-- (open) **A message node `src`'s `Ready` handed out** (persistent; today `isRaftMsg` and
`termLB`): sent by the node `src` of the cluster, legitimately, of a term within the cluster's
budget. (2026-10-27, for etcd's server: names its sender, `sentMsg_appFrom`.) -/
@[no_expose] def sentMsg (γ : Cluster) (N : Namespace) (src : w64) (st : MsgSt) : IProp GF :=
  ApiImpl.sentMsg γ N src st

instance sentMsg_persistent (γ : Cluster) (N : Namespace) (src : w64) (st : MsgSt) :
    Persistent (sentMsg (GF := GF) γ N src st) := by
  unfold sentMsg; exact ApiImpl.sentMsg_persistent γ N src st

/-- **A `MsgApp` is from the node that sent it** (`AppFrom`: its `From` is `src`): what rafthttp's
msgappv2 codec needs, whose frames carry no sender. -/
theorem sentMsg_appFrom (γ : Cluster) (N : Namespace) (src : w64) (st : MsgSt) :
    sentMsg (GF := GF) γ N src st ⊢ ⌜AppFrom src st⌝ := by
  unfold sentMsg; exact ApiImpl.sentMsg_appFrom_impl γ N src st

/-- (open) **What a sent message carries for its receiver's `Step`** (today `rdCred`, one for a
`MsgReadIndex`, and `stTks`, a forwarded proposal's tickets). -/
@[no_expose] def msgCredits (γ : Cluster) (N : Namespace) (st : MsgSt) : IProp GF :=
  ApiImpl.msgCredits γ N st

/-- (open) **A message `node.Step` takes** at the node `id` (today `stepP`): the message at `ml`. -/
@[no_expose] def stepIn (γ : Cluster) (N : Namespace) (id : w64) (ml : Loc) : IProp GF :=
  ApiImpl.stepIn γ N id ml

/-- (open) **Stepping a sent message**: a copy of it (its fields, entries and snapshot; no local
responses), owned with its entries slice fresh, addressed to `id`, with its credits (until
2026-10-29, stage U7, also a tick credit for a `MsgTimeoutNow`: `node.Step` now takes its own time
receipt): a forwarded proposal (of any context: its abstraction ignores it),
or what a node steps from the network (`NetMsgOk`, no leader transfer; a snapshot below `2^61`).
(Today kv's `stepP_deliverable`. 2026-10-27, for etcd's server, whose nodes run with `PreVote`: the
pre-vote premise `bootedCluster` in place of excluding it, and no premise on a forwarded proposal's
context; until then `stepIn_intro_booted` beside it. 2026-10-29, stage U4: no pre-vote premise, in
any cluster: a node at term `0` has an empty log and grants a pre-vote request, so no rejection is
sent at term `0`; until then `⌜st.msg.Type' ≠ MsgPreVote⌝ ∨ bootedCluster γ`.) -/
theorem stepIn_intro (γ : Cluster) (N : Namespace) (id : w64) (ml : Loc) (src : w64) (st : MsgSt) :
    st.msg.To' = id →
    sentMsg (GF := GF) γ N src st ∗
      msgPtsC ml (DFrac.own 1) (DFrac.own 1) true ⟨st.msg, st.ents, st.snap, st.ctx, []⟩ ∗
      msgCredits γ N st ⊢
    |==> stepIn γ N id ml := by
  intro H3
  unfold sentMsg msgCredits stepIn
  exact ApiImpl.stepIn_intro_impl γ N id ml src st H3

/-- (raft-final, 2026-10-29, U7: the design's §2.5, C12's `sentMsg_shape`) **A sent message has the
shape raft sends** (`SentMsgShape`: its type, a nonzero sender, stamped or not by type, from another
node but for the listed types, a `MsgApp` of raft's shape, the transfer messages with no entries and
no context, no responses), and a `MsgSnap` holds a snapshot of index below `2^61` (the storage's
snapshots are `snapshotValid`, which bounds it: the design's A10). What a transport needs to marshal
it and a receiver to step it. -/
theorem sentMsg_shape (γ : Cluster) (N : Namespace) (src : w64) (st : MsgSt) :
    sentMsg (GF := GF) γ N src st ⊢
      ⌜SentMsgShape st ∧
        (st.msg.Type' = MsgSnap → ∃ sv, st.snap = some sv ∧ uint.Z sv.Metadata'.Index' < 2 ^ 61)⌝ := by
  sorry

/-- (raft-final, 2026-10-29, U7: S1's `msgCredits_intro`, the design's §2.9) **A delivered copy of a
message other than a proposal needs nothing**: its credits are a forwarded proposal's tickets only
(a `MsgReadIndex`'s read credit is minted by its receiver, `rdPool`). -/
theorem msgCredits_intro (γ : Cluster) (N : Namespace) (st : MsgSt) :
    st.msg.Type' ≠ MsgProp → ⊢ |==> msgCredits (GF := GF) γ N st := by
  sorry

/-! ## The storage contract at the node API (U8 v2, 2026-10-29; candidate 17 rev 3 §2) -/

/-- **Raft's applied index of node `id` has reached `k`** (persistent, timeless; raft-issued: by
`Advance`, `node.Advance`'s post). -/
@[no_expose] def nodeAppliedLb (γ : Cluster) (id : w64) (k : Nat) : IProp GF :=
  ApiImpl.nodeAppliedLbU γ id k

/-- **Node `id` handed out a snapshot at index `k`** to install (persistent, timeless; raft-issued:
by a snapshot `Ready`). -/
@[no_expose] def snapGiven (γ : Cluster) (id : w64) (k : Nat) : IProp GF :=
  ApiImpl.snapGivenU γ id k

instance nodeAppliedLb_persistent (γ : Cluster) (id : w64) (k : Nat) :
    Persistent (nodeAppliedLb (GF := GF) γ id k) := by
  sorry -- PHASE1
  /- PHASE1-OLD
 by
  unfold nodeAppliedLb; infer_instance
  -/

instance nodeAppliedLb_timeless (γ : Cluster) (id : w64) (k : Nat) :
    Timeless (nodeAppliedLb (GF := GF) γ id k) := by
  sorry -- PHASE1
  /- PHASE1-OLD
 by
  unfold nodeAppliedLb; infer_instance
  -/

instance snapGiven_persistent (γ : Cluster) (id : w64) (k : Nat) :
    Persistent (snapGiven (GF := GF) γ id k) := by
  sorry -- PHASE1
  /- PHASE1-OLD
 by
  unfold snapGiven; infer_instance
  -/

instance snapGiven_timeless (γ : Cluster) (id : w64) (k : Nat) :
    Timeless (snapGiven (GF := GF) γ id k) := by
  sorry -- PHASE1
  /- PHASE1-OLD
 by
  unfold snapGiven; infer_instance
  -/

theorem nodeAppliedLb_zero (γ : Cluster) (id : w64) : ⊢ nodeAppliedLb (GF := GF) γ id 0 := by
  unfold nodeAppliedLb; exact ApiImpl.nodeAppliedLbU_zero γ id

theorem nodeAppliedLb_mono (γ : Cluster) (id : w64) (k k' : Nat) :
    k' ≤ k → nodeAppliedLb (GF := GF) γ id k ⊢ nodeAppliedLb γ id k' := by
  intro h; unfold nodeAppliedLb; exact ApiImpl.nodeAppliedLbU_mono γ id k k' h

/-! ## The rest of a `Ready` -/

/-- (open) A `Ready`'s storage part, by its snapshot's loan (U8 v2, 2026-10-29: the frozen design's
§3): none -- the right to write the entries `es` (`appendRight`: the log from their first index on,
with the end; nothing for no entries) and the committed entries `ce` below them frozen
(`ceFrozen`) -- or a snapshot (its loan `l`, `ce` empty): the committed log up to it (`strip l.dlv`,
its entries at their positions), past what was delivered, half of the snapshot, its certificate
(`snapshotCert`; its validity, `snapshotCert_valid`), every range of the storage from an index at
most the snapshot's on, with the end, and the right to install it (`snapGiven`). (Until U8 v2 the
old contract's `readyOut`: the storage itself.) -/
def readySnap (γ : Cluster) (N : Namespace) (id : w64) (rd : Ready) (st : NodeDriverState)
    (ce : List LogEntry) (es : List EntryM) : Option SnapLoan → IProp GF
  | none => iprop(⌜rd.Snapshot' = null⌝ ∗ appendRight st.storage es ∗
      ceFrozen st.storage st.delivered.length (LogEntry.toEntries ce st.delivered.length) es)
  | some l => iprop(
      ⌜l.dlv = LogEntry.toEntries (strip l.dlv) 0 ∧ l.ptr = rd.Snapshot' ∧ ce = [] ∧
        st.delivered <+: strip l.dlv ∧ st.delivered.length < l.dlv.length ∧
        l.dlv.length = uint.nat l.snap.Metadata'.Index' ∧ 0 < uint.Z l.snap.Metadata'.Index' ∧
        uint.Z l.snap.Metadata'.Index' < 2 ^ 61 ∧ uint.Z l.fl ≤ uint.Z l.snap.Metadata'.Index' ∧
        LogIndicesOk (snapId l.snap) es⌝ ∗
      ownSnapS l.ptr (DFrac.own (1 : Qp).half) l.snap ∗ isCommittedLogLb γ (strip l.dlv) ∗
      snapshotCert γ N (snapTrip l.snap l.snap.Metadata'.ConfState'.lists) ∗
      (∃ (k : Nat) (old : List EntryM), ⌜k ≤ uint.nat l.snap.Metadata'.Index'⌝ ∗
        storLog st.storage k (DFrac.own 1) old ∗ storEnd st.storage (k + old.length)) ∗
      snapGiven γ id (uint.nat l.snap.Metadata'.Index'))

/-- (open) **The rest of a `Ready`** after its committed entries `ce` and read states, at the loop's
state `st` (today's `readyDataL` without them; the storage's part in the storage contract's
vocabulary, `appendRight`, `readyOut`): the entries `es` to persist, the messages (each owned as
`Ready` hands it out, `readyDq`, sent, with its credits), the hard state `h` (`nil` or not:
`hsOpt`) and the soft state, the indices' bound, and the storage's part (`readySnap`, by the
snapshot's loan `L`). (2026-10-27, for etcd's server: the messages are the node `id`'s, `sentMsg`.) -/
def readyRest (γ : Cluster) (N : Namespace) (id : w64) (rd : Ready) (st : NodeDriverState)
    (ce : List LogEntry) (es : List EntryM) (h : HardStateM) (L : Option SnapLoan) : IProp GF :=
  iprop(∃ ms : List QMsg,
    entsRO rd.Entries' es ∗
    rd.Messages' ↦* ms.map QMsg.loc ∗
    ([∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st ∗ sentMsg γ N id q.st ∗
      msgCredits γ N q.st) ∗
    hsOpt rd.HardState' h ∗ softStateRO rd.SoftState' ∗
    ⌜∃ Lx : Int, Lx < 2 ^ 64 ∧
      (∀ e0, es.head? = some e0 → uint.Z e0.Index' + (es.length : Int) ≤ Lx + 1) ∧
      ((st.delivered ++ ce).length : Int) ≤ Lx ∧ Lx < (receiptBound GF : Int) + γ.bootLen⌝ ∗
    readySnap γ N id rd st ce es L)

/-- The implementation's rest of a `Ready` is the draft's. -/
private theorem readyRest_of_impl (γ : Cluster) (N : Namespace) (id : w64) (rd : Ready)
    (st : NodeDriverState) (ce : List LogEntry) (es : List EntryM) (h : HardStateM)
    (L : Option SnapLoan) :
    ApiImpl.readyRest (GF := GF) γ N id rd st ce es h L ⊢ readyRest γ N id rd st ce es h L := by
  cases L <;> exact .rfl

/-- (raft-final, 2026-10-29, the design's A2, review 1's H2) **A `Ready`'s committed entries inside
its batch are the batch's** (pure): after a `Ready` without a snapshot whose entries `es` start at
index `k`, the committed entry at log index `|delivered| + 1 + j` (position `j` of `ce`), if at or past
`k`, is `es`'s at that index (both lists are read from raft's log in the same step). So a snapshot
the client creates at an in-batch index has the committed term (`snapshotValid`), and `ce` ends within
the batch. -/
theorem readyRest_ceInBatch (γ : Cluster) (N : Namespace) (id : w64) (rd : Ready)
    (st : NodeDriverState) (ce : List LogEntry) (es : List EntryM) (h : HardStateM) :
    readyRest (GF := GF) γ N id rd st ce es h none ⊢
      ⌜∀ e0, es.head? = some e0 → ∀ (j : Nat) (e : LogEntry), ce[j]? = some e →
        uint.nat e0.Index' ≤ st.delivered.length + 1 + j →
        (es[st.delivered.length + 1 + j - uint.nat e0.Index']?).map LogEntry.ofEntryM = some e⌝ ∗
      readyRest γ N id rd st ce es h none := by
  sorry

/-! ## What etcd's server needs (2026-10-27, branch `server-port`; implemented the same day)

The server runs raft's **dynamic** mode (its membership changes: `notes/membership-plan.md`), in
raft's no-snapshot and no-transfer modes, and its transport (rafthttp) carries the messages a
`Ready` hands out. What it uses of raft's tree today, and the statements below, are listed in
`notes/decisions.md`, "Raft's node API for etcd's server (draft)". Every predicate here is sealed
over its definition in `InvApiDyn.lean` (or `InvApi.lean`), every law and spec proved
there: nothing here is `sorry`; **(open)** marks what carries
today's meaning unchanged (no redesign). The pure vocabulary (`Membership`, `ConfChangeDecoder`,
`ConfigView`, `NoConfChangeIn`, `confStateIs`) is in `NodeApiVocab.lean`. -/

/-! ### The configuration, abstractly -/

/-- (open) **A membership raft accepts** (sealed; today `CfgOk` and `CCGood` of the configuration
with its progress flags): what `checkInvariants` accepts, with some voter, within raft's bound on
the tracked ids. -/
@[no_expose] def Membership.Valid (m : Membership) : Prop := ApiImpl.memValid m

/-- A non-empty set of non-zero voters, within raft's bound, is a valid membership. -/
theorem Membership.simple_valid (vs : GSet w64) :
    vs ≠ ∅ → W64 0 ∉ vs → GMap.size vs < 2 ^ 62 → (Membership.simple vs).Valid := by
  intro hne _ hsz; exact ApiImpl.memValid_simple vs hne hsz

/-- (open) **What a conf change does to a membership** (sealed; today `ccStepB ∘ ccV2Of`: the
change as `AsV2` makes it, applied by `confchange`'s `Changer`, within raft's bound on the tracked
ids): `none` where `ApplyConfChange` would fail. The laws below give the simple changes etcd's
server makes; nothing is said of joint configurations. -/
@[no_expose] def Membership.applyChange (o : ConfChangeIM) (m : Membership) : Option Membership :=
  ApiImpl.memApply o m

/-- A change keeps a membership valid. -/
theorem Membership.applyChange_valid (o : ConfChangeIM) (m m' : Membership) :
    m.Valid → Membership.applyChange o m = some m' → m'.Valid :=
  ApiImpl.memApply_valid o m m'

/-- A legacy change of the node `0` changes nothing (raft skips it): what etcd hands raft in place of
a change it refuses (`applyConfChange`'s `NodeID = 0`). -/
theorem Membership.applyChange_nodeZero (vs : GSet w64) (cm : ConfChangeM) :
    cm.nodeId = W64 0 → (Membership.simple vs).Valid →
    Membership.applyChange (.v1 cm) (Membership.simple vs) = some (Membership.simple vs) :=
  ApiImpl.memApply_nodeZero vs cm

/-- A legacy `AddNode` of a voter changes nothing (what the bootstrap entries do when a node of a new
dynamic cluster applies them again). -/
theorem Membership.applyChange_addVoter (vs : GSet w64) (cm : ConfChangeM) :
    cm.type = W32 0 → cm.nodeId ∈ vs → (Membership.simple vs).Valid →
    Membership.applyChange (.v1 cm) (Membership.simple vs) = some (Membership.simple vs) :=
  ApiImpl.memApply_addVoter vs cm

/-- A legacy `RemoveNode` of a voter, not the last, removes it. -/
theorem Membership.applyChange_removeVoter (vs : GSet w64) (cm : ConfChangeM) :
    cm.type = W32 1 → cm.nodeId ≠ W64 0 → cm.nodeId ∈ vs →
    (GMap.delete cm.nodeId vs : GSet w64) ≠ ∅ → (Membership.simple vs).Valid →
    Membership.applyChange (.v1 cm) (Membership.simple vs) =
      some (Membership.simple (GMap.delete cm.nodeId vs)) :=
  ApiImpl.memApply_removeVoter vs cm

/-- A legacy `RemoveNode` of a node that is not a voter changes nothing. -/
theorem Membership.applyChange_removeAbsent (vs : GSet w64) (cm : ConfChangeM) :
    cm.type = W32 1 → cm.nodeId ≠ W64 0 → cm.nodeId ∉ vs → (Membership.simple vs).Valid →
    Membership.applyChange (.v1 cm) (Membership.simple vs) = some (Membership.simple vs) :=
  ApiImpl.memApply_removeAbsent vs cm

/-! ### A node's configuration view (2026-10-29, U9: the dynamic cluster `isDynamicCluster` deleted) -/

/-- (open) **A node's configuration view** (exclusive, one per node; today `nodeCfg`): what
`node.ApplyConfChange.dynamicSpec` moves and `node.Advance.dynamicSpec` checks. Separate from the
`Ready` loop's token (`nodeDriver`): an application may apply the conf changes on another goroutine
than its `Ready` loop (etcd's server applies them on its apply goroutine, and hands the view back
before `Advance`). -/
@[no_expose] def nodeConfig (n : Loc) (γ : Cluster) (N : Namespace) (v : ConfigView) : IProp GF :=
  ApiImpl.nodeConfig n γ N v

/-- (open) **The committed log delivered to node `n` extends `l`** (persistent; today `dlvLb`): what
`node.ApplyConfChange.dynamicSpec` takes of the entry it applies. -/
@[no_expose] def deliveredLogLb (n : Loc) (γ : Cluster) (N : Namespace) (l : List LogEntry) :
    IProp GF := ApiImpl.deliveredLogLb n γ N l

instance deliveredLogLb_persistent (n : Loc) (γ : Cluster) (N : Namespace) (l : List LogEntry) :
    Persistent (deliveredLogLb (GF := GF) n γ N l) := by
  unfold deliveredLogLb; exact ApiImpl.deliveredLogLb_persistent n γ N l

/-- The `Ready` loop knows what it was delivered. -/
theorem nodeDriver_deliveredLogLb (n : Loc) (γ : Cluster) (N : Namespace) (st : NodeDriverState) :
    nodeDriver (GF := GF) n γ N st ⊢ nodeDriver n γ N st ∗ deliveredLogLb n γ N st.delivered := by
  unfold nodeDriver deliveredLogLb; exact ApiImpl.nodeDriver_deliveredLogLb_impl n γ N st

theorem deliveredLogLb_mono (n : Loc) (γ : Cluster) (N : Namespace) (l1 l2 : List LogEntry) :
    l1 <+: l2 → deliveredLogLb (GF := GF) n γ N l2 ⊢ deliveredLogLb n γ N l1 := by
  unfold deliveredLogLb; exact ApiImpl.deliveredLogLb_mono_impl n γ N l1 l2

/-- What was delivered is committed. -/
theorem deliveredLogLb_committed (n : Loc) (γ : Cluster) (N : Namespace) (l : List LogEntry) :
    deliveredLogLb (GF := GF) n γ N l ⊢ isCommittedLogLb γ l := by
  unfold deliveredLogLb isCommittedLogLb; exact ApiImpl.deliveredLogLb_committed_impl n γ N l

/-! ### A `Ready`'s hard state -/

/-- (open) **The log through index `c` was committed at term `t`** (persistent; today `commitWit`): a
leader of term `t` had committed the log through `c`. What the snapshot a server builds itself needs
(`sentMsg_replaceSnapshot`), and etcd's apply batches record (`toApply.raftTerm`). -/
@[no_expose] def committedAtTerm (γ : Cluster) (N : Namespace) (t c : w64) : IProp GF :=
  ApiImpl.committedAtTerm γ N t c

instance committedAtTerm_persistent (γ : Cluster) (N : Namespace) (t c : w64) :
    Persistent (committedAtTerm (GF := GF) γ N t c) := by
  unfold committedAtTerm; exact ApiImpl.committedAtTerm_persistent γ N t c

theorem committedAtTerm_committed (γ : Cluster) (N : Namespace) (t c : w64) :
    committedAtTerm (GF := GF) γ N t c ⊢
      ∃ l, isCommittedLogLb γ l ∗ ⌜l.length = uint.nat c⌝ := by
  unfold committedAtTerm isCommittedLogLb; exact ApiImpl.committedAtTerm_committed_impl γ N t c

/-! ### A snapshot the client builds (the snapshot track; open) -/

/-- (open) **A raft `MsgSnap` with the client's snapshot in place of raft's** (today
`isMessage_snap_recontent`, D22 S-b; etcd's server sends the merged snapshot, its backend's image
at its applied index, in place of the snapshot raft's `MsgSnap` names): sent, if the new snapshot
is certified, at an index committed at the message's term, past raft's, and its term the term of
the committed log's entry at its index (`l`, the committed log up to it). (2026-10-27: the
committed log `l` added; a certificate does not fix the snapshot's term, which a client may
register at any term, `storageCert_registerAny`, and raft's `MsgSnap` names the entry at its
index, `isMessage_snap_recontent`.) -/
theorem sentMsg_replaceSnapshot (γ : Cluster) (N : Namespace) (src : w64) (st : MsgSt)
    (sv sv' : SnapshotM) (c : w64) (l : List LogEntry) (E : CoPset) :
    ↑N ⊆ E → st.msg.Type' = MsgSnap → st.snap = some sv →
    uint.Z sv.Metadata'.Index' ≤ uint.Z sv'.Metadata'.Index' →
    uint.Z sv'.Metadata'.Index' ≤ uint.Z c →
    l.length = uint.nat sv'.Metadata'.Index' →
    l.getLast?.map LogEntry.term = some sv'.Metadata'.Term' →
    ⊢ sentMsg (GF := GF) γ N src st -∗ committedAtTerm γ N st.msg.Term' c -∗
      isCommittedLogLb γ l -∗ snapshotCert γ N (snapTrip sv' sv'.Metadata'.ConfState'.lists) ={E}=∗
      sentMsg γ N src { st with snap := some sv' } := by
  unfold sentMsg committedAtTerm isCommittedLogLb snapshotCert
  exact ApiImpl.sentMsg_replaceSnapshot_impl γ N src st sv sv' c l E

/-- **In a cluster allocated with `dup`, a `MsgProp`'s credits are persistent** (2026-10-29, S1):
what `Ready` returns with it, and what `stepIn_intro` takes; a network may step any number of copies
of it. Every other message's credits come from `msgCredits_none` and `msgCredits_snapshot`. -/
theorem msgCredits_copy (γ : Cluster) (N : Namespace) (st : MsgSt) :
    γ.dup = true → msgCredits (GF := GF) γ N st ⊢ □ msgCredits γ N st := by
  -- (raft-final, 2026-10-29: of any message, S1's F1; until then of a `MsgProp`, whose credits had
  -- no read credit)
  sorry

/-! ### The server port's additions (2026-10-27, branch `server-port`; proved the same day, branch
`raft-api`)

What porting etcd's server onto this API needed beyond the section above (`notes/decisions.md`,
"etcd's server on raft's node API"). -/

/-- **A committed log's next index fits raft's 64-bit indices** (2026-10-27, the server port's
addition): every committed entry's index is covered by a time receipt, so a committed log is shorter
than the receipts' bound past the bootstrap log, at most `2 ^ 61` in a cluster that `readyFits`.
What the server needs to number the requested entries of its own log (`SrvRaftLog.lean`,
`srvPropAu_api`) and to hand a committed log to its committed index (`E.C`). (Changed from the
draft: `readyFits` taken; the receipts' bound alone, `≤ 2 ^ 64 - 2` past a bootstrap log of up to
`2 ^ 61` entries, does not keep the next index within `2 ^ 64`.) -/
theorem isCommittedLogLb_length (γ : Cluster) (N : Namespace) (l : List LogEntry) :
    readyFits (GF := GF) γ N ∗ isCommittedLogLb γ l ⊢ ⌜(l.length : Int) + 1 < 2 ^ 64⌝ := by
  unfold readyFits Cluster.bootLen isCommittedLogLb ApiImpl.isCommittedLogLb
  iintro ⟨%Hf, (%Hnil | ⟨-, -, %Hb, -⟩)⟩
  · ipureintro; subst Hnil; simp
  · ipureintro; omega

/-- (2026-10-27, the server port's addition) **The read context `c` was committed after the log
`l0` was** (persistent): what `readCtx_commit_after` gives with the context. Raft's read index is
the leader's commit index once it has committed in its term, after the request: at least every
log committed before the context was (raft's `readReq` registered the committed log at the
deposit, and `readOk`'s index bounds it). -/
@[no_expose] def readCtxAfter (γ : Cluster) (N : Namespace) (c : List w8) (l0 : List LogEntry) :
    IProp GF := ApiImpl.readCtxAfter γ N c l0

instance readCtxAfter_persistent (γ : Cluster) (N : Namespace) (c : List w8) (l0 : List LogEntry) :
    Persistent (readCtxAfter (GF := GF) γ N c l0) := by
  unfold readCtxAfter; exact ApiImpl.readCtxAfter_persistent γ N c l0

omit [StorageModel GF] sem package_sem in
/-- (the server port's addition) **Committing a context after a committed log** `l0`:
`readCtx_commit`, and the context's lower bound. -/
theorem readCtx_commit_after (γ : Cluster) (N : Namespace) (U : GSet (List w8)) (c : List w8)
    (Q : List LogEntry → IProp GF) (l0 : List LogEntry) :
    c ∉ U →
    ownReadCtxs (GF := GF) γ U ∗ isCommittedLogLb γ l0 ∗
      □ AU <{ ∃∃ (ops : List LogEntry), ownCommittedOps γ ops }> @ ⊤ \ ↑N, ∅
           <{ ownCommittedOps γ ops, COMM □ Q ops }> ⊢
    |==> (ownReadCtxs γ (insert c U) ∗ isReadCtx γ N c Q ∗ readCtxAfter γ N c l0) := by
  intro Hc
  unfold ownReadCtxs isCommittedLogLb ownCommittedOps isReadCtx readCtxAfter
  exact ApiImpl.readCtx_commit_after_impl γ N U c Q l0 Hc

omit [StorageModel GF] sem package_sem in
/-- (the server port's addition) **A read state's index is past what was committed before its
context** (the read-index guarantee etcd's `LinearizableReadNotify` states in indices: the applied
index reaches the committed index the caller knew of). -/
theorem readStateOk_after (γ : Cluster) (N : Namespace) (c : List w8) (idx : w64)
    (l0 : List LogEntry) :
    readStateOk (GF := GF) γ N c idx ∗ readCtxAfter γ N c l0 ⊢ ⌜l0.length ≤ uint.nat idx⌝ := by
  unfold readStateOk readCtxAfter ApiImpl.readStateOk ApiImpl.readCtxAfter
  iintro ⟨⟨-, -, %γq, %l1, #Hel, %Hl1⟩, %γq', #Hel'⟩
  ihave %Hag := ghostMapElem_agree $$ Hel Hel'
  ipureintro
  simp only [Prod.mk.injEq] at Hag
  rw [← Hag.2]; exact Hl1

/-- (2026-10-27, the server port's addition) **Receiving a `Ready` as a channel's receive**, for a
`select` (etcd's `raftNode.start` receives it among a ticker's and a stop channel's): with the loop's
token at rest, the node's `Ready` channel is a channel of `Ready`s whose receive gives
`node.readyRecv.spec`'s postcondition (two later credits, as a handshake's receive). (Changed from
the draft: the token is taken before the channel's names, which are its node's.) -/
theorem isReadyChan_recvAu (n ch : Loc) (γ : Cluster) (N : Namespace) (id : w64)
    (st : NodeDriverState) (Φ : Ready → Bool → IProp GF) :
    st.handling = none →
    ⊢ isReadyChan (GF := GF) n γ N ch -∗ isNode n γ N id -∗ nodeDriver n γ N st -∗
      ∃ γc : ChanNames, isChan ch γc Ready ∗
        (£ 1 ∗ £ 1 -∗
          ▷ (∀ rd : Ready, (∃ (ce : List LogEntry) (es : List EntryM) (h : HardStateM)
              (L : Option SnapLoan),
              committedEntriesAt rd.CommittedEntries' st.delivered.length ce ∗
              isCommittedLogLb γ (st.delivered ++ ce) ∗
              (∃ rs, readStatesPts rd.ReadStates' rs ∗
                [∗list] s ∈ rs, readStateOk γ N s.RequestCtx' s.Index') ∗
              readyRest γ N id rd st ce es h L ∗
              nodeDriver n γ N (match L with
                | none => { st with
                    delivered := st.delivered ++ ce
                    hardState := phsNext st.hardState h
                    handling := some (es, none) }
                | some l => { st with
                    delivered := strip l.dlv
                    hardState := phsNext st.hardState h
                    handling := some (es, some l) })) -∗ Φ rd true) -∗
          recvAu γc Ready Φ) := by
  intro Hh
  unfold isReadyChan isNode nodeDriver
  iintro Hrc Hn Hdrv
  icases ApiImpl.isReadyChan_recvAu_impl n ch γ N id st Φ Hh $$ Hrc Hn Hdrv
    with ⟨%γc, #Hch, Hau⟩
  iexists γc
  iframe Hch
  iintro Hlc HΦ
  iapply Hau $$ Hlc
  inext
  iintro %rd ⟨%ce, %es, %h, %L, Hce, Hlb, Hrs, Hrest, Hdrv⟩
  iapply HΦ
  iexists ce, es, h, L
  unfold isCommittedLogLb readStateOk
  iframe Hce Hlb Hrs Hdrv
  iapply readyRest_of_impl $$ Hrest

end api

/-! ### Laws free of raft's instances (2026-10-27, the server port's addition; proved)

For a client whose own statements are free of `[StorageModel GF]` and raft's `Assumptions` (etcd's
server, whose committed-log predicates are used across hundreds of its modules). (The laws above
that do not use them omit them, `omit ... in`; until 2026-10-27 the server used primed copies of
them here.) -/

section lawsPure2
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- (2026-10-27, the server port's addition) **A `Ready`'s entries fit `MemoryStorage.Append`'s
bound** (`readyFits`). -/
theorem readyRest_fits [StorageModel GF] [go.Semantics] (γ : Cluster) (N : Namespace) (id : w64) (rd : Ready)
    (st : NodeDriverState) (ce : List LogEntry) (es : List EntryM) (h : HardStateM)
    (L : Option SnapLoan) :
    readyFits (GF := GF) γ N ∗ readyRest γ N id rd st ce es h L ⊢
      readyRest γ N id rd st ce es h L ∗
        ⌜∀ e0, es.head? = some e0 → uint.Z e0.Index' + (es.length : Int) ≤ 2 ^ 61⌝ := by
  unfold readyFits readyRest
  iintro ⟨%Hf, %ms, Hes, Hm, Hms, Hh, Hss, %Hx, Hsn⟩
  obtain ⟨Lx, H1, Hhd, H3, HLx⟩ := Hx
  isplitl
  · iexists ms
    iframe Hes Hm Hms Hh Hss Hsn
    ipureintro; exact ⟨Lx, H1, Hhd, H3, HLx⟩
  · ipureintro
    intro e0 he0
    have := Hhd e0 he0
    omega

/-- (2026-10-27, the server port's addition) **A sent `MsgSnap` carries a certified snapshot**
(raft's `msgCert`: a `MsgSnap`'s snapshot is one of its storage's, whose certificates are the
cluster's): with `snapshotCert_data`, a static cluster that vouches for no snapshot's data
(`snapOk` false) sends none. -/
theorem sentMsg_snapshot (γ : Cluster) (N : Namespace) (src : w64) (st : MsgSt) :
    st.msg.Type' = MsgSnap →
    sentMsg (GF := GF) γ N src st ⊢
      ∃ sv, ⌜st.snap = some sv⌝ ∗ snapshotCert γ N (snapTrip sv sv.Metadata'.ConfState'.lists) := by
  intro Hty
  unfold sentMsg snapshotCert
  exact ApiImpl.sentMsg_snapshot_impl γ N src st Hty

end lawsPure2

/-! ## Receiving a `Ready` (a law: `chan.receive` on the node's `Ready` channel) -/

section readyRecv
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **Receiving a `Ready`** (`for rd := range n.Ready()`): its committed entries are the committed
log's next entries `ce` (fillers included) after those delivered so far (`st.delivered`), field for
field (the index from the position), and the log is committed through them; with
`ownCommittedOps_lb_prefix`, their requested entries are the client's next committed ones. Each of
its read states is a `readStateOk` (`readStateOk_ctx`). The rest of the `Ready` (`readyRest`, open):
the entries `es` to persist, the messages, the hard state `h` and soft state, and the snapshot's
loan `L`, if any. The loop's new state, by whether the `Ready` carries a snapshot: without one, the
committed log delivered grows by `ce`; with one, it is the committed log up to the snapshot
(`strip l.dlv`); either way the hard state after `h` (`phsNext`), busy with `es` and the loan.
(2026-10-27: the new state stated, not an existential. For etcd's server: the node's `isNode` taken,
so that its messages are the node `id`'s, `readyRest`.) -/
theorem node.wp_readyRecv :
  ∀ (n ch : Loc) (γ : Cluster) (N : Namespace) (id : w64) (st : NodeDriverState),
  st.handling = none →
  {{ isReadyChan (GF := GF) n γ N ch ∗ isNode n γ N id ∗ nodeDriver n γ N st }}
    (App (Val (chan.receive Ready.ty)) (Val #ch))
  {{ (rd : Ready), RET (PairV #rd #true);
      ∃ (ce : List LogEntry) (es : List EntryM) (h : HardStateM) (L : Option SnapLoan),
        committedEntriesAt rd.CommittedEntries' st.delivered.length ce ∗
        isCommittedLogLb γ (st.delivered ++ ce) ∗
        (∃ rs, readStatesPts rd.ReadStates' rs ∗
          [∗list] s ∈ rs, readStateOk γ N s.RequestCtx' s.Index') ∗
        readyRest γ N id rd st ce es h L ∗
        nodeDriver n γ N (match L with
          | none => { st with
              delivered := st.delivered ++ ce
              hardState := phsNext st.hardState h
              handling := some (es, none) }
          | some l => { st with
              delivered := strip l.dlv
              hardState := phsNext st.hardState h
              handling := some (es, some l) }) }}
  := by
  intro n ch γ N id st Hh
  iintro %Φ Hpre HΦ
  unfold isReadyChan isNode nodeDriver
  iapply (ApiImpl.node.wp_readyRecv_impl n ch γ N id st Hh) $$ Hpre
  iintro !> %rd ⟨%ce, %es, %h, %L, Hce, Hlb, Hrs, Hrest, Hdrv⟩
  iapply HΦ
  iexists ce, es, h, L
  unfold isCommittedLogLb readStateOk
  iframe Hce Hlb Hrs Hdrv
  iapply readyRest_of_impl $$ Hrest

end readyRecv

end EtcdGrove
end Perennial
