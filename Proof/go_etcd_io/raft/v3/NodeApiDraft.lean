/-
# Raft's node API, redesigned: draft statements for review (2026-10-27)

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
`NodeApiImpl.lean` (namespace `ApiImpl`), every law and spec proved there, from raft's internals and
raft's linked specs (`node.wp_Propose`, ..., which a client's linking file links against): nothing
here is `sorry`.
Marked **(open)**: premises carried over unchanged from today's specs, for the items not yet
redesigned (the storage contract, the term budget, the static/dynamic modes, the rest of a `Ready`).

**What the key-value store needs (2026-10-27, `examples/kv` ported onto this draft):** the static
cluster (`isStaticCluster`, `cluster_alloc_static`, `RestartNode`), the rest of a `Ready`
(`readyRest`, `readySnap`), `Advance`, `Step` (`sentMsg`, `msgCredits`, `stepIn`), `Tick`
(`tickCredit`), `TransferLeadership` (`leaderTransferOn`) and the snapshots' certificates
(`snapshotCert`, `storageCertInv`, `storageCertLink`). The storage contract itself (`StorageModel`,
`isStorage`, `appendRight`, `readyOut`, `advReceipt`, `storFloor`) and `MemoryStorage`'s specs and
predicates are raft's storage API, carried over unchanged (not redesigned here).
-/
module

public import Proof.go_etcd_io.raft.v3.InvNodeCtx
public import Perennial.Proof.context
public import Proof.go_etcd_io.raft.v3.InvMemstorage
public import Proof.go_etcd_io.raft.v3.NodeApiVocab
-- (2026-10-27) the implementation (`NodeApiImpl.lean`) and raft's linked specs, not exported
import Proof.go_etcd_io.raft.v3.NodeApiImpl
import Proof.go_etcd_io.raft.v3.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Draft

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

/-- The committed requested entries are those of a committed log. (2026-10-27, for kv: the
client's resource kept, which a persistent conclusion alone does not give back.) -/
theorem ownCommittedOps_get_lb (γ : Cluster) (ops : List LogEntry) :
    ownCommittedOps (GF := GF) γ ops ⊢
      ownCommittedOps γ ops ∗ ∃ l, isCommittedLogLb γ l ∗ ⌜opsOf l = ops⌝ := by
  unfold ownCommittedOps isCommittedLogLb; exact ApiImpl.ownCommittedOps_get_lb_impl γ ops

/-- The requested entries of a committed log are a prefix of those committed now. -/
theorem ownCommittedOps_lb_prefix (γ : Cluster) (ops l : List LogEntry) :
    ownCommittedOps (GF := GF) γ ops ∗ isCommittedLogLb γ l ⊢ ⌜opsOf l <+: ops⌝ := by
  unfold ownCommittedOps isCommittedLogLb; exact ApiImpl.ownCommittedOps_lb_prefix_impl γ ops l

/-- Every committed log extends the empty one. -/
theorem isCommittedLogLb_nil (γ : Cluster) : ⊢ isCommittedLogLb (GF := GF) γ [] := by
  unfold isCommittedLogLb; exact ApiImpl.isCommittedLogLb_nil_impl γ

theorem isCommittedLogLb_mono (γ : Cluster) (l1 l2 : List LogEntry) :
    l1 <+: l2 → isCommittedLogLb (GF := GF) γ l2 ⊢ isCommittedLogLb γ l1 := by
  unfold isCommittedLogLb; exact ApiImpl.isCommittedLogLb_mono_impl γ l1 l2

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

/-- (open) **Read requests' credits**: raft counts read requests in a 64-bit counter (today's
`rdCred`); carried over until the read path's bounds are redesigned. A new cluster gives
`2 ^ 64 - 2` of them (`cluster_alloc`). -/
@[no_expose] def readCredits (γ : Cluster) (n : Nat) : IProp GF := ApiImpl.readCredits γ n

theorem readCredits_split (γ : Cluster) (a b : Nat) :
    readCredits (GF := GF) γ (a + b) ⊣⊢ readCredits γ a ∗ readCredits γ b := by
  unfold readCredits; exact ApiImpl.readCredits_split γ a b

/-- (open) **A read request's credit**: one of `readCredits`. -/
@[no_expose] def readCredit (γ : Cluster) : IProp GF := ApiImpl.readCredit γ

theorem readCredit_eq (γ : Cluster) : readCredit (GF := GF) γ ⊣⊢ readCredits γ 1 := by
  unfold readCredit readCredits ApiImpl.readCredit; exact .rfl

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

/-- **A read state's context was committed** (`readCtx_commit`): a read is requested only with a
committed context (`node.ReadIndex`). (2026-10-27, for kv: the applier tells its own reader's
context from another's by it.) -/
theorem readStateOk_used (γ : Cluster) (N : Namespace) (c : List w8) (idx : w64) (U : GSet (List w8)) :
    readStateOk (GF := GF) γ N c idx ∗ ownReadCtxs γ U ⊢ ⌜c ∈ U⌝ := by
  unfold readStateOk ownReadCtxs; exact ApiImpl.readStateOk_used_impl γ N c idx U

/-! ## A static cluster

A cluster whose voters are fixed: raft's static mode (no joint configuration ever exists). A client
may still propose conf changes (they commit as requested entries); it applies only those that keep
the voters (`node.ApplyConfChange`, `CCShrink`). It takes snapshots whose data the client vouches
for (`snapOk`, a relation of a committed log and the data, fixed at allocation), and has leader
transfer on. Both allocations make one: `cluster_alloc` (bootstrapped, for `StartNode`) and
`cluster_alloc_static` (empty, for `RestartNode`). -/

/-- **The cluster is static** (persistent): of the voters `vs` (non-empty, distinct, non-zero, at
most `2 ^ 62`), taking snapshots whose data `d` at index `i` satisfy `snapOk l d` of the committed
log `l` of length `i`. -/
@[no_expose] def isStaticCluster (γ : Cluster) (N : Namespace) (vs : List w64)
    (snapOk : List LogEntry → List w8 → Prop) : IProp GF :=
  ApiImpl.isStaticCluster γ N vs snapOk

instance isStaticCluster_persistent (γ : Cluster) (N : Namespace) (vs : List w64)
    (snapOk : List LogEntry → List w8 → Prop) :
    Persistent (isStaticCluster (GF := GF) γ N vs snapOk) := by
  unfold isStaticCluster; exact ApiImpl.isStaticCluster_persistent γ N vs snapOk

/-- **Leader transfer is on** in the cluster (persistent; today `RaftNames.reNoXfer = false`): what
`node.TransferLeadership` takes. -/
@[no_expose] def leaderTransferOn (γ : Cluster) (N : Namespace) : IProp GF :=
  ApiImpl.leaderTransferOn γ N

instance leaderTransferOn_persistent (γ : Cluster) (N : Namespace) :
    Persistent (leaderTransferOn (GF := GF) γ N) := by
  unfold leaderTransferOn; exact ApiImpl.leaderTransferOn_persistent γ N

/-- **A node's boot token** of a new cluster of the peers `ps` with the contexts `ctxs`, for node
`id`'s `StartNode` (exclusive). -/
@[no_expose] def nodeBoot (γ : Cluster) (N : Namespace) (ps : List w64) (ctxs : List (List w8))
    (id : w64) : IProp GF :=
  ApiImpl.nodeBoot γ N ps ctxs id

/-- **A new cluster** of the peers `ps`, in the caller's namespace `N`: the client's committed
requested entries at the bootstrap entries (one `ConfChangeAddNode` per peer, at term 1: `BootLog`;
none is a filler), the read contexts with none used, the cluster's read credits, the cluster static
(of the peers, taking snapshots whose data satisfy `snapOk`), leader transfer on, and one boot token
per peer, for its `StartNode`. The term budget, backed by time receipts (`receiptBound`), is the
cluster's. `bootMarshal` is what `StartNode` needs of `proto.Marshal` at the peers' conf changes.
Replaces the allocation variants (`ownRaftGhost_alloc_*`, `raft_dyn_alloc*`, `allocClient*`).
(2026-10-27: changed from the first draft: a fancy update at any mask, the receipts' bound, the
peers non-empty and non-zero, `bootMarshal`, the read credits; `nodeBoot` names the peers and their
contexts; the cluster takes snapshots, `snapOk`. A client that takes none chooses
`snapOk := fun _ _ => False`, and refutes a snapshot `Ready` by `snapshotCert_data`.) -/
theorem cluster_alloc (N : Namespace) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (snapOk : List LogEntry → List w8 → Prop) (E : CoPset) :
    receiptBound GF ≤ 2 ^ 64 - 2 →
    BootLog ps ctxs boot → ps.Nodup → ps ≠ [] → W64 0 ∉ ps →
    ⊢ bootMarshal (GF := GF) ps ctxs (LogEntry.toEntries boot 0) -∗
      |={E}=> ∃ γ, ownCommittedOps γ boot ∗ ownReadCtxs γ ∅ ∗ readCredits γ (2 ^ 64 - 2) ∗
        isStaticCluster γ N ps snapOk ∗ leaderTransferOn γ N ∗
        [∗list] id ∈ ps, nodeBoot γ N ps ctxs id := by
  intro Hrb HB Hnd Hne Hnz
  unfold ownCommittedOps ownReadCtxs readCredits nodeBoot isStaticCluster leaderTransferOn
  exact ApiImpl.cluster_alloc_impl N ps ctxs boot snapOk E Hrb HB Hnd Hne Hnz

/-- **A static cluster's boot token** for node `id` (exclusive): what its `RestartNode` takes. -/
@[no_expose] def nodeRestartBoot (γ : Cluster) (N : Namespace) (vs : List w64) (id : w64) : IProp GF :=
  ApiImpl.nodeRestartBoot γ N vs id

/-- **A new static cluster** of the voters `vs`, in the caller's namespace `N`: nothing committed
(the client's committed requested entries empty), the read contexts with none used, the cluster's
read credits, its parameters, and one boot token per voter. The term budget, backed by time
receipts (`receiptBound`), is the cluster's. Replaces `ownRaftGhost_alloc_snap` and
`budget_alloc`. (2026-10-27: the read credits added.) -/
theorem cluster_alloc_static (N : Namespace) (vs : List w64)
    (snapOk : List LogEntry → List w8 → Prop) (E : CoPset) :
    receiptBound GF ≤ 2 ^ 64 - 2 → vs ≠ [] → vs.Nodup → W64 0 ∉ vs → (vs.length : Int) ≤ 2 ^ 62 →
    ⊢ |={E}=> ∃ γ, ownCommittedOps (GF := GF) γ [] ∗ ownReadCtxs γ ∅ ∗ readCredits γ (2 ^ 64 - 2) ∗
        isStaticCluster γ N vs snapOk ∗ leaderTransferOn γ N ∗
        [∗list] id ∈ vs, nodeRestartBoot γ N vs id := by
  intro Hrb Hne Hnd Hnz Hlen
  unfold ownCommittedOps ownReadCtxs readCredits isStaticCluster leaderTransferOn nodeRestartBoot
  exact ApiImpl.cluster_alloc_static_impl N vs snapOk E Hrb Hne Hnd Hnz Hlen

/- The node's predicates take the node `n` first (there is one per node, many per cluster), then
the cluster and namespace, and the state that changes as one record, so that a new field does not
change their arity. -/

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

/-! ## Snapshots' certificates -/

/-- **The snapshot `k` is certified** for the cluster (persistent; today `raftSnapCertD`): its
configuration the cluster's at its index, its data what the client vouches for of the committed log
up to it. -/
@[no_expose] def snapshotCert (γ : Cluster) (N : Namespace) (k : SnapTrip) : IProp GF :=
  ApiImpl.snapshotCert γ N k

instance snapshotCert_persistent (γ : Cluster) (N : Namespace) (k : SnapTrip) :
    Persistent (snapshotCert (GF := GF) γ N k) := by
  unfold snapshotCert; exact ApiImpl.snapshotCert_persistent γ N k

/-- **What a certified snapshot's data is**, in a static cluster: `snapOk` of the committed log up
to its index. -/
theorem snapshotCert_data (γ : Cluster) (N : Namespace) (vs : List w64)
    (snapOk : List LogEntry → List w8 → Prop) (k : SnapTrip) :
    isStaticCluster (GF := GF) γ N vs snapOk ∗ snapshotCert γ N k ⊢
      ∃ l, isCommittedLogLb γ l ∗ ⌜l.length = uint.nat k.sid.index' ∧ snapOk l k.dat⌝ := by
  unfold isStaticCluster snapshotCert isCommittedLogLb
  exact ApiImpl.snapshotCert_data_impl γ N vs snapOk k

/-- **Certifying a snapshot** of a static cluster, at any term: its configuration the voters (no
learners, not joint, well formed: `SnapListsOk`), its data what the client vouches for of a
committed log as long as its index. -/
theorem snapshotCert_static (γ : Cluster) (N : Namespace) (vs : List w64)
    (snapOk : List LogEntry → List w8 → Prop) (l : List LogEntry) (i : w64) (d : List w8) :
    (∀ t : w64, SnapListsOk ⟨⟨t, i⟩, ⟨vs, [], [], []⟩, false, d⟩) →
    l.length = uint.nat i → snapOk l d →
    isStaticCluster (GF := GF) γ N vs snapOk ∗ isCommittedLogLb γ l ⊢
      □ ∀ t : w64, snapshotCert γ N ⟨⟨t, i⟩, ⟨vs, [], [], []⟩, false, d⟩ := by
  intro Hok Hl Hso
  unfold isStaticCluster snapshotCert isCommittedLogLb
  exact ApiImpl.snapshotCert_static_impl γ N vs snapOk l i d Hok Hl Hso

/-- **A `MemoryStorage`'s certificate registry tied to the cluster** (persistent; today
`memCertInv`): its entries are certified snapshots. The client allocates it from
`NewMemoryStorage`'s `memCertAuth`. -/
@[no_expose] def storageCertInv (γ : Cluster) (N : Namespace) (γs : MemStorNames) : IProp GF :=
  ApiImpl.storageCertInv γ N γs

instance storageCertInv_persistent (γ : Cluster) (N : Namespace) (γs : MemStorNames) :
    Persistent (storageCertInv (GF := GF) γ N γs) := by
  unfold storageCertInv; exact ApiImpl.storageCertInv_persistent γ N γs

theorem storageCertInv_alloc (γ : Cluster) (N : Namespace) (γs : MemStorNames) (E : CoPset) :
    ⊢ memCertAuth (GF := GF) γs ={E}=∗ storageCertInv γ N γs := by
  unfold storageCertInv; exact ApiImpl.storageCertInv_alloc_impl γ N γs E

/-- A registered snapshot is certified. -/
theorem storageCert_read (γ : Cluster) (N : Namespace) (γs : MemStorNames) (k : SnapTrip)
    (E : CoPset) :
    ↑N ⊆ E →
    ⊢ storageCertInv (GF := GF) γ N γs -∗ memStorCert γs k ={E}=∗ snapshotCert γ N k := by
  intro hE
  unfold storageCertInv snapshotCert; exact ApiImpl.storageCert_read_impl γ N γs k E hE

/-- A certified snapshot can be registered. -/
theorem storageCert_register (γ : Cluster) (N : Namespace) (γs : MemStorNames) (k : SnapTrip)
    (E : CoPset) :
    ↑N ⊆ E →
    ⊢ storageCertInv (GF := GF) γ N γs -∗ snapshotCert γ N k ={E}=∗ memStorCert γs k := by
  intro hE
  unfold storageCertInv snapshotCert; exact ApiImpl.storageCert_register_impl γ N γs k E hE

/-- ... at any term (what `MemoryStorage.CreateSnapshot` asks). -/
theorem storageCert_registerAny (γ : Cluster) (N : Namespace) (γs : MemStorNames) (i : w64)
    (cl : CSLists) (al : Bool) (d : List w8) (E : CoPset) :
    ↑N ⊆ E →
    ⊢ storageCertInv (GF := GF) γ N γs -∗ (□ ∀ t : w64, snapshotCert γ N ⟨⟨t, i⟩, cl, al, d⟩) ={E}=∗
      □ ∀ t : w64, memStorCert γs ⟨⟨t, i⟩, cl, al, d⟩ := by
  intro hE
  unfold storageCertInv snapshotCert
  exact ApiImpl.storageCert_registerAny_impl γ N γs i cl al d E hE

/-- **The storage's certificates are the cluster's** (persistent; today `certLink`, `storCertOk`):
what `StartNode` and `RestartNode` take of their storage. -/
@[no_expose] def storageCertLink (γ : Cluster) (N : Namespace) (st : Storage) : IProp GF :=
  ApiImpl.storageCertLink γ N st

instance storageCertLink_persistent (γ : Cluster) (N : Namespace) (st : Storage) :
    Persistent (storageCertLink (GF := GF) γ N st) := by
  unfold storageCertLink; exact ApiImpl.storageCertLink_persistent γ N st

theorem storageCertLink_intro (γ : Cluster) (N : Namespace) (st : Storage) :
    (□ ∀ (k : SnapTrip) (E : CoPset), ⌜↑N ⊆ E⌝ -∗ storCert st k ={E}=∗
        snapshotCert (GF := GF) γ N k) ∗
      (□ ∀ (k : SnapTrip) (E : CoPset), ⌜↑N ⊆ E⌝ -∗ snapshotCert γ N k ={E}=∗ storCert st k) ⊢
      storageCertLink γ N st := by
  unfold storageCertLink snapshotCert; exact ApiImpl.storageCertLink_intro_impl γ N st

/-! ## Messages and the term budget (open: carried over) -/

/-- (open) **A message a `Ready` handed out** (persistent; today `isRaftMsg` and `termLB`): sent by
a node of the cluster, legitimately, of a term within the cluster's budget. -/
@[no_expose] def sentMsg (γ : Cluster) (N : Namespace) (st : MsgSt) : IProp GF :=
  ApiImpl.sentMsg γ N st

instance sentMsg_persistent (γ : Cluster) (N : Namespace) (st : MsgSt) :
    Persistent (sentMsg (GF := GF) γ N st) := by
  unfold sentMsg; exact ApiImpl.sentMsg_persistent γ N st

/-- (open) **What a sent message carries for its receiver's `Step`** (today `rdCred`, one for a
`MsgReadIndex`, and `stTks`, a forwarded proposal's tickets). -/
@[no_expose] def msgCredits (γ : Cluster) (N : Namespace) (st : MsgSt) : IProp GF :=
  ApiImpl.msgCredits γ N st

/-- (open) **Tick credits** (today `tickCred`: time receipts): one per `Tick`, and one per
`MsgTimeoutNow` stepped. -/
@[no_expose] def tickCredit (γ : Cluster) (n : Nat) : IProp GF := ApiImpl.tickCredit γ n

theorem tickCredit_intro (γ : Cluster) (n : Nat) : ⧗ n ⊢ tickCredit (GF := GF) γ n := by
  unfold tickCredit; exact ApiImpl.tickCredit_intro_impl γ n

theorem tickCredit_zero (γ : Cluster) : ⊢ |==> tickCredit (GF := GF) γ 0 := by
  unfold tickCredit; exact ApiImpl.tickCredit_zero_impl γ

/-- (open) **A message `node.Step` takes** at the node `id` (today `stepP`): the message at `ml`. -/
@[no_expose] def stepIn (γ : Cluster) (N : Namespace) (id : w64) (ml : Loc) : IProp GF :=
  ApiImpl.stepIn γ N id ml

/-- (open) **Stepping a sent message**: a copy of it (its fields, entries and snapshot; no local
responses), owned with its entries slice fresh, addressed to `id`, with its credits and, for a
`MsgTimeoutNow`, a tick credit: a forwarded proposal with no context, or what a node steps from the
network (`NetMsgOk`, no pre-vote, no leader transfer; a snapshot below `2^61`). (Today kv's
`stepP_deliverable`.) -/
theorem stepIn_intro (γ : Cluster) (N : Namespace) (id : w64) (ml : Loc) (st : MsgSt) :
    (st.msg.Type' = MsgProp → st.ctx = []) →
    (st.msg.Type' ≠ MsgProp → NetMsgOk id ⟨st.msg, st.ents, st.snap, st.ctx, []⟩ ∧
      st.msg.Type' ≠ MsgPreVote ∧ st.msg.Type' ≠ MsgTransferLeader) →
    (st.msg.Type' = MsgSnap → ∃ sv, st.snap = some sv ∧ uint.Z sv.Metadata'.Index' < 2 ^ 61) →
    st.msg.To' = id →
    sentMsg (GF := GF) γ N st ∗
      msgPtsC ml (DFrac.own 1) (DFrac.own 1) true ⟨st.msg, st.ents, st.snap, st.ctx, []⟩ ∗
      msgCredits γ N st ∗ tickCredit γ (if st.msg.Type' = MsgTimeoutNow then 1 else 0) ⊢
    |==> stepIn γ N id ml := by
  intro H1 H2 H3 H4
  unfold sentMsg msgCredits tickCredit stepIn
  exact ApiImpl.stepIn_intro_impl γ N id ml st H1 H2 H3 H4

/-! ## The rest of a `Ready` -/

/-- (open) A `Ready`'s storage part, by its snapshot's loan: none -- the right to append the entries
`es` -- or a snapshot (its loan `l`, `ce` empty): the committed log up to it (`strip l.dlv`, its
entries at their positions), past what was delivered, half of the snapshot, its certificate, and the
storage itself (`readyOut`). (Today `readyDataL`'s snapshot part.) -/
def readySnap (γ : Cluster) (N : Namespace) (rd : Ready) (st : NodeDriverState)
    (ce : List LogEntry) (es : List EntryM) : Option SnapLoan → IProp GF
  | none => iprop(⌜rd.Snapshot' = null⌝ ∗ appendRight st.storage es)
  | some l => iprop(
      ⌜l.dlv = LogEntry.toEntries (strip l.dlv) 0 ∧ l.ptr = rd.Snapshot' ∧ ce = [] ∧
        st.delivered <+: strip l.dlv ∧ st.delivered.length < l.dlv.length ∧
        l.dlv.length = uint.nat l.snap.Metadata'.Index' ∧ 0 < uint.Z l.snap.Metadata'.Index' ∧
        uint.Z l.snap.Metadata'.Index' < 2 ^ 61 ∧ uint.Z l.fl ≤ uint.Z l.snap.Metadata'.Index' ∧
        LogIndicesOk (snapId l.snap) es⌝ ∗
      ownSnapS l.ptr (DFrac.own (1 : Qp).half) l.snap ∗ isCommittedLogLb γ (strip l.dlv) ∗
      snapshotCert γ N (snapTrip l.snap l.snap.Metadata'.ConfState'.lists) ∗
      readyOut st.storage es (some l))

/-- (open) **The rest of a `Ready`** after its committed entries `ce` and read states, at the loop's
state `st` (today's `readyDataL` without them; the storage's part in the storage contract's
vocabulary, `appendRight`, `readyOut`): the entries `es` to persist, the messages (each owned as
`Ready` hands it out, `readyDq`, sent, with its credits), the hard state `h` (`nil` or not:
`hsOpt`) and the soft state, the indices' bound, and the storage's part (`readySnap`, by the
snapshot's loan `L`). -/
def readyRest (γ : Cluster) (N : Namespace) (rd : Ready) (st : NodeDriverState)
    (ce : List LogEntry) (es : List EntryM) (h : HardStateM) (L : Option SnapLoan) : IProp GF :=
  iprop(∃ ms : List QMsg,
    entsRO rd.Entries' es ∗
    rd.Messages' ↦* ms.map QMsg.loc ∗
    ([∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st ∗ sentMsg γ N q.st ∗ msgCredits γ N q.st) ∗
    hsOpt rd.HardState' h ∗ softStateRO rd.SoftState' ∗
    ⌜∃ Lx : Int, Lx < 2 ^ 64 ∧
      (∀ e0, es.head? = some e0 → uint.Z e0.Index' + (es.length : Int) ≤ Lx + 1) ∧
      ((st.delivered ++ ce).length : Int) ≤ Lx⌝ ∗
    readySnap γ N rd st ce es L)

/-- The implementation's rest of a `Ready` is the draft's. -/
private theorem readyRest_of_impl (γ : Cluster) (N : Namespace) (rd : Ready) (st : NodeDriverState)
    (ce : List LogEntry) (es : List EntryM) (h : HardStateM) (L : Option SnapLoan) :
    ApiImpl.readyRest (GF := GF) γ N rd st ce es h L ⊢ readyRest γ N rd st ce es h L := by
  cases L <;> exact .rfl

end api

/-! ## The specs -/

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **`node.Propose(ctx, data)`**: hands raft the update appending `data`'s entry to the committed
requested entries, raft choosing its term; it fires at most once, when an entry of this proposal
commits, on whichever node commits it, and never for `data = []` (the entry is a filler, `isFiller`).
The error is `nil` (run took the proposal; it may still be lost), `ErrStopped`, `ErrProposalDropped`
(raft refused it; it was not appended) or the context's. -/
abbrev node.Propose.spec : Prop :=
  ∀ (n : Loc) (γ : Cluster) (N : Namespace) (id : w64) (data_sl : GoSlice) (data : List w8)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ N id ∗ nodeCtx ctx cd ∗
      data_sl ↦*□ data ∗
      AU <{ ∃∃ (ops : List LogEntry), ownCommittedOps γ ops }> @ ⊤ \ ↑N, ∅
         <{ ∀∀ (t : w64), ownCommittedOps γ (ops ++ [⟨t, W32 0, data⟩]), COMM True }> }}
    (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Propose"))
      (Val #(interface.ok ctx))) (Val #data_sl))
  {{ (err : GoInterface), RET #err;
      ⌜err = interface.nil⌝ ∨ errStopped err ∨ errProposalDropped err ∨ ctxErr cd err }}

/-- **`node.ProposeConfChange(ctx, cc)`**: the same, for the conf change `o` that `cc` holds (given
back): its entry has the type and bytes `MarshalConfChange` gives it, raft choosing the term. The
update never fires if the leader refuses the change (an empty normal entry commits in its place,
`raft.go:1341`) or if its entry is a filler (an empty `ConfChangeV2`). -/
abbrev node.ProposeConfChange.spec : Prop :=
  ∀ (n : Loc) (γ : Cluster) (N : Namespace) (id : w64) (c : GoInterface) (o : ConfChangeIM) (dq : DFrac)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ N id ∗ nodeCtx ctx cd ∗
      ownConfChangeI c dq (some o) ∗
      AU <{ ∃∃ (ops : List LogEntry), ownCommittedOps γ ops }> @ ⊤ \ ↑N, ∅
         <{ ∀∀ (t : w64) (bs : List w8), ⌜MarshalsConfChange (some o) bs⌝ ∗
              ownCommittedOps γ (ops ++ [⟨t, confChangeEntryType (some o), bs⟩]),
            COMM True }> }}
    (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"ProposeConfChange"))
      (Val #(interface.ok ctx))) (Val #c))
  {{ (err : GoInterface), RET #err; ownConfChangeI c dq (some o) ∗ nodeErr cd err }}

/-- **`node.ReadIndex(ctx, rctx)`**: requests a read with the context `c` (the bytes of `rctx`),
committed to `Q` beforehand (`readCtx_commit`); a `Ready`'s `ReadState` with context `c` then says
what it gave (`readStateOk_ctx`). The context may be retried. (open: `readCredit`.) -/
abbrev node.ReadIndex.spec : Prop :=
  ∀ (n : Loc) (γ : Cluster) (N : Namespace) (id : w64) (rctx : GoSlice) (c : List w8)
    (Q : List LogEntry → IProp GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ N id ∗ nodeCtx ctx cd ∗
      rctx ↦*□ c ∗ isReadCtx γ N c Q ∗ readCredit γ }}
    (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"ReadIndex"))
      (Val #(interface.ok ctx))) (Val #rctx))
  {{ (err : GoInterface), RET #err; nodeErr cd err }}

/-- **`node.Ready()`**: the node's `Ready` channel. -/
abbrev node.Ready.spec : Prop :=
  ∀ (γ : Cluster) (N : Namespace) (id : w64) (n : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ N id }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Ready")) (Val #()))
  {{ (ch : Loc), RET #ch; isReadyChan n γ N ch }}

/-- **Receiving a `Ready`** (`for rd := range n.Ready()`): its committed entries are the committed
log's next entries `ce` (fillers included) after those delivered so far (`st.delivered`), field for
field (the index from the position), and the log is committed through them; with
`ownCommittedOps_lb_prefix`, their requested entries are the client's next committed ones. Each of
its read states is a `readStateOk` (`readStateOk_ctx`). The rest of the `Ready` (`readyRest`, open):
the entries `es` to persist, the messages, the hard state `h` and soft state, and the snapshot's
loan `L`, if any. The loop's new state, by whether the `Ready` carries a snapshot: without one, the
committed log delivered grows by `ce`; with one, it is the committed log up to the snapshot
(`strip l.dlv`); either way the hard state after `h` (`phsNext`), busy with `es` and the loan.
(2026-10-27: the new state stated, not an existential.) -/
abbrev node.readyRecv.spec : Prop :=
  ∀ (n ch : Loc) (γ : Cluster) (N : Namespace) (st : NodeDriverState),
  st.handling = none →
  {{ isReadyChan (GF := GF) n γ N ch ∗ nodeDriver n γ N st }}
    (App (Val (chan.receive Ready.ty)) (Val #ch))
  {{ (rd : Ready), RET (PairV #rd #true);
      ∃ (ce : List LogEntry) (es : List EntryM) (h : HardStateM) (L : Option SnapLoan),
        committedEntriesAt rd.CommittedEntries' st.delivered.length ce ∗
        isCommittedLogLb γ (st.delivered ++ ce) ∗
        (∃ rs, readStatesPts rd.ReadStates' rs ∗
          [∗list] s ∈ rs, readStateOk γ N s.RequestCtx' s.Index') ∗
        readyRest γ N rd st ce es h L ∗
        nodeDriver n γ N (match L with
          | none => { st with
              delivered := st.delivered ++ ce
              hardState := phsNext st.hardState h
              handling := some (es, none) }
          | some l => { st with
              delivered := strip l.dlv
              hardState := phsNext st.hardState h
              handling := some (es, some l) }) }}

/-- (open) **`node.Advance()`**: the driver, done with a `Ready` (its entries `es` appended, or its
snapshot installed: the storage contract's receipt, `advReceipt`), hands it back; the loop is idle
again. After a `Ready` without a snapshot, the storage's floor is at least the committed log
delivered (`storFloor`, today `reqWit`). (2026-10-27: the premise that no conf-change entry was
delivered is gone: the nodes are in raft's static mode, which needs none -- a conf change the client
applies keeps the voters, `node.ApplyConfChange`.) -/
abbrev node.Advance.spec : Prop :=
  ∀ (n : Loc) (γ : Cluster) (N : Namespace) (st : NodeDriverState) (es : List EntryM)
    (L : Option SnapLoan),
  st.handling = some (es, L) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ nodeDriver n γ N st ∗
      advReceipt st.storage es L }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Advance")) (Val #()))
  {{ RET #(); nodeDriver n γ N { st with handling := none } ∗
      match L with
      | none => ∃ x : w64, storFloor st.storage x ∗ ⌜(st.delivered.length : Int) ≤ uint.Z x⌝
      | some _ => True }}

/-- (open) **`node.Step(ctx, m)`**: a message from the network (`stepIn`), from any goroutine. -/
abbrev node.Step.spec : Prop :=
  ∀ (n : Loc) (γ : Cluster) (N : Namespace) (id : w64) (ml : Loc)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ N id ∗ nodeCtx ctx cd ∗
      stepIn γ N id ml }}
    (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Step"))
      (Val #(interface.ok ctx))) (Val #ml))
  {{ (err : GoInterface), RET #err; nodeErr cd err }}

/-- (open) **`node.Tick()`**: a tick, for one tick credit, from any goroutine. -/
abbrev node.Tick.spec : Prop :=
  ∀ (n : Loc) (γ : Cluster) (N : Namespace) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ N id ∗ tickCredit γ 1 }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Tick")) (Val #()))
  {{ RET #(); True }}

/-- **`node.TransferLeadership(ctx, lead, transferee)`**, in a cluster with leader transfer on;
nothing is promised of the transfer. -/
abbrev node.TransferLeadership.spec : Prop :=
  ∀ (n : Loc) (γ : Cluster) (N : Namespace) (id : w64) (lead transferee : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ N id ∗ nodeCtx ctx cd ∗
      leaderTransferOn γ N }}
    (App (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"TransferLeadership"))
      (Val #(interface.ok ctx))) (Val #lead)) (Val #transferee))
  {{ RET #(); True }}

/-- **`RestartNode(c)`**: starts node `cv.ID'` of a static cluster of voters `vs`
(`cluster_alloc_static`) from its boot token, on a fresh storage whose `InitialState` gives the
voters' conf state, and whose certificates are the cluster's (`storageCertLink`). Today's premises,
with the ghost ones (`rnInit`, `isCommitted γ []`, the term budget, `certLink`, the mode and
`snapIn`) replaced by `nodeRestartBoot` and `storageCertLink`. -/
abbrev RestartNode.spec : Prop :=
  ∀ (γ : Cluster) (N : Namespace) (vs : List w64) (c : Loc) (cv : Config) (lok si : GoInterfaceOk)
    (σ : StorState) (hs : HardStateM) (csm : ConfStateM),
  -- `NewRawNode`'s premises (unchanged)
  ConfigValid cv →
  cv.Logger' = interface.ok lok →
  cv.Storage' = interface.ok si →
  sint.Z cv.MaxInflightMsgs' < 2 ^ 62 →
  cv.DisableProposalForwarding' = false →
  cv.ReadOnlyOption' = W64 0 →
  cv.DisableConfChangeValidation' = false →
  (cv.MaxCommittedSizePerReady' ≠ W64 0 ∨ cv.MaxSizePerMsg' ≠ W64 0) →
  cv.AsyncStorageWrites' = false →
  cv.Applied' = W64 0 →
  -- an empty storage, the voters' conf state (unchanged)
  σ.prev = entryID.mk (W64 0) (W64 0) → σ.ents = [] → (uint.Z σ.ss.index' = 0 ∨ σ.ss = σ.prev) →
  σ.pend = [] → HsEmpty hs →
  csm.Voters' = vs → csm.VotersOutgoing' = [] → csm.Learners' = [] → csm.LearnersNext' = [] →
  csm.AutoLeave' = false →
  cv.ID' ∈ vs →
  σ.fl = W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗ isLogger lok ∗
      isStorage (interface.ok si) ∗ ownStorage (interface.ok si) σ ∗
      □ (∀ (Φ : val → IProp GF) (ss' : entryID), ownStorage (interface.ok si) { σ with ss := ss' } -∗
           (∀ (hp cs : Loc) (al : Bool), ownStorage (interface.ok si) { σ with ss := ss' } -∗
            hsOpt hp hs -∗ csPts cs DFrac.discard csm al -∗
            Φ (PairV (PairV #hp #cs) #interface.nil)) -∗
           WP (App (Val #(methods si.ty go!"InitialState" si.v)) (Val #())) {{ Φ }}) ∗
      nodeRestartBoot γ N vs cv.ID' ∗ storageCertLink γ N (interface.ok si) }}
    (App (Val #(functions RestartNode [])) (Val #c))
  {{ (nd : GoInterface), RET #nd;
      ∃ (n : Loc), ⌜nd = interface.mkOk (go.GoType.PointerType node.ty) #n⌝ ∗
        isNode n γ N cv.ID' ∗ nodeDriver n γ N (NodeDriverState.init (interface.ok si)) }}

/-- **`StartNode(c, peers)`**: starts node `cv.ID'` of the cluster `γ` from its boot token
(`cluster_alloc`), of the peers `ps` with the contexts `ctxs`. The Go-level premises are today's.
(2026-10-27: the term budget is the cluster's, in the boot token; the storage's certificates are
the cluster's, `storageCertLink`: the cluster takes snapshots.) -/
abbrev StartNode.spec : Prop :=
  ∀ (γ : Cluster) (N : Namespace) (c : Loc) (cv : Config) (lok si : GoInterfaceOk)
    (σ : StorState) (hs : HardStateM) (csm : ConfStateM) (R : IProp GF)
    (peers : GoSlice) (dq : DFrac) (pv : List Peer) (ps : List w64) (ctxs : List (List w8)),
  -- `NewRawNode`'s premises (unchanged)
  ConfigValid cv →
  cv.Logger' = interface.ok lok →
  cv.Storage' = interface.ok si →
  sint.Z cv.MaxInflightMsgs' < 2 ^ 62 →
  cv.DisableProposalForwarding' = false →
  cv.ReadOnlyOption' = W64 0 →
  cv.DisableConfChangeValidation' = false →
  (cv.MaxCommittedSizePerReady' ≠ W64 0 ∨ cv.MaxSizePerMsg' ≠ W64 0) →
  cv.AsyncStorageWrites' = false →
  cv.Applied' = W64 0 →
  -- an empty storage and conf state (unchanged)
  σ.prev = entryID.mk (W64 0) (W64 0) → σ.ents = [] → (uint.Z σ.ss.index' = 0 ∨ σ.ss = σ.prev) →
  σ.pend = [] → HsEmpty hs →
  csm.Voters' = [] → csm.VotersOutgoing' = [] → csm.Learners' = [] → csm.LearnersNext' = [] →
  csm.AutoLeave' = false →
  -- the peers (unchanged)
  ps = pv.map Peer.ID' → ps ≠ [] → ps.Nodup → W64 0 ∉ ps → (ps.length : Int) ≤ 2 ^ 62 →
  cv.ID' ∈ ps →
  σ.fl = W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗ isLogger lok ∗
      isStorage (interface.ok si) ∗ ownStorage (interface.ok si) σ ∗
      (∀ (Φ : val → IProp GF) (ss' : entryID), ownStorage (interface.ok si) { σ with ss := ss' } -∗
           (∀ (hp cs : Loc) (al : Bool), ownStorage (interface.ok si) { σ with ss := ss' } -∗
            R -∗ hsOpt hp hs -∗ csPts cs DFrac.discard csm al -∗
            Φ (PairV (PairV #hp #cs) #interface.nil)) -∗
           WP (App (Val #(methods si.ty go!"InitialState" si.v)) (Val #())) {{ Φ }}) ∗
      peers ↦*{dq} pv ∗ peersCtx pv ctxs ∗
      -- the node's boot token (in place of `bootInit`, `isCommitted γ bootLog`, `bootMarshal`,
      -- the term budget)
      nodeBoot γ N ps ctxs cv.ID' ∗
      -- (2026-10-27) the storage's certificates are the cluster's (until then: never compacted past
      -- index `1`, `storCap`, raft's no-snapshot mode)
      storageCertLink γ N (interface.ok si) }}
    (App (App (Val #(functions StartNode [])) (Val #c)) (Val #peers))
  {{ (nd : GoInterface), RET #nd;
      R ∗ ∃ (n : Loc), ⌜nd = interface.mkOk (go.GoType.PointerType node.ty) #n⌝ ∗
        isNode n γ N cv.ID' ∗ nodeDriver n γ N (NodeDriverState.init (interface.ok si)) }}

/-- **`node.ApplyConfChange(cc)`** in a static cluster of the voters `vs`, from any goroutine: a
change that keeps the voters and drops only learners (`CCShrink`: e.g. a `ConfChange` with
`NodeId = 0`, or a `RemoveNode` of a learner), which the client states of a change it requested
(its committed requested entries say which). The answer is a fresh `ConfState`: the voters, no
learner among them, not joint. (2026-10-27: raft's static case, `node__ApplyConfChange.lean`.) -/
abbrev node.ApplyConfChange.spec : Prop :=
  ∀ (n : Loc) (γ : Cluster) (N : Namespace) (id : w64) (vs : List w64)
    (snapOk : List LogEntry → List w8 → Prop) (c : GoInterface) (o : ConfChangeIM),
  CCShrink (GMap.listToSet vs) (ccV2Of o).1 (ccV2Of o).2 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ N id ∗
      isStaticCluster γ N vs snapOk ∗ ownConfChangeI c DFrac.discard (some o) }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"ApplyConfChange")) (Val #c))
  {{ (csp : Loc) (cs : ConfStateM), RET #csp; csPts csp (DFrac.own 1) cs true ∗
      ⌜cs.Voters' ≡ₚ vs ∧ (∀ k ∈ cs.Learners', k ∉ vs) ∧ cs.VotersOutgoing' = [] ∧
        cs.LearnersNext' = [] ∧ cs.AutoLeave' = false⌝ }}

end spec

/-! ## The specs' placeholders (until raft's proof proves them: `sorry`)

What a client's linking file links its proofs against. -/

section links
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem node.wp_Propose : node.Propose.spec (GF := GF) (hG := hG) := by
  exact ApiImpl.node.wp_Propose_impl _root_.Perennial.EtcdGrove.node.wp_Propose
theorem node.wp_ProposeConfChange : node.ProposeConfChange.spec (GF := GF) (hG := hG) := by
  exact ApiImpl.node.wp_ProposeConfChange_impl _root_.Perennial.EtcdGrove.node.wp_ProposeConfChange
theorem node.wp_ReadIndex : node.ReadIndex.spec (GF := GF) (hG := hG) := by
  exact ApiImpl.node.wp_ReadIndex_impl
    (_root_.Perennial.EtcdGrove.node.ReadIndex.wp_proofReq
      _root_.Perennial.EtcdGrove.node.wp_step
      _root_.Perennial.EtcdGrove.raftpb.MessageType.wp_Enum)
theorem node.wp_Ready : node.Ready.spec (GF := GF) (hG := hG) := by
  exact ApiImpl.node.wp_Ready_impl
theorem node.wp_readyRecv : node.readyRecv.spec (GF := GF) (hG := hG) := by
  intro n ch γ N st Hh
  iintro %Φ Hpre HΦ
  unfold isReadyChan nodeDriver
  iapply (ApiImpl.node.wp_readyRecv_impl n ch γ N st Hh) $$ Hpre
  iintro !> %rd ⟨%ce, %es, %h, %L, Hce, Hlb, Hrs, Hrest, Hdrv⟩
  iapply HΦ
  iexists ce, es, h, L
  unfold isCommittedLogLb readStateOk
  iframe Hce Hlb Hrs Hdrv
  iapply readyRest_of_impl $$ Hrest
theorem node.wp_Advance : node.Advance.spec (GF := GF) (hG := hG) := by
  exact ApiImpl.node.wp_Advance_impl _root_.Perennial.EtcdGrove.node.wp_Advance
theorem node.wp_Step : node.Step.spec (GF := GF) (hG := hG) := by
  exact ApiImpl.node.wp_Step_impl _root_.Perennial.EtcdGrove.node.wp_Step
theorem node.wp_Tick : node.Tick.spec (GF := GF) (hG := hG) := by
  exact ApiImpl.node.wp_Tick_impl _root_.Perennial.EtcdGrove.node.wp_Tick
theorem node.wp_TransferLeadership : node.TransferLeadership.spec (GF := GF) (hG := hG) := by
  exact ApiImpl.node.wp_TransferLeadership_impl
    _root_.Perennial.EtcdGrove.node.wp_TransferLeadership
theorem wp_StartNode : StartNode.spec (GF := GF) (hG := hG) := by
  exact ApiImpl.wp_StartNode_impl _root_.Perennial.EtcdGrove.wp_StartNode
theorem wp_RestartNode : RestartNode.spec (GF := GF) (hG := hG) := by
  exact ApiImpl.wp_RestartNode_impl _root_.Perennial.EtcdGrove.wp_RestartNode
theorem node.wp_ApplyConfChange : node.ApplyConfChange.spec (GF := GF) (hG := hG) := by
  exact ApiImpl.node.wp_ApplyConfChange_impl _root_.Perennial.EtcdGrove.node.wp_ApplyConfChange

end links

end Draft
end EtcdGrove
end Perennial
