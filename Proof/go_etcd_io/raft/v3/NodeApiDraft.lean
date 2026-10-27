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

DRAFT: the predicates' bodies and the laws' proofs are placeholders (`sorry`), to be defined and
proved in raft's proof (step 2); nothing imports this module. The statements are what to review.
Marked **(open)**: premises carried over unchanged from today's specs, for the items not yet
redesigned (the storage contract, the term budget, the static/dynamic modes, the rest of a `Ready`).
-/
module

public import Proof.go_etcd_io.raft.v3.InvNodeCtx
public import Perennial.Proof.context

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

/-- An entry of the committed log as a client sees it. Its index is its position (the `i`-th entry,
from 0, has index `i + 1`). -/
structure LogEntry where
  term : w64
  type : raftpb.EntryType
  data : List w8

/-- The Go record of the entry at index `idx`. -/
def LogEntry.toEntryM (idx : w64) (e : LogEntry) : EntryM := ⟨e.term, idx, e.type, e.data⟩

/-- **A filler**: an entry that carries nothing, an empty normal entry or an empty `ConfChangeV2`.
Raft appends these itself: a new leader's entry (`raft.go:961`), the entry leaving a joint
configuration (`AutoLeave`, `raft.go:742`), the entry in place of a conf change it refuses
(`raft.go:1341`). A client's empty proposal looks the same, so it is a filler too: an operation must
be encoded as non-empty bytes to take effect as one. -/
def LogEntry.isFiller (e : LogEntry) : Prop :=
  e.data = [] ∧ (e.type = W32 0 ∨ e.type = W32 2)

instance (e : LogEntry) : Decidable e.isFiller := by unfold LogEntry.isFiller; infer_instance

/-- **The requested entries** of a log: everything but its fillers. -/
def opsOf (l : List LogEntry) : List LogEntry := l.filter fun e => !decide e.isFiller

/-- A cluster's ghost names (opaque to clients). -/
@[no_expose] def Cluster : Type 1 := RaftNames

/-- **The committed requested entries, the client's** (exclusive): `opsOf` of the committed log.
Raft changes it only by firing an update the client gave it, when the requested entry commits;
fillers commit without changing it. -/
@[no_expose] def ownCommittedOps (γ : Cluster) (ops : List LogEntry) : IProp GF := sorry

/-- **A lower bound of the committed log**, fillers included (persistent): the committed log extends
`l`. -/
@[no_expose] def isCommittedLogLb (γ : Cluster) (l : List LogEntry) : IProp GF := sorry

instance ownCommittedOps_timeless (γ : Cluster) (ops : List LogEntry) :
    Timeless (ownCommittedOps (GF := GF) γ ops) := sorry
instance isCommittedLogLb_persistent (γ : Cluster) (l : List LogEntry) :
    Persistent (isCommittedLogLb (GF := GF) γ l) := sorry
instance isCommittedLogLb_timeless (γ : Cluster) (l : List LogEntry) :
    Timeless (isCommittedLogLb (GF := GF) γ l) := sorry

/-- The committed requested entries are those of a committed log. -/
theorem ownCommittedOps_get_lb (γ : Cluster) (ops : List LogEntry) :
    ownCommittedOps (GF := GF) γ ops ⊢ ∃ l, isCommittedLogLb γ l ∗ ⌜opsOf l = ops⌝ := sorry

/-- The requested entries of a committed log are a prefix of those committed now. -/
theorem ownCommittedOps_lb_prefix (γ : Cluster) (ops l : List LogEntry) :
    ownCommittedOps (GF := GF) γ ops ∗ isCommittedLogLb γ l ⊢ ⌜opsOf l <+: ops⌝ := sorry

theorem isCommittedLogLb_mono (γ : Cluster) (l1 l2 : List LogEntry) :
    l1 <+: l2 → isCommittedLogLb (GF := GF) γ l2 ⊢ isCommittedLogLb γ l1 := sorry

theorem isCommittedLogLb_agree (γ : Cluster) (l1 l2 : List LogEntry) :
    isCommittedLogLb (GF := GF) γ l1 ∗ isCommittedLogLb γ l2 ⊢ ⌜l1 <+: l2 ∨ l2 <+: l1⌝ := sorry

/-! ## The cluster and its nodes -/

/-! ## Read contexts -/

/-- **The read contexts, the client's** (exclusive): `U` is the finite set of the contexts committed
so far (`readCtx_commit`); any other context is unused and may be committed. A new cluster gives it
at `∅`. (The authority-over-used-keys pattern of a ghost map; a client whose readers run
concurrently shares it through its own invariant.) -/
@[no_expose] def ownReadCtxs (γ : Cluster) (U : GSet (List w8)) : IProp GF := sorry

/-- **The read context `c` is committed to `Q`** (persistent): every read with context `c` takes
effect at a moment when the committed requested entries are some `ops`, and gives `□ Q ops`
(`readStateOk_ctx`). A client may retry a read with the same context. -/
@[no_expose] def isReadCtx (γ : Cluster) (N : Namespace) (c : List w8)
    (Q : List LogEntry → IProp GF) : IProp GF := sorry

instance isReadCtx_persistent (γ : Cluster) (N : Namespace) (c : List w8)
    (Q : List LogEntry → IProp GF) : Persistent (isReadCtx (GF := GF) γ N c Q) := sorry

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
    |==> ownReadCtxs γ (insert c U) ∗ isReadCtx γ N c Q := sorry

/-- (open) **A read request's credit**: raft counts read requests in a 64-bit counter (today's
`rdCred`); carried over until the read path's bounds are redesigned. -/
@[no_expose] def readCredit (γ : Cluster) : IProp GF := sorry

/-- **A read state** (persistent): a `Ready`'s `ReadState{Index: idx, RequestCtx: c}`. -/
@[no_expose] def readStateOk (γ : Cluster) (N : Namespace) (c : List w8) (idx : w64) : IProp GF :=
  sorry

instance readStateOk_persistent (γ : Cluster) (N : Namespace) (c : List w8) (idx : w64) :
    Persistent (readStateOk (GF := GF) γ N c idx) := sorry

/-- **What a read state tells the client** of a context it committed: a read with context `c` took
effect when the committed log was `l`, of length `idx`, and gave `Q` of its requested entries. -/
theorem readStateOk_ctx (γ : Cluster) (N : Namespace) (c : List w8) (idx : w64)
    (Q : List LogEntry → IProp GF) :
    readStateOk (GF := GF) γ N c idx ∗ isReadCtx γ N c Q ⊢
    ∃ l, ⌜l.length = uint.nat idx⌝ ∗ isCommittedLogLb γ l ∗ ▷ □ Q (opsOf l) := sorry

/-- **A new cluster** of the peers `ps`, in the caller's namespace `N`: the client's committed
requested entries at the bootstrap entries (one `ConfChangeAddNode` per peer, at term 1: `BootLog`;
none is a filler), the read contexts with none used, and one boot
token per peer, for its `StartNode`. Replaces the allocation variants (`ownRaftGhost_alloc_*`,
`raft_dyn_alloc*`, `allocClient*`). -/
@[no_expose] def nodeBoot (γ : Cluster) (N : Namespace) (id : w64) : IProp GF := sorry

/-- The bootstrap log: a `ConfChangeAddNode` of each peer, its context `ctx`, at term 1, as
`MarshalConfChange` encodes it (`bs`). -/
def BootLog (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry) : Prop :=
  boot.length = ps.length ∧ (boot.length : Int) < 2 ^ 61 ∧
  ∀ (k : Nat) (e : LogEntry), boot[k]? = some e →
    ∃ id ctx, ps[k]? = some id ∧ ctxs[k]? = some ctx ∧ e.term = W64 1 ∧ e.type = W32 1 ∧
      -- `Bootstrap`'s `ConfChange{Type: ConfChangeAddNode, NodeID: id, Context: ctx}`
      MarshalsConfChange (some (.v1 ⟨W32 0, id, ctx, W64 0⟩)) e.data

theorem cluster_alloc (N : Namespace) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry) :
    BootLog ps ctxs boot → ps.Nodup →
    ⊢ |==> ∃ γ, ownCommittedOps (GF := GF) γ boot ∗ ownReadCtxs γ ∅ ∗
        [∗list] id ∈ ps, nodeBoot γ N id :=
  sorry

/- The node's predicates take the node `n` first (there is one per node, many per cluster), then
the cluster and namespace, and the state that changes as one record, so that a new field does not
change their arity. -/

/-- **A running node** `n` of id `id` in the cluster `γ` (persistent). -/
@[no_expose] def isNode (n : Loc) (γ : Cluster) (N : Namespace) (id : w64) : IProp GF := sorry

instance isNode_persistent (n : Loc) (γ : Cluster) (N : Namespace) (id : w64) :
    Persistent (isNode (GF := GF) n γ N id) := sorry

/-- The node's `Ready` channel `ch` (persistent). -/
@[no_expose] def isReadyChan (n : Loc) (γ : Cluster) (N : Namespace) (ch : Loc) : IProp GF := sorry

/-- The state of a node's `Ready` loop. -/
structure NodeDriverState where
  /-- the committed log delivered so far (fillers included) -/
  delivered : List LogEntry
  /-- the hard state last handed out -/
  hardState : HardStateM
  /-- while a `Ready` is being handled (between receiving it and `Advance`): its entries to persist -/
  handling : Option (List EntryM)

/-- The state a node's `Ready` loop starts in. -/
def NodeDriverState.init : NodeDriverState := ⟨[], hsZero, none⟩

/-- **The `Ready` loop's token** (exclusive): one per node, at the loop's state `st`. -/
@[no_expose] def nodeDriver (n : Loc) (γ : Cluster) (N : Namespace) (st : NodeDriverState) : IProp GF :=
  sorry

/-- (open) **The rest of a `Ready`** after its committed entries, from the loop's state `st` to `st'`:
the entries to persist, the hard state, the messages, the soft state (today's `readyData` without
its committed entries and read states); redesigned with the open items. -/
@[no_expose] def readyRest (n : Loc) (γ : Cluster) (N : Namespace) (rd : Ready) (st st' : NodeDriverState) :
    IProp GF := sorry

/-- The Go entries `sl` are the log entries `ce`, at the indices after `base` (read-only). -/
def committedEntriesAt (sl : GoSlice) (base : Nat) (ce : List LogEntry) : IProp GF :=
  entsRO sl (ce.mapIdx fun i e => e.toEntryM (W64 (base + i + 1)))

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
         <{ ∀∀ (t : w64) (bs : List w8), ⌜MarshalsConfChange (some o) bs⌝ →
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
its read states is a `readStateOk` (`readStateOk_ctx`). (open: the rest of the `Ready`, `readyRest`; and a `Ready`
carrying a snapshot, today's `readyDataL`.) -/
abbrev node.readyRecv.spec : Prop :=
  ∀ (n ch : Loc) (γ : Cluster) (N : Namespace) (st : NodeDriverState),
  st.handling = none →
  {{ isReadyChan (GF := GF) n γ N ch ∗ nodeDriver n γ N st }}
    (App (Val (chan.receive Ready.ty)) (Val #ch))
  {{ (rd : Ready), RET (PairV #rd #true);
      -- `es`, `hs'`: (open) the entries to persist and the hard state handed out, from the rest of
      -- the `Ready`
      ∃ (ce : List LogEntry) (es : List EntryM) (hs' : HardStateM),
        committedEntriesAt rd.CommittedEntries' st.delivered.length ce ∗
        isCommittedLogLb γ (st.delivered ++ ce) ∗
        (∃ rs, readStatesPts rd.ReadStates' rs ∗ [∗list] s ∈ rs, readStateOk γ N s.RequestCtx' s.Index') ∗
        readyRest n γ N rd st ⟨st.delivered ++ ce, hs', some es⟩ ∗
        nodeDriver n γ N ⟨st.delivered ++ ce, hs', some es⟩ }}

/-- **`StartNode(c, peers)`**: starts a node of the cluster `γ` from its boot token. The ghost
premises of today's spec (`bootInit`, `isCommitted γ bootLog`, `BootLogOk γ.reCCOk`, the
`RaftNames` fields) are replaced by `nodeBoot`; the Go-level premises are today's. (open: the
storage contract's premises `ownStorage`/`NsCap`/`certLink`, the term budget `budgetInv`/`termLB`,
the static/dynamic mode and `snapIn`, carried over unchanged.) -/
abbrev StartNode.spec : Prop :=
  ∀ (γ : Cluster) (N : Namespace) (c : Loc) (cv : Config) (lok si : GoInterfaceOk)
    (σ : StorState) (hs : HardStateM) (csm : ConfStateM) (R : IProp GF)
    (peers : GoSlice) (dq : DFrac) (pv : List Peer) (ps : List w64) (ctxs : List (List w8))
    (bud : BudgetNames),
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
      -- the node's boot token (in place of `bootInit`, `isCommitted γ bootLog`, `bootMarshal`)
      nodeBoot γ N cv.ID' ∗
      -- (open) the term budget
      inv budgetN (budgetInv bud) ∗ termLB bud (W64 1) }}
    (App (App (Val #(functions StartNode [])) (Val #c)) (Val #peers))
  {{ (nd : GoInterface), RET #nd;
      R ∗ ∃ (n : Loc), ⌜nd = interface.mkOk (go.GoType.PointerType node.ty) #n⌝ ∗
        isNode n γ N cv.ID' ∗ nodeDriver n γ N NodeDriverState.init }}

end spec

end Draft
end EtcdGrove
end Perennial
