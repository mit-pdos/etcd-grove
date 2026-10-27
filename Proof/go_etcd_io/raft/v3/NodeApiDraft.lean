/-
# Raft's node API, redesigned: draft statements for review (2026-10-27)

The statements decided with the user on 2026-10-27 (`notes/decisions.md`, "Raft's node API over an
abstract log"; memory "spec state principles"):

- **The abstract state** is the committed log as a client sees it: a list of `Ent` (term, type,
  data). The index is the position (not stored); the term is raft's choice (stored, since `Ready`
  shows it).
- **`ownCommitted γ L`** (exclusive, the client's) and **`isCommittedLb γ l`** (persistent, a lower
  bound): an authority and a fragment of one log, related by plain laws (no invariant, no mask).
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
structure Ent where
  term : w64
  type : raftpb.EntryType
  data : List w8

/-- The Go record of the entry at index `idx`. -/
def Ent.toM (idx : w64) (e : Ent) : EntryM := ⟨e.term, idx, e.type, e.data⟩

/-- A cluster's ghost names (opaque to clients). -/
@[no_expose] def Cluster : Type 1 := RaftNames

/-- **The committed log, the client's share** (exclusive). Raft changes it only by firing an update
the client gave it. -/
@[no_expose] def ownCommitted (γ : Cluster) (L : List Ent) : IProp GF := sorry

/-- **A lower bound of the committed log** (persistent): the committed log extends `l`. -/
@[no_expose] def isCommittedLb (γ : Cluster) (l : List Ent) : IProp GF := sorry

instance ownCommitted_timeless (γ : Cluster) (L : List Ent) :
    Timeless (ownCommitted (GF := GF) γ L) := sorry
instance isCommittedLb_persistent (γ : Cluster) (l : List Ent) :
    Persistent (isCommittedLb (GF := GF) γ l) := sorry
instance isCommittedLb_timeless (γ : Cluster) (l : List Ent) :
    Timeless (isCommittedLb (GF := GF) γ l) := sorry

theorem ownCommitted_get_lb (γ : Cluster) (L : List Ent) :
    ownCommitted (GF := GF) γ L ⊢ isCommittedLb γ L := sorry

theorem ownCommitted_lb_prefix (γ : Cluster) (L l : List Ent) :
    ownCommitted (GF := GF) γ L ∗ isCommittedLb γ l ⊢ ⌜l <+: L⌝ := sorry

theorem isCommittedLb_mono (γ : Cluster) (l1 l2 : List Ent) :
    l1 <+: l2 → isCommittedLb (GF := GF) γ l2 ⊢ isCommittedLb γ l1 := sorry

theorem isCommittedLb_agree (γ : Cluster) (l1 l2 : List Ent) :
    isCommittedLb (GF := GF) γ l1 ∗ isCommittedLb γ l2 ⊢ ⌜l1 <+: l2 ∨ l2 <+: l1⌝ := sorry

/-! ## The client's updates -/

/-- **Raft's own entries**, which no client proposes: the empty entry a new leader appends
(`raft.go:961`), the empty `ConfChangeV2` a leader appends to leave a joint configuration
(`AutoLeave`, `raft.go:742`), and the empty entry a leader puts in place of a conf change it refuses
(`raft.go:1341`). The client authorizes them once, for the cluster. -/
def ownEntsAu (γ : Cluster) (N : Namespace) : IProp GF :=
  iprop(□ AU <{ ∃∃ (L : List Ent), ownCommitted γ L }> @ ⊤ \ ↑N, ∅
              <{ ∀∀ (t : w64) (ty : raftpb.EntryType),
                   ⌜ty = W32 0 ∨ ty = W32 2⌝ → ownCommitted γ (L ++ [⟨t, ty, []⟩]),
                 COMM True }>)

/-- The update a proposal of `data` hands in: its entry appended, raft choosing the term. -/
def proposeAu (γ : Cluster) (N : Namespace) (data : List w8) : IProp GF :=
  iprop(AU <{ ∃∃ (L : List Ent), ownCommitted γ L }> @ ⊤ \ ↑N, ∅
           <{ ∀∀ (t : w64), ownCommitted γ (L ++ [⟨t, W32 0, data⟩]), COMM True }>)

/-- The update a proposal of the conf change `o` hands in: its entry appended (the type and bytes
`MarshalConfChange` gives it, raft choosing the term), or, if the leader refuses the change, an
empty normal entry in its place (`raft.go:1341`). -/
def proposeConfAu (γ : Cluster) (N : Namespace) (o : CCMsg) : IProp GF :=
  iprop(AU <{ ∃∃ (L : List Ent), ownCommitted γ L }> @ ⊤ \ ↑N, ∅
           <{ ∀∀ (t : w64) (bs : List w8) (refused : Bool),
                ⌜CCData (some o) bs⌝ →
                ownCommitted γ (L ++ [if refused then ⟨t, W32 0, []⟩ else ⟨t, ccEntryType (some o), bs⟩]),
              COMM True }>)

/-! ## The cluster and its nodes -/

/-- **A new cluster** of the peers `ps`, in the caller's namespace `N`: the client's committed log
at the bootstrap entries (one `ConfChangeAddNode` per peer, at term 1: `bootEnts`), and one boot
token per peer, for its `StartNode`. Replaces the allocation variants (`ownRaftGhost_alloc_*`,
`raft_dyn_alloc*`, `allocClient*`). -/
@[no_expose] def nodeBoot (γ : Cluster) (N : Namespace) (id : w64) : IProp GF := sorry

/-- The bootstrap log: a `ConfChangeAddNode` of each peer, its context `ctx`, at term 1, as
`MarshalConfChange` encodes it (`bs`). -/
def BootEnts (ps : List w64) (ctxs : List (List w8)) (boot : List Ent) : Prop :=
  boot.length = ps.length ∧ (boot.length : Int) < 2 ^ 61 ∧
  ∀ (k : Nat) (e : Ent), boot[k]? = some e →
    ∃ id ctx, ps[k]? = some id ∧ ctxs[k]? = some ctx ∧ e.term = W64 1 ∧ e.type = W32 1 ∧
      -- `Bootstrap`'s `ConfChange{Type: ConfChangeAddNode, NodeID: id, Context: ctx}`
      CCData (some (.v1 ⟨W32 0, id, ctx, W64 0⟩)) e.data

theorem cluster_alloc (N : Namespace) (ps : List w64) (ctxs : List (List w8)) (boot : List Ent) :
    BootEnts ps ctxs boot → ps.Nodup →
    ⊢ |==> ∃ γ, ownCommitted (GF := GF) γ boot ∗ [∗list] id ∈ ps, nodeBoot γ N id :=
  sorry

/-- **A running node** `n` of id `id` in the cluster `γ` (persistent). -/
@[no_expose] def isNode (γ : Cluster) (N : Namespace) (id : w64) (n : Loc) : IProp GF := sorry

instance isNode_persistent (γ : Cluster) (N : Namespace) (id : w64) (n : Loc) :
    Persistent (isNode (GF := GF) γ N id n) := sorry

/-- The node's `Ready` channel (persistent). -/
@[no_expose] def isReadyChan (γ : Cluster) (N : Namespace) (n ch : Loc) : IProp GF := sorry

/-- **The `Ready` loop's token**: the committed log delivered so far `D`, and the hard state last
handed out `p` (exclusive). -/
@[no_expose] def nodeDriver (γ : Cluster) (N : Namespace) (n : Loc) (D : List Ent)
    (p : HardStateM) : IProp GF := sorry

/-- The token while a `Ready` is being handled: delivered `D`, the entries to persist `es`. -/
@[no_expose] def nodeDriverBusy (γ : Cluster) (N : Namespace) (n : Loc) (D : List Ent)
    (es : List EntryM) (p : HardStateM) : IProp GF := sorry

/-- (open) **The rest of a `Ready`** after its committed entries: the entries to persist, the hard
state, the messages, the read states, the soft state (today's `readyData` without its first two
conjuncts); redesigned with the open items. -/
@[no_expose] def readyRest (γ : Cluster) (N : Namespace) (rd : Ready) (D ce : List Ent)
    (es : List EntryM) (p p' : HardStateM) : IProp GF := sorry

/-- The Go entries `sl` are the log entries `ce`, at the indices after `base` (read-only). -/
def committedEntsRO (sl : GoSlice) (base : Nat) (ce : List Ent) : IProp GF :=
  entsRO sl (ce.mapIdx fun i e => e.toM (W64 (base + i + 1)))

end api

/-! ## The specs -/

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **`node.Propose(ctx, data)`**: hands raft the update appending `data`; it fires at most once,
when an entry of this proposal commits, on whichever node commits it. The error is `nil` (run took
the proposal; it may still be lost), `ErrStopped`, `ErrProposalDropped` (raft refused it; it was not
appended) or the context's. -/
abbrev node.Propose.spec : Prop :=
  ∀ (γ : Cluster) (N : Namespace) (id : w64) (n : Loc) (data_sl : GoSlice) (data : List w8)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode γ N id n ∗ nodeCtx ctx cd ∗
      data_sl ↦*□ data ∗ proposeAu γ N data }}
    (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Propose"))
      (Val #(interface.ok ctx))) (Val #data_sl))
  {{ (err : GoInterface), RET #err;
      ⌜err = interface.nil⌝ ∨ errStopped err ∨ errProposalDropped err ∨ ctxErr cd err }}

/-- **`node.ProposeConfChange(ctx, cc)`**: the same, for the conf change `cc` holds; it is given
back. -/
abbrev node.ProposeConfChange.spec : Prop :=
  ∀ (γ : Cluster) (N : Namespace) (id : w64) (n : Loc) (c : GoInterface) (o : CCMsg) (dq : DFrac)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode γ N id n ∗ nodeCtx ctx cd ∗
      ownCCI c dq (some o) ∗ proposeConfAu γ N o }}
    (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"ProposeConfChange"))
      (Val #(interface.ok ctx))) (Val #c))
  {{ (err : GoInterface), RET #err; ownCCI c dq (some o) ∗ nodeErr cd err }}

/-- **`node.Ready()`**: the node's `Ready` channel. -/
abbrev node.Ready.spec : Prop :=
  ∀ (γ : Cluster) (N : Namespace) (id : w64) (n : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode γ N id n }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Ready")) (Val #()))
  {{ (ch : Loc), RET #ch; isReadyChan γ N n ch }}

/-- **Receiving a `Ready`** (`for rd := range n.Ready()`): its committed entries are the log's next
entries `ce` after those delivered so far `D`, field for field (the index from the position), and
the log is committed through them. (open: the rest of the `Ready`, `readyRest`; and a `Ready`
carrying a snapshot, today's `readyDataL`.) -/
abbrev node.readyRecv.spec : Prop :=
  ∀ (γ : Cluster) (N : Namespace) (n ch : Loc) (D : List Ent) (p : HardStateM),
  {{ isReadyChan (GF := GF) γ N n ch ∗ nodeDriver γ N n D p }}
    (App (Val (chan.receive Ready.ty)) (Val #ch))
  {{ (rd : Ready), RET (PairV #rd #true);
      ∃ (ce : List Ent) (es : List EntryM) (p' : HardStateM),
        committedEntsRO rd.CommittedEntries' D.length ce ∗ isCommittedLb γ (D ++ ce) ∗
        readyRest γ N rd D ce es p p' ∗ nodeDriverBusy γ N n (D ++ ce) es p' }}

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
      -- the node's boot token (in place of `bootInit`, `isCommitted γ bootLog`, `bootMarshal`), and the
      -- client's update for raft's own entries (any node may become leader and append one)
      nodeBoot γ N cv.ID' ∗ ownEntsAu γ N ∗
      -- (open) the term budget
      inv budgetN (budgetInv bud) ∗ termLB bud (W64 1) }}
    (App (App (Val #(functions StartNode [])) (Val #c)) (Val #peers))
  {{ (nd : GoInterface), RET #nd;
      R ∗ ∃ (n : Loc), ⌜nd = interface.mkOk (go.GoType.PointerType node.ty) #n⌝ ∗
        isNode γ N cv.ID' n ∗ nodeDriver γ N n [] hsZero }}

end spec

end Draft
end EtcdGrove
end Perennial
