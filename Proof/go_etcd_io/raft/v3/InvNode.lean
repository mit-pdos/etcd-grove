/-
Lean-first (no Rocq counterpart).

# `node.go`: the concurrent `Node` over a `RawNode` (2026-10-10)

`node.run` is one goroutine that owns the `RawNode`; clients talk to it over channels:
`propc` (a proposal and, for `Propose`, a buffered result channel), `recvc` (a message from
the network), `tickc` (buffered, a tick dropped when full), `readyc` (the next `Ready`),
`advancec` (the application's "done with that `Ready`"), and `done`, `stop`, `status`,
`confc` (shutdown, status and reconfiguration: out of scope, never used).

## The ghost state

- **The term budget** (`BudgetNames`, one per cluster): `RawNode.Tick` needs `term + 1 <
  2^64`, and `RawNode.Step` moves a node's term to at most a message's. The invariant
  `isBudget` holds a monotone bound `M` (`monoNatAuthOwn`) and the number `c` of tick
  credits handed out (`● c`, additive), with `M + c < 2^64 - 1`. A tick credit
  (`tickCred bud 1`, `◯ 1`) is what `Node.Tick` spends (`budget_spend`): it raises `M` by
  at most one past a term. Every node's term is at most `M` (`termLB`, a lower bound on
  `M`, persistent), and so is every message's term a `Ready` hands out (`readyData`): a
  receiver's `Step` keeps its term under `M` too. The application creates the budget once
  (`budget_alloc`), with as many credits as it will ever tick.
- **The `Ready`/`Advance` hand-shake** between `run` and the single *driver* (the
  application's loop over `Node.Ready()`): `dlv` (halves: `run`'s and the driver's) is the
  committed log handed out so far, `rof` (halves: `run` keeps one) records the last
  `Ready`'s `(delivered, committed entries, entries)`. A `Ready` carries `run`'s `dlv` half
  and the other `rof` half (`readyP`): the driver, holding both `dlv` halves, learns that
  the `Ready`'s committed entries come right after what it applied, and moves `dlv` on
  (`node_ready_receive`). `Advance` carries a `dlv` half back with the `rof` half and the
  receipt of the storage append (`advanceP`): `run` recognizes its own record (`rof`) and so
  the receipt is for the entries it handed out.
- **The channels**: Perennial's `Handshake` idiom for the unbuffered ones (the payload `P`
  from the sender, nothing back), with `P := False` for the channels nobody sends on; the
  tick channel's own invariant (`tickInv`: one credit per buffered tick); a proposal's
  result channel is a `Handoff` (`Proof/go_etcd_io/etcd/cache/v3/Handoff.lean`).

`isNode γ id n` (persistent) is the node struct (read-only), the raft struct's two shared
fields (`raftOwn`, `rawNodeOwn`: `Tick`'s warning reads them), the channels' invariants and
the budget. `nodeDriver γ n ds` is the driver's token.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRawnodeReady
public import Spec.go_etcd_io.raft.v3.RawNode__Step
public import Spec.go_etcd_io.raft.v3.RawNode__Propose
public import Perennial.Golang.Theory.Chan.Idioms.Handshake
public import Proof.go_etcd_io.etcd.cache.v3.Handoff
public import Perennial.Ghost.MonoNat
public import Proof.go_etcd_io.raft.v3.Protocol.Facts

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI OFE CMRA Iris.ProofMode go_etcd_io.raft.v3

/-! ## Countability of the channels' element types -/

section countable
variable [FfiSyntax]

instance hardState_countable : Pos.Countable raftpb.HardState :=
  countableOfLeftInverse (fun h : raftpb.HardState => (h.Term', h.Vote', h.Commit'))
    (fun p => ⟨p.1, p.2.1, p.2.2⟩) (fun _ => rfl)

instance confState_countable : Pos.Countable raftpb.ConfState :=
  countableOfLeftInverse
    (fun c : raftpb.ConfState => (c.Voters', c.Learners', c.VotersOutgoing', c.LearnersNext',
      c.AutoLeave'))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩) (fun _ => rfl)

instance snapshotMetadata_countable : Pos.Countable raftpb.SnapshotMetadata :=
  countableOfLeftInverse (fun m : raftpb.SnapshotMetadata => (m.ConfState', m.Index', m.Term'))
    (fun p => ⟨p.1, p.2.1, p.2.2⟩) (fun _ => rfl)

instance snapshot_countable : Pos.Countable raftpb.Snapshot :=
  countableOfLeftInverse (fun s : raftpb.Snapshot => (s.Data', s.Metadata'))
    (fun p => ⟨p.1, p.2⟩) (fun _ => rfl)

instance message_countable : Pos.Countable raftpb.Message :=
  countableOfLeftInverse
    (fun m : raftpb.Message => (m.Type', m.To', m.From', m.Term', m.LogTerm', m.Index',
      m.Entries', m.Commit', m.Vote', m.Snapshot', m.Reject', m.RejectHint', m.Context',
      m.Responses'))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2⟩)
    (fun _ => rfl)

instance msgWithResult_countable : Pos.Countable msgWithResult :=
  countableOfLeftInverse (fun m : msgWithResult => (m.m', m.result'))
    (fun p => ⟨p.1, p.2⟩) (fun _ => rfl)

instance ready_countable : Pos.Countable Ready :=
  countableOfLeftInverse
    (fun r : Ready => (r.SoftState', r.HardState', r.ReadStates', r.Entries', r.Snapshot',
      r.CommittedEntries', r.Messages', r.MustSync'))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2⟩) (fun _ => rfl)

instance confChangeV2_countable : Pos.Countable raftpb.ConfChangeV2 :=
  countableOfLeftInverse (fun c : raftpb.ConfChangeV2 => (c.Transition', c.Changes', c.Context'))
    (fun p => ⟨p.1, p.2.1, p.2.2⟩) (fun _ => rfl)

end countable

/-! ## The term budget -/

/-- Ghost names of a cluster's term budget. -/
structure BudgetNames where
  /-- the bound `M` on every term (a monotone nat) -/
  bound : GName
  /-- the tick credits handed out (`Auth Nat`, additive) -/
  creds : GName

def budgetN : Namespace := nroot.@"raft_budget"


section budget
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- See the file header. -/
def budgetInv (bud : BudgetNames) : IProp GF :=
  iprop(∃ (M c : Nat), monoNatAuthOwn bud.bound 1 M ∗ own bud.creds (● c : Auth Nat) ∗
    ⌜M + c < 2 ^ 64 - 1⌝)

/-- `n` tick credits: `Node.Tick` spends one. -/
def tickCred (bud : BudgetNames) (n : Nat) : IProp GF :=
  own bud.creds (◯ n : Auth Nat)

/-- The budget's bound is at least `t` (persistent): every node's term, every message's. -/
def termLB (bud : BudgetNames) (t : w64) : IProp GF :=
  monoNatLbOwn bud.bound (uint.nat t)

instance termLB_persistent (bud : BudgetNames) (t : w64) :
    Persistent (termLB (GF := GF) bud t) := by
  unfold termLB; infer_instance

instance budgetInv_timeless (bud : BudgetNames) : Timeless (budgetInv (GF := GF) bud) := by
  unfold budgetInv; infer_instance

theorem tickCred_split (bud : BudgetNames) (a b : Nat) :
    tickCred (GF := GF) bud (a + b) ⊣⊢ tickCred bud a ∗ tickCred bud b := by
  unfold tickCred
  rw [show (◯ (a + b) : Auth Nat) = (◯ a) • (◯ b) from Auth.frag_op]
  exact own_op bud.creds _ _

theorem tickCred_zero (bud : BudgetNames) : ⊢ |==> tickCred (GF := GF) bud 0 := by
  unfold tickCred
  exact own_unit bud.creds

theorem termLB_le (bud : BudgetNames) (t t' : w64) (h : uint.Z t' ≤ uint.Z t) :
    ⊢ termLB (GF := GF) bud t -∗ termLB bud t' := by
  unfold termLB
  iapply monoNatLbOwn_le
  have := uint_nat_eq t
  have := uint_nat_eq t'
  omega

/-- The budget, created once per cluster, with `N` credits. -/
theorem budget_alloc (N : Nat) (HN : N < 2 ^ 64 - 1) (E : CoPset) :
    ⊢ |={E}=> ∃ bud : BudgetNames, inv budgetN (budgetInv (GF := GF) bud) ∗ tickCred bud N ∗
      termLB bud (W64 0) := by
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γM, HM, #HMlb⟩
  imod own_alloc ((● N : Auth Nat) • ◯ N)
    (Auth.auth_both_valid_discrete.mpr ⟨⟨0, (Nat.add_zero N).symm⟩, trivial⟩) with ⟨%γC, HC⟩
  icases (own_op γC _ _).1 $$ HC with ⟨HCa, HCf⟩
  imod inv_alloc budgetN E (budgetInv (GF := GF) ⟨γM, γC⟩) $$ [HM HCa] with #Hinv
  · inext
    unfold budgetInv
    iexists 0, N
    iframe HM HCa
    ipureintro; omega
  imodintro
  iexists ⟨γM, γC⟩
  iframe Hinv
  unfold tickCred termLB
  iframe HCf
  iExactEq HMlb
  rfl

/-- Term `0` is within the budget (2026-10-13: a local read-index request's). -/
theorem termLB_zero (bud : BudgetNames) : ⊢ |==> termLB (GF := GF) bud (W64 0) := by
  unfold termLB
  exact monoNatLbOwn_0 bud.bound

/-- A term at most the budget's bound is not the last one. -/
theorem termLB_bound (bud : BudgetNames) (t : w64) (E : CoPset) (HE : ↑budgetN ⊆ E) :
    ⊢ inv budgetN (budgetInv (GF := GF) bud) -∗ termLB bud t ={E}=∗ ⌜uint.Z t < 2 ^ 64 - 1⌝ := by
  iintro #Hinv #Hlb
  iinv Hinv with >Hi Hclose
  unfold budgetInv
  icases Hi with ⟨%M, %c, HM, HC, %Hb⟩
  unfold termLB
  ihave %Hle := monoNatLbOwn_valid bud.bound 1 M (uint.nat t) $$ HM Hlb
  imod Hclose $$ [HM HC] with -
  · inext; iexists M, c; iframe HM HC; ipureintro; exact Hb
  imodintro
  ipureintro
  have := uint_nat_eq t
  omega

/-- Spending a tick credit: the bound covers one term more (`Node.Tick`'s). -/
theorem budget_spend (bud : BudgetNames) (t : w64) (E : CoPset) (HE : ↑budgetN ⊆ E) :
    ⊢ inv budgetN (budgetInv (GF := GF) bud) -∗ tickCred bud 1 -∗ termLB bud t ={E}=∗
      ⌜uint.Z t + 1 < 2 ^ 64 - 1⌝ ∗ termLB bud (t + W64 1) := by
  iintro #Hinv Hcr #Hlb
  iinv Hinv with >Hi Hclose
  unfold budgetInv
  icases Hi with ⟨%M, %c, HM, HC, %Hb⟩
  unfold termLB tickCred
  ihave %Hle := monoNatLbOwn_valid bud.bound 1 M (uint.nat t) $$ HM Hlb
  icombine HC Hcr gives %Hv
  have Hc1 : 1 ≤ c := by
    obtain ⟨z, hz⟩ := (Auth.auth_both_valid_discrete.mp Hv).1
    have : c = 1 + z := hz
    omega
  icombine HC Hcr as HCC
  imod own_update bud.creds _ ((● (c - 1) : Auth Nat) • ◯ (0 : Nat))
    (Auth.auth_update (CommMonoidLike.leftCancelAdd_local_update (by show c + 0 = (c - 1) + 1; omega)))
    $$ HCC with HCC
  icases (own_op bud.creds _ _).1 $$ HCC with ⟨HC, -⟩
  have := uint_nat_eq t
  have Hnw : uint.Z t + 1 < 2 ^ 64 - 1 := by omega
  imod mono_nat_own_update (max M (uint.nat (t + W64 1))) (Nat.le_max_left _ _) $$ HM
    with ⟨HM, #HMlb⟩
  imod Hclose $$ [HM HC] with -
  · inext
    iexists max M (uint.nat (t + W64 1)), c - 1
    iframe HM HC
    ipureintro
    have : uint.Z (t + W64 1) = uint.Z t + 1 := by word
    have := uint_nat_eq (t + W64 1)
    omega
  imodintro
  isplitr
  · ipureintro; exact Hnw
  iapply monoNatLbOwn_le $$ HMlb
  exact Nat.le_max_right _ _

end budget

/-! ## The node's ghost names and channel payloads -/

/-- Ghost names (and the storage) of one node. -/
structure NodeNames [FfiSyntax] where
  raft : RaftNames
  bud : BudgetNames
  /-- the node's `Storage` (`RNState.storage`), for the append right and its receipt -/
  stor : Storage
  propc : ChanNames
  recvc : ChanNames
  confc : ChanNames
  readyc : ChanNames
  advancec : ChanNames
  tick : ChanNames
  done : ChanNames
  stop : ChanNames
  status : ChanNames
  /-- the committed log handed out so far: `run`'s half and the driver's -/
  dlv : GName
  /-- `run`'s record of its last `Ready` `(delivered, committed entries, entries)` -/
  rof : GName

def tickN : Namespace := nroot.@"raft_tick"

/-- The proposed slices' invariant (2026-10-10). -/
def propDataN : Namespace := nroot.@"raft_propdata"

section node
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The message `Propose` builds: `pb.Message{Type: MsgProp, Entries: esl}`. -/
def propMsg (esl : GoSlice) : raftpb.Message :=
  { (zero_val raftpb.Message) with Type' := MsgProp, Entries' := esl }

/-- The proposed slices (2026-10-10): every slice recorded in the cluster's map `reSl`
(`isPropData`) holds its data, read-only. The application allocates it once per cluster,
with the raft ghost state (`propDataInv_alloc`). -/
def propDataInv (γ : RaftNames) : IProp GF :=
  iprop(∃ S : GMap GoSlice (List w8), ghostMapAuth γ.reSl 1 S ∗
    [∗map] sl ↦ d ∈ S, sl ↦*□ d ∗ sl ↪[γ.reSl]□ d)

instance propDataInv_timeless (γ : RaftNames) : Timeless (propDataInv (GF := GF) γ) := by
  unfold propDataInv; infer_instance

/-- A proposal forwarded by a peer (2026-10-10), as `Node.Step` takes it: its batch owned
(`appendEntry` stamps it; a transport delivers a copy), its context, and what it carries
as a protocol message (each entry's data, `entData`, so its update was deposited). -/
def fwdP (γ : NodeNames) (m : raftpb.Message) : IProp GF :=
  iprop(⌜m.Type' = MsgProp⌝ ∗ ∃ (ents : List raftpb.Entry) (ctx : List w8),
    m.Entries' ↦* ents ∗ ownSliceCap raftpb.Entry m.Entries' (DFrac.own 1) ∗
    m.Context' ↦*□ ctx ∗ ⌜ctx ≠ campaignTransfer⌝ ∗
    isMessage γ.raft (absMsg .propose m ents))

/-- A proposal on `propc`: the message `Propose` builds, with its one-entry batch owned,
the data read-only and its record (`entData`, 2026-10-10), and its result channel, of
which `run` is the producer (a `Handoff`: `run` sends the error and closes); or
(2026-10-10) a proposal forwarded by a peer (`Node.Step`), with no result channel. -/
def propP (γ : NodeNames) (pm : msgWithResult) : IProp GF :=
  iprop((∃ (data_sl esl : GoSlice) (data : List w8) (γr : HandoffNames),
    ⌜pm.m' = propMsg esl⌝ ∗ esl ↦* [propEntry data_sl] ∗
    ownSliceCap raftpb.Entry esl (DFrac.own 1) ∗ data_sl ↦*□ data ∗
    entData γ.raft (propEntry data_sl) ∗
    isHandoff γr pm.result' (fun (_ : GoInterface) => iprop(True)) iprop(True) iprop(True) ∗
    handoffProducer γr false) ∨
    (⌜pm.result' = zero_val GoChan⌝ ∗ fwdP γ pm.m'))

/-- A message from the network on `recvc`, for node `id`: what `RawNode.Step` takes
(`NetMsgOk`, its entries read-only with their capacity, its context, its abstraction sent;
since 2026-10-13 a read-index request only with more than one voter, and with its read
credit) and a term within the budget. Also (2026-10-13) a local read-index request
(`node.ReadIndex`), which goes through `step` too. -/
def netP (γ : NodeNames) (id : w64) (m : raftpb.Message) : IProp GF :=
  iprop(⌜NetMsgOk id m⌝ ∗
    ∃ (ents : List raftpb.Entry) (ctx : List w8),
      m.Entries' ↦*□ ents ∗ ownSliceCap raftpb.Entry m.Entries' (DFrac.own 1) ∗
      m.Context' ↦*□ ctx ∗
      ⌜ctx ≠ campaignTransfer ∧ (m.Type' = MsgReadIndex → 1 < GMap.size γ.raft.reCfg)⌝ ∗
      □ (∀ ty, ⌜mtypeOf m.Type' = some ty⌝ -∗ isMessage γ.raft (absMsg ty m ents ctx)) ∗
      termLB γ.bud m.Term' ∗
      rdCred γ.raft (if m.Type' = MsgReadIndex then 1 else 0))

/-- What `Node.Step` takes (2026-10-10): a message from the network for the receive
channel (`netP`), or a proposal forwarded by a peer (`fwdP`). -/
def stepP (γ : NodeNames) (id : w64) (m : raftpb.Message) : IProp GF :=
  iprop(netP γ id m ∨ fwdP γ m)

/-- What a `Ready` gives the driver, after the committed log `d` handed out before it: the
committed entries `ce` to apply next (`isCommitted` of `d ++ ce`), the entries `es` to
append with the right to (`appendRight`), the messages to send (each legitimately sent,
of a term within the budget, and (2026-10-13) with its read credit, one for a
`MsgReadIndex`, for the receiver's `Step`), no snapshot, and (2026-10-13) the read states, read-only,
each `readStateOk`: its context a proposed slice (`isPropData`) whose read was created
knowing a committed log of length at most its index (`readOk`). -/
def readyData (γ : NodeNames) (rd : Ready) (d ce es : List raftpb.Entry)
    (ms : List raftpb.Message) : IProp GF :=
  iprop(rd.CommittedEntries' ↦*□ ce ∗ isCommitted γ.raft (d ++ ce) ∗
    rd.Entries' ↦*□ es ∗ appendRight γ.stor es ∗
    rd.Messages' ↦* ms ∗ ([∗list] m ∈ ms, isRaftMsg γ.raft m ∗ termLB γ.bud m.Term') ∗
    ([∗list] m ∈ ms, rdCred γ.raft (if m.Type' = MsgReadIndex then 1 else 0)) ∗
    (∃ sts : List ReadState, rd.ReadStates' ↦*□ sts ∗ [∗list] st ∈ sts, readStateOk γ.raft st) ∗
    ⌜rd.Snapshot' = zero_val raftpb.Snapshot⌝)

/-- A `Ready` on `readyc` (see the file header): `run`'s half of `dlv` at `d`, the other half
of its record, and the data. -/
def readyP (γ : NodeNames) (rd : Ready) : IProp GF :=
  iprop(∃ (d ce es : List raftpb.Entry) (ms : List raftpb.Message),
    dghostVar γ.dlv (DFrac.own (1 : Qp).half) d ∗
    dghostVar γ.rof (DFrac.own (1 : Qp).half) (d, ce, es) ∗ readyData γ rd d ce es ms)

/-- An `Advance` on `advancec`: a `dlv` half after the last `Ready`, `run`'s record back,
and the receipt of the append of the `Ready`'s entries. -/
def advanceP (γ : NodeNames) (_ : Unit) : IProp GF :=
  iprop(∃ (d ce es : List raftpb.Entry),
    dghostVar γ.dlv (DFrac.own (1 : Qp).half) (d ++ ce) ∗
    dghostVar γ.rof (DFrac.own (1 : Qp).half) (d, ce, es) ∗ appendReceipt γ.stor es)

/-- The tick channel: one credit per buffered tick. -/
def tickInv (γ : NodeNames) : IProp GF :=
  iprop(∃ l : List Unit, ownChan γ.tick Unit (.Buffered l) ∗ tickCred γ.bud l.length)

/-- See the file header. -/
def isNode (γ : NodeNames) (id : w64) (n : Loc) : IProp GF :=
  iprop(∃ (nv : node) (r : Loc) (lok : GoInterfaceOk),
    "#Hn" ∷ n ↦□ nv ∗
    "#Hrnraft" ∷ nv.rn'.[RawNode, go!"raft"] ↦□ r ∗
    "#Hrid" ∷ r.[raft, go!"id"] ↦□ id ∗
    "#Hrlogger" ∷ r.[raft, go!"logger"] ↦□ (interface.ok lok : GoInterface) ∗
    "#Hlogger" ∷ isLogger lok ∗
    "#Hpropc" ∷ isHandshake γ.propc nv.propc' (propP γ) iprop(True) ∗
    "#Hrecvc" ∷ isHandshake γ.recvc nv.recvc' (netP γ id) iprop(True) ∗
    "#Hconfc" ∷ isHandshake γ.confc nv.confc' (fun (_ : raftpb.ConfChangeV2) => iprop(False))
      iprop(True) ∗
    "#Hreadyc" ∷ isHandshake γ.readyc nv.readyc' (readyP γ) iprop(True) ∗
    "#Hadvancec" ∷ isHandshake γ.advancec nv.advancec' (advanceP γ) iprop(True) ∗
    "#Hdone" ∷ isHandshake γ.done nv.done' (fun (_ : Unit) => iprop(False)) iprop(True) ∗
    "#Hstop" ∷ isHandshake γ.stop nv.stop' (fun (_ : Unit) => iprop(False)) iprop(True) ∗
    "#Hstatus" ∷ isHandshake γ.status nv.status' (fun (_ : GoChan) => iprop(False)) iprop(True) ∗
    "#Htickc" ∷ isChan nv.tickc' γ.tick Unit ∗
    "#Htickinv" ∷ inv tickN (tickInv γ) ∗
    "#Hbud" ∷ inv budgetN (budgetInv γ.bud) ∗
    -- the cluster's commit invariant and proposed slices (2026-10-10)
    "#Hcinv" ∷ raftCommitInv γ.raft ∗
    "#Hpdinv" ∷ inv propDataN (propDataInv γ.raft))

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 4096 in
instance isNode_persistent (γ : NodeNames) (id : w64) (n : Loc) :
    Persistent (isNode (GF := GF) γ id n) := by
  unfold isNode; infer_instance

/-- The driver's token: the committed log it was handed so far is `ds`. -/
def nodeDriver (γ : NodeNames) (id : w64) (n : Loc) (ds : List raftpb.Entry) : IProp GF :=
  iprop(isNode γ id n ∗ dghostVar γ.dlv (DFrac.own (1 : Qp).half) ds)

/-- The driver with a `Ready` in hand: it was handed the committed log `ds` (the last
`Ready`'s included) and must append `es` (the last `Ready`'s entries) before `Advance`. -/
def nodeDriverBusy (γ : NodeNames) (id : w64) (n : Loc) (ds es : List raftpb.Entry) :
    IProp GF :=
  iprop(isNode γ id n ∗
    ∃ (d ce : List raftpb.Entry), dghostVar γ.dlv (DFrac.own (1 : Qp).half) d ∗
      dghostVar γ.dlv (DFrac.own (1 : Qp).half) d ∗
      dghostVar γ.rof (DFrac.own (1 : Qp).half) (d, ce, es) ∗ ⌜ds = d ++ ce⌝)

/-- `readyc`, as the driver sees it (`Node.Ready()`'s result). -/
def isReadyChan (γ : NodeNames) (ch : Loc) : IProp GF :=
  isHandshake γ.readyc ch (readyP γ) iprop(True)

instance isReadyChan_persistent (γ : NodeNames) (ch : Loc) :
    Persistent (isReadyChan (GF := GF) γ ch) := by
  unfold isReadyChan; infer_instance

/-- **Receiving a `Ready`** (the driver's loop, `for rd := range node.Ready()`): with the
driver's token, the `Ready`'s data for the committed log handed out so far, and the token
busy with it. The channel is never closed. -/
theorem node_ready_receive (γ : NodeNames) (id : w64) (n ch : Loc) (ds : List raftpb.Entry) :
    {{ isReadyChan γ ch ∗ nodeDriver (GF := GF) γ id n ds }}
      (App (Val (chan.receive Ready.ty)) (Val #ch))
    {{ (rd : Ready), RET (PairV #rd #true);
        ∃ (ce es : List raftpb.Entry) (ms : List raftpb.Message),
          readyData γ rd ds ce es ms ∗ nodeDriverBusy γ id n (ds ++ ce) es }} := by
  iintro %Φ ⟨#Hrc, Hdrv⟩ HΦ
  unfold nodeDriver
  icases Hdrv with ⟨#Hnode, Hds⟩
  unfold isReadyChan
  iapply wp_handshake_receive (t := Ready.ty) γ.readyc ch (readyP γ) iprop(True) $$ [] [HΦ Hds]
  · iframe Hrc
  iintro %rd
  iintro !> HP
  unfold readyP
  icases HP with ⟨%d, %ce, %es, %ms, Hd, Hrof, Hdata⟩
  ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hd Hds
  subst Heq
  iapply HΦ
  iexists ce, es, ms
  iframe Hdata
  unfold nodeDriverBusy
  iframe Hnode
  iexists d, ce
  iframe Hd Hds Hrof
  ipureintro; rfl

/-- The handshake's send, where the payload is made only when the send happens (a ghost
update inside the atomic update): `run` hands out the storage's append right with a
`Ready` (`ownRawNodeReady_handout`) only if the `Ready` is taken. -/
theorem handshake_send_au_upd {V : Type} [Pos.Countable V] [ZeroVal V]
    [TypedPointsto (GF := GF) V] {t : go.GoType} [IntoValTyped (GF := GF) V t]
    (γc : ChanNames) (ch : Loc) (v : V) (P : V → IProp GF) (Q : IProp GF) (Φ : IProp GF) :
    ⊢ £ 1 ∗ £ 1 ∗ £ 1 -∗ isHandshake γc ch P Q -∗ (|==> (P v ∗ ▷ (Q -∗ Φ))) -∗
      sendAu γc v Φ := by
  iintro Hlc #His Hupd
  unfold sendAu
  imod Hupd with ⟨HP, Hau⟩
  ihave H := handshake_send_au γc ch v P Q Φ $$ Hlc His HP Hau
  iunfold sendAu at H
  iexact H

end node

section helpers
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

theorem isHandshake_isChan {V : Type} [Pos.Countable V] [ZeroVal V]
    [TypedPointsto (GF := GF) V] (γc : ChanNames) (ch : Loc) (P : V → IProp GF) (Q : IProp GF) :
    ⊢ isHandshake γc ch P Q -∗ isChan ch γc V := by
  iintro H
  unfold isHandshake
  icases H with ⟨$, -⟩

/-- A receive on a channel nobody sends on (`P := False`) never completes: any
continuation. -/
theorem handshake_false_recv_au {V : Type} [Pos.Countable V] [ZeroVal V]
    [TypedPointsto (GF := GF) V] (γc : ChanNames) (ch : Loc) (Φ : V → Bool → IProp GF) :
    ⊢ £ 1 ∗ £ 1 -∗ isHandshake γc ch (fun (_ : V) => iprop(False)) iprop(True) -∗
      recvAu γc V Φ := by
  iintro Hlc #Hh
  iapply handshake_receive_au γc ch (fun (_ : V) => iprop(False)) iprop(True) Φ $$ Hlc Hh []
  · itrivial
  inext
  iintro %v Hf
  iexfalso; iexact Hf

end helpers

set_option hygiene false in
/-- Open `isNode` in the hypothesis `H` (persistent): the node struct's value `nv`, the
raft struct `r`, its logger `lok`, the named conjuncts, and the node struct's fields as
persistent points-tos (named by field: `propc`, `recvc`, ..., `rn`). -/
macro "open_node " H:ident : tactic =>
  `(tactic| (iunfold isNode at $H:ident
             icases $H:ident with ⟨%nv, %r, %lok, #$H:ident⟩
             iNamed $H:ident
             ihave #Hn' := Hn
             iStructNamed Hn'))

/-! ## Proposals and the client log, at the node (2026-10-10)

The cluster's proposed slices (`propDataInv`), allocated once with the raft ghost state;
a proposal's ghost work before it leaves the node (`node_propose_ghost`: the slice
recorded, the update deposited); and what the committed log's entries hold, for the
application applying them (`node_committed_data`, `node_entData_heap`,
`node_collect`). -/

section props
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- What `Node.Propose` takes for its data `d` (`fresh`: the first proposal of `d`, with
its fresh token and the client's atomic update; otherwise a retry, with `d` deposited). -/
def propArg (γ : RaftNames) (d : List w8) (Q : List (List w8) → IProp GF) (fresh : Bool) :
    IProp GF :=
  if fresh then iprop(propFresh γ d ∗ propAu γ d Q) else deposited γ d

/-- What it gives back: `d` deposited, and for a first proposal the handle and ticket for
the update's result. -/
def propRes (γ : RaftNames) (d : List w8) (Q : List (List w8) → IProp GF) (fresh : Bool) :
    IProp GF :=
  iprop(deposited γ d ∗
    if fresh then iprop(∃ γp, isProp γ d γp Q ∗ propTok γp) else iprop(True))

theorem propDataInv_alloc (γ : RaftNames) (E : CoPset) :
    ⊢ ghostMapAuth γ.reSl 1 (∅ : GMap GoSlice (List w8)) ={E}=∗
      inv propDataN (propDataInv (GF := GF) γ) := by
  iintro Ha
  iapply inv_alloc propDataN E
  inext
  unfold propDataInv
  iexists ∅
  iframe Ha
  iapply (BigSepM.bigSepM_empty).2; iempintro

/-- Recording a proposed slice. -/
theorem propData_register (γ : RaftNames) (sl : GoSlice) (d : List w8) (E : CoPset)
    (HE : ↑propDataN ⊆ E) :
    ⊢ inv propDataN (propDataInv (GF := GF) γ) -∗ sl ↦*□ d ={E}=∗ isPropData γ sl d := by
  iintro #Hinv #Hsl
  iinv Hinv with >Hi Hclose
  unfold propDataInv
  icases Hi with ⟨%S, Ha, #Hm⟩
  cases HS : S !! sl with
  | some d' =>
    ihave ⟨#Hsl', #Hfrag⟩ := BigSepM.bigSepM_lookup (Φ := fun (sl : GoSlice) (d : List w8) =>
      iprop(sl ↦*□ d ∗ sl ↪[γ.reSl]□ d)) HS $$ Hm
    ihave %Heq := ownSlice_agree sl _ _ d d' $$ Hsl Hsl'
    subst Heq
    imod Hclose $$ [Ha] with -
    · inext
      iexists S
      iframe Ha Hm
    imodintro
    unfold isPropData
    iexact Hfrag
  | none =>
    imod ghost_map_insert_persist sl d HS $$ Ha with ⟨Ha, #Hfrag⟩
    imod Hclose $$ [Ha] with -
    · inext
      iexists Std.insert S sl d
      iframe Ha
      iapply (BigSepM.bigSepM_insert (Φ := fun (sl : GoSlice) (d : List w8) =>
        iprop(sl ↦*□ d ∗ sl ↪[γ.reSl]□ d)) HS).2
      iframe Hsl Hfrag Hm
    imodintro
    unfold isPropData
    iexact Hfrag

/-- A recorded slice holds its data. -/
theorem propData_heap (γ : RaftNames) (sl : GoSlice) (d : List w8) (E : CoPset)
    (HE : ↑propDataN ⊆ E) :
    ⊢ inv propDataN (propDataInv (GF := GF) γ) -∗ isPropData γ sl d ={E}=∗ sl ↦*□ d := by
  iintro #Hinv #Hfrag
  iinv Hinv with >Hi Hclose
  unfold propDataInv
  icases Hi with ⟨%S, Ha, #Hm⟩
  unfold isPropData
  icases ghost_map_lookup $$ Ha Hfrag with %HS
  ihave ⟨#Hsl, -⟩ := BigSepM.bigSepM_lookup (Φ := fun (sl : GoSlice) (d : List w8) =>
    iprop(sl ↦*□ d ∗ sl ↪[γ.reSl]□ d)) HS $$ Hm
  imod Hclose $$ [Ha] with -
  · inext
    iexists S
    iframe Ha Hm
  imodintro
  iexact Hsl

end props

section nodeprops
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A proposal's ghost work before it leaves the node (`Node.Propose`): its slice
recorded, its update deposited (a first proposal; a later credit with it), so that its
entry carries its data (`entData`). -/
theorem node_propose_ghost (γ : NodeNames) (id : w64) (n : Loc) (data_sl : GoSlice)
    (data : List w8) (Q : List (List w8) → IProp GF) (fresh : Bool) (E : CoPset)
    (HE1 : ↑raftN ⊆ E) (HE2 : ↑propDataN ⊆ E) :
    ⊢ isNode γ id n -∗ data_sl ↦*□ data -∗ £ 1 -∗ propArg γ.raft data Q fresh ={E}=∗
      entData γ.raft (propEntry data_sl) ∗ propRes γ.raft data Q fresh := by
  iintro #Hnode #Hdata Hlc Harg
  open_node Hnode
  imod propData_register γ.raft data_sl data E HE2 $$ Hpdinv Hdata with #Hpd
  ihave Hres : |={E}=> propRes γ.raft data Q fresh $$ [Hlc Harg]
  · unfold propArg propRes
    cases fresh with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      imodintro
      iframe Harg
    | true =>
      simp only [↓reduceIte]
      icases Harg with ⟨Hfr, Hau⟩
      imod prop_deposit γ.raft E data Q HE1 $$ Hcinv Hfr Hlc Hau with ⟨%γp, #Hp, Htok⟩
      imodintro
      isplitr
      · iapply isProp_deposited $$ Hp
      · iexists γp
        iframe Hp Htok
  imod Hres with Hres
  ihave #Hdep : deposited γ.raft data $$ [Hres]
  · unfold propRes
    icases Hres with ⟨#Hd, -⟩
    iexact Hd
  imodintro
  iframe Hres
  unfold entData
  by_cases Hz : data_sl = (zero_val raftpb.Entry).Data'
  · iexists none
    unfold entDataIs
    ileft
    ipureintro; exact ⟨rfl, Hz⟩
  · iexists some data
    unfold entDataIs propEntry
    simp only []
    iframe Hpd Hdep
    ipureintro; exact ⟨Hz, rfl⟩

/-- A read context's slice, recorded (2026-10-13): what `Node.ReadIndex` takes of it
(`isPropData`). -/
theorem node_read_register (γ : NodeNames) (id : w64) (n : Loc) (rctx : GoSlice) (c : List w8)
    (E : CoPset) (HE : ↑propDataN ⊆ E) :
    ⊢ isNode γ id n -∗ rctx ↦*□ c ={E}=∗ isPropData γ.raft rctx c := by
  iintro #Hnode #Hc
  open_node Hnode
  iapply propData_register γ.raft rctx c E HE $$ Hpdinv Hc

/-- A `ReadState`'s context, read through the heap (2026-10-13): the bytes `c` its slice
holds, and `readOk` of them. A client that compares them with its own context's (its
`readReq γ c Lc`) learns `readOk` of its read (`readOk_prefix`). -/
theorem node_readState_data (γ : NodeNames) (id : w64) (n : Loc) (st : ReadState) (E : CoPset)
    (HE : ↑propDataN ⊆ E) :
    ⊢ isNode γ id n -∗ readStateOk γ.raft st ={E}=∗
      ∃ c, st.RequestCtx' ↦*□ c ∗ readOk γ.raft c st.Index' := by
  iintro #Hnode #Hst
  iunfold readStateOk at Hst
  icases Hst with ⟨%c, #Hpd, #Hok⟩
  open_node Hnode
  imod propData_heap γ.raft st.RequestCtx' c E HE $$ Hpdinv Hpd with #Hsl
  imodintro
  iexists c
  iframe Hsl Hok

/-- The data of a committed log's entries. -/
theorem node_committed_data (γ : NodeNames) (id : w64) (n : Loc) (l : List raftpb.Entry)
    (E : CoPset) (HE : ↑raftN ⊆ E) :
    ⊢ isNode γ id n -∗ isCommitted γ.raft l ={E}=∗
      ∃ ods, [∗list] e;o ∈ l;ods, entDataIs (GF := GF) γ.raft e o := by
  iintro #Hnode #Hc
  open_node Hnode
  iapply committed_data γ.raft E l HE $$ Hcinv Hc

/-- A proposed entry's slice holds its data. -/
theorem node_entData_heap (γ : NodeNames) (id : w64) (n : Loc) (e : raftpb.Entry)
    (d : List w8) (E : CoPset) (HE : ↑propDataN ⊆ E) :
    ⊢ isNode γ id n -∗ entDataIs γ.raft e (some d) ={E}=∗ e.Data' ↦*□ d := by
  iintro #Hnode #He
  open_node Hnode
  unfold entDataIs
  icases He with ⟨-, #Hpd, -⟩
  iapply propData_heap γ.raft e.Data' d E HE $$ Hpdinv Hpd

/-- Collecting a proposal's result (`prop_collect`), at the node. -/
theorem node_collect (γ : NodeNames) (id : w64) (n : Loc) (d : List w8) (γp : GName × GName)
    (Q : List (List w8) → IProp GF) (l : List raftpb.Entry) (ods : List (Option (List w8)))
    (m : Nat) (E : CoPset) (HE : ↑raftN ⊆ E) :
    ods[m]? = some (some d) → d ∉ firstOcc (ods.take m) →
    ⊢ isNode γ id n -∗ isProp γ.raft d γp Q -∗ propTok γp -∗ isCommitted γ.raft l -∗
      ([∗list] e;o ∈ l;ods, entDataIs γ.raft e o) ={E}=∗ ▷ ▷ Q (firstOcc (ods.take m)) := by
  intro Hm Hf
  iintro #Hnode #Hp Htok #Hc #Hds
  open_node Hnode
  iapply prop_collect γ.raft E d γp Q l ods m HE Hm Hf $$ Hcinv Hp Htok Hc Hds

end nodeprops

end EtcdGrove
end Perennial
