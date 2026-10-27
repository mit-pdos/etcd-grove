/-
Lean-first (no Rocq counterpart).

# `node.go`: the concurrent `Node` over a `RawNode` (2026-10-10)

`node.run` is one goroutine that owns the `RawNode`; clients talk to it over channels:
`propc` (a proposal and, for `Propose`, a buffered result channel), `recvc` (a message from
the network), `tickc` (buffered, a tick dropped when full), `readyc` (the next `Ready`),
`advancec` (the application's "done with that `Ready`"), `confc`/`confstatec` (a conf change
to apply and the resulting `ConfState`, `confcP`/`confstateP`: since 2026-10-13 in the static
mode a change that keeps the voters; since 2026-10-15, stage N, in the dynamic mode any change
the driver applies in order), and `done`, `stop`, `status` (shutdown and status: out of scope,
never used).

Since 2026-10-15 (stage N) `node.go` is verified in either mode of the `RawNode`
(`NodeNames.mode`). In the dynamic mode `run` and the driver also share the committed log handed
out (`dlm`, a `mono_list`: `run`'s authority, the driver's `dlvLb`), the configuration as of the
last applied conf change (`cap`, halves: `run`'s in `runCfg`, the driver's in `nodeCfg`) with its
index as a monotone nat (`cam`), and an answer slot (`ccq`); see `confcP`, `confstateP`,
`advanceP` and `runCfg`.

## The ghost state

- **The term budget** (`BudgetNames`, one per cluster): `RawNode.Tick` needs `term + 1 <
  2^64`, and `RawNode.Step` moves a node's term to at most a message's. The invariant
  `isBudget` holds a monotone bound `M` (`monoNatAuthOwn`) backed by time receipts (D19b,
  2026-10-18: `k` receipts with `M ≤ k + 1`, under `receiptBound GF ≤ 2 ^ 64 - 2`; until then
  the number `c` of tick credits handed out, `● c`, with `M + c < 2^64 - 1`). A tick credit
  (`tickCred bud 1`, a time receipt since D19b) is what `Node.Tick` spends (`budget_spend`): it
  raises `M` by
  at most one past a term. Every node's term ceiling (`RNState.tc`, 2026-10-17; until then its
  term) is at most `M` (`termLB`, a lower bound on `M`, persistent), and so is every message's
  term a `Ready` hands out (`readyData`): a receiver raises its ceiling to the message's term
  (`ownRawNode_raise_tc`) and its `Step` keeps its term under it; a tick raises the ceiling by
  one with its credit (a pre-campaign's requests are of the next term). The application creates the budget once
  (`budget_alloc`); since D19b a tick's caller takes the credit, a receipt, from a Go step of
  its own (until then `budget_alloc` handed out as many credits as it would ever tick).
- **The `Ready`/`Advance` hand-shake** between `run` and the single *driver* (the
  application's loop over `Node.Ready()`): `dlv` (halves: `run`'s and the driver's) is the
  committed log handed out so far, `rof` (halves: `run` keeps one) records the last
  `Ready`'s `(delivered, committed entries, entries)`. A `Ready` carries `run`'s `dlv` half
  and the other `rof` half (`readyP`): the driver, holding both `dlv` halves, learns that
  the `Ready`'s committed entries come right after what it applied, and moves `dlv` on
  (`node_ready_receive`). `Advance` carries a `dlv` half back with the `rof` half and the
  receipt of the storage append (`advanceP`): `run` recognizes its own record (`rof`) and so
  the receipt is for the entries it handed out. (D22 S-d4, 2026-10-21) With a snapshot (at a node
  that takes them, `NodeNames.snapIn`) the record names the loan (`SnapLoan`), the `Ready` hands
  out half the snapshot, the committed log up to it (`dlvAfter`), the storage itself and the
  snapshot's certificate (`readySnapData`), and the receipt is the storage at the snapshot
  (`advReceipt`, `snapReceipt`).
- **The channels**: Perennial's `Handshake` idiom for the unbuffered ones (the payload `P`
  from the sender, nothing back), with `P := False` for the channels nobody sends on; the
  tick channel's own invariant (`tickInv`: one credit per buffered tick); a proposal's
  result channel is a `Handoff` (`Proof/go_etcd_io/etcd/cache/v3/Handoff.lean`).

`isNode γ id n` (persistent) is the node struct (read-only), the raft struct's two shared
fields (`raftOwn`, `rawNodeOwn`: `Tick`'s warning reads them), the channels' invariants and
the budget. `nodeDriver γ n ds` is the driver's token.

**Raft v3.7 (2026-10-16, stage R5 of the retarget, `notes/decisions.md`, "The node layer over
pointer messages").** Ported from the old proof's file. What changed: the channels carry
pointers (`recvc`, `confc`, `confstatec` a `Loc`; `propc` a `msgWithResult` whose `m` is a
`*pb.Message`), so the payloads are over the pointed-to objects: `fwdP γ ml`/`netP γ id ml` an
owned message (`msgIn`) and its state's facts (`NetMsgOk` on the state, `InvRawnode.lean`),
`propP γ pm` the message `Propose` builds (`propMsgM`, one entry `propEntryM d` holding the
data's bytes, D6), `confcP γ v` a read-only `*pb.ConfChangeV2` (`ownCCV2 v □ ccm`, the changes
`ccm.changes`), `confstateP γ cs` the fresh `*pb.ConfState` `applyConfChange` returns (`csPts cs
1 c true`), with `confstateOk`/`confstateS` pure over its record; `readyData` hands out the
messages (D8, at `readyDq`), the hard state (`hsOpt`), the entries `entsRO`, the read states
`readStatesPts`. D6 retired the proposed slices: `propDataInv`, `propDataN`,
`propData_register`, `propData_heap`, `propDataInv_alloc`, `node_read_register` are gone (a
read context, an entry's data, is its bytes); `node_readState_data`/`node_entData_heap` read
them off the records. The countability instances of the old Goose message types are gone (no
channel carries one).
-/
module

public import Proof.go_etcd_io.raft.v3.ApiCtx
public import Proof.go_etcd_io.raft.v3.ApiVocab
public import Proof.go_etcd_io.raft.v3.CCApply
public import Proof.go_etcd_io.raft.v3.InvConfchange
public import Proof.go_etcd_io.raft.v3.InvStorage
import Proof.go_etcd_io.raft.v3.InvRawnodeReady
-- (2026-10-16, stage R5) `netStepTypes`, `NetMsgOk`, `DynCCPreOp`, `propEntryM` are
-- `InvRawnode.lean`'s (until then `RawNode__Step`'s, `RawNode__Propose`'s,
-- `RawNode__ApplyConfChange`'s)
public import Perennial.Golang.Theory.Chan.Idioms.Handshake
public import Proof.go_etcd_io.etcd.cache.v3.Handoff
public import Perennial.Ghost.MonoNat
public import Proof.go_etcd_io.raft.v3.Protocol.Facts
import Proof.go_etcd_io.raft.v3.InvApplyConf
public import Perennial.Ghost.MonoList

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI OFE CMRA Iris.ProofMode go_etcd_io.raft.v3

/-! ## Countability of the channels' element types -/

section countable
variable [GooseExts]

-- (2026-10-16, stage R5) the instances for `raftpb.HardState`, `ConfState`,
-- `SnapshotMetadata`, `Snapshot`, `Message`, `ConfChangeV2` are gone: the channels carry
-- pointers to them.

instance msgWithResult_countable : Pos.Countable msgWithResult :=
  countableOfLeftInverse (fun m : msgWithResult => (m.m', m.result'))
    (fun p => ⟨p.1, p.2⟩) (fun _ => rfl)

instance ready_countable : Pos.Countable Ready :=
  countableOfLeftInverse
    (fun r : Ready => (r.SoftState', r.HardState', r.ReadStates', r.Entries', r.Snapshot',
      r.CommittedEntries', r.Messages', r.MustSync'))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2⟩) (fun _ => rfl)

/-- (2026-10-15, stage N) a configuration, for the run loop's configuration shared with the
driver (`NodeNames.cap`). -/
instance cfgM_countable : Pos.Countable CfgM :=
  countableOfLeftInverse
    (fun c : CfgM => (c.incoming, c.outgoing, c.learners, c.learnersNext, c.autoLeave))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩) (fun _ => rfl)

instance ccState_countable : Pos.Countable CCState :=
  countableOfLeftInverse (fun c : CCState => (c.cfg, c.prs)) (fun p => ⟨p.1, p.2⟩)
    (fun _ => rfl)

/-- (D22 S-d4, 2026-10-21) A snapshot `Ready`'s loan, in `run`'s record of its last `Ready`
(`NodeNames.rof`). -/
instance snapLoan_countable : Pos.Countable SnapLoan :=
  .ofInjective (fun l => Pos.Countable.encode
      ((((((((((l.ptr, l.snap.Data'), l.snap.Metadata'.ConfState'.Voters'),
        l.snap.Metadata'.ConfState'.Learners'), l.snap.Metadata'.ConfState'.VotersOutgoing'),
        l.snap.Metadata'.ConfState'.LearnersNext'), l.snap.Metadata'.ConfState'.AutoLeave'),
        l.snap.Metadata'.Index'), l.snap.Metadata'.Term'), l.fl), l.dlv))
    (fun ⟨_, ⟨_, ⟨⟨_, _, _, _, _⟩, _, _⟩⟩, _, _⟩ ⟨_, ⟨_, ⟨⟨_, _, _, _, _⟩, _, _⟩⟩, _, _⟩ h => by
      have h := Pos.encode_inj h
      simp only [Prod.mk.injEq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := h
      rfl)

end countable

/-! ## The term budget -/

/-- Ghost names of a cluster's term budget (D19b, 2026-10-18: until then also the tick credits'
`Auth Nat`, `creds`; the credits are time receipts now). -/
structure BudgetNames where
  /-- the bound `M` on every term (a monotone nat) -/
  bound : GName

def budgetN : Namespace := nroot.@"raft_budget"


section budget
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- See the file header. The bound `M` is backed by time receipts (D19b, 2026-10-18): `k`
receipts with `M ≤ k + 1` (the `+ 1` the bootstrap term), and the receipts' bound is at most
`2 ^ 64 - 2`, so `M < 2 ^ 64 - 1`. Until D19b: `M + c < 2 ^ 64 - 1` with `c` the tick credits
handed out (an `Auth Nat`), minted by the application up front. -/
def budgetInv (bud : BudgetNames) : IProp GF :=
  iprop(∃ (M k : Nat), monoNatAuthOwn bud.bound 1 M ∗ ⧗ k ∗
    ⌜M ≤ k + 1 ∧ receiptBound GF ≤ 2 ^ 64 - 2⌝)

/-- `n` tick credits: `Node.Tick` spends one. Since D19b (2026-10-18) `n` time receipts (`bud`
unused): a tick's caller takes one from a Go step of its own. -/
def tickCred (_bud : BudgetNames) (n : Nat) : IProp GF := ⧗ n

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
  exact receipt_add a b

theorem tickCred_zero (bud : BudgetNames) : ⊢ |==> tickCred (GF := GF) bud 0 := by
  unfold tickCred
  exact receipt_zero

theorem termLB_le (bud : BudgetNames) (t t' : w64) (h : uint.Z t' ≤ uint.Z t) :
    ⊢ termLB (GF := GF) bud t -∗ termLB bud t' := by
  unfold termLB
  iapply monoNatLbOwn_le
  have := uint_nat_eq t
  have := uint_nat_eq t'
  omega

/-- The budget at bound `m ≤ 1`, created once per cluster (D19b: under the receipts' bound;
until then with `N` credits). -/
theorem budget_alloc_at (m : Nat) (hm : m ≤ 1) (Hb : receiptBound GF ≤ 2 ^ 64 - 2)
    (E : CoPset) :
    ⊢ |={E}=> ∃ bud : BudgetNames, inv budgetN (budgetInv (GF := GF) bud) ∗
      monoNatLbOwn bud.bound m := by
  imod mono_nat_own_alloc (GF := GF) m with ⟨%γM, HM, #HMlb⟩
  imod receipt_zero (GF := GF) with H0
  imod inv_alloc budgetN E (budgetInv (GF := GF) ⟨γM⟩) $$ [HM H0] with #Hinv
  · inext
    unfold budgetInv
    iexists m, 0
    iframe HM H0
    ipureintro; omega
  imodintro
  iexists ⟨γM⟩
  iframe Hinv HMlb

/-- The budget, created once per cluster. -/
theorem budget_alloc (Hb : receiptBound GF ≤ 2 ^ 64 - 2) (E : CoPset) :
    ⊢ |={E}=> ∃ bud : BudgetNames, inv budgetN (budgetInv (GF := GF) bud) ∗
      termLB bud (W64 0) := by
  imod budget_alloc_at 0 (by omega) Hb E with ⟨%bud, #Hinv, #Hlb⟩
  imodintro
  iexists bud
  iframe Hinv
  unfold termLB
  iExactEq Hlb
  rfl

/-- The budget of a new cluster (2026-10-16, stage R8b, `StartNode`): its bound at the bootstrap
term `1` from the start (`RawNode.Bootstrap`'s `becomeFollower(1, None)`), so that `run` starts
with `termLB bud 1`. -/
theorem budget_alloc_boot (Hb : receiptBound GF ≤ 2 ^ 64 - 2) (E : CoPset) :
    ⊢ |={E}=> ∃ bud : BudgetNames, inv budgetN (budgetInv (GF := GF) bud) ∗
      termLB bud (W64 1) := by
  imod budget_alloc_at 1 (by omega) Hb E with ⟨%bud, #Hinv, #Hlb⟩
  imodintro
  iexists bud
  iframe Hinv
  unfold termLB
  iExactEq Hlb
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
  icases Hi with ⟨%M, %k, HM, Hk, %Hb⟩
  unfold termLB
  ihave %Hle := monoNatLbOwn_valid bud.bound 1 M (uint.nat t) $$ HM Hlb
  imod receipt_snapshot k $$ Hk with ⟨Hk, #Hp⟩
  ihave %Hkl := preceipt_lt k $$ Hp
  imod Hclose $$ [HM Hk] with -
  · inext; iexists M, k; iframe HM Hk; ipureintro; exact Hb
  imodintro
  ipureintro
  have := uint_nat_eq t
  omega

/-- Spending a tick credit (a time receipt): the bound covers one term more (`Node.Tick`'s). -/
theorem budget_spend (bud : BudgetNames) (t : w64) (E : CoPset) (HE : ↑budgetN ⊆ E) :
    ⊢ inv budgetN (budgetInv (GF := GF) bud) -∗ tickCred bud 1 -∗ termLB bud t ={E}=∗
      ⌜uint.Z t + 1 < 2 ^ 64 - 1⌝ ∗ termLB bud (t + W64 1) := by
  iintro #Hinv Hcr #Hlb
  iinv Hinv with >Hi Hclose
  unfold budgetInv
  icases Hi with ⟨%M, %k, HM, Hk, %Hb⟩
  unfold termLB tickCred
  ihave %Hle := monoNatLbOwn_valid bud.bound 1 M (uint.nat t) $$ HM Hlb
  icases receipt_add_one_lt k $$ [Hcr Hk] with ⟨%Hlt, Hk⟩
  · iframe
  have := uint_nat_eq t
  have Hnw : uint.Z t + 1 < 2 ^ 64 - 1 := by omega
  imod mono_nat_own_update (max M (uint.nat (t + W64 1))) (Nat.le_max_left _ _) $$ HM
    with ⟨HM, #HMlb⟩
  imod Hclose $$ [HM Hk] with -
  · inext
    iexists max M (uint.nat (t + W64 1)), k + 1
    iframe HM Hk
    ipureintro
    have : uint.Z (t + W64 1) = uint.Z t + 1 := by word
    have := uint_nat_eq (t + W64 1)
    omega
  imodintro
  isplitr
  · ipureintro; exact Hnw
  iapply monoNatLbOwn_le $$ HMlb
  exact Nat.le_max_right _ _

/-- (2026-10-13) A step of a message of term `t2` at a node of term `t1`, with a tick credit
if `P` (a `MsgTimeoutNow`, which campaigns one term past both): neither term is the last
one, and the bound covers the larger, one more if `P`. -/
theorem budget_step (bud : BudgetNames) (t1 t2 : w64) (P : Prop) [Decidable P] (E : CoPset)
    (HE : ↑budgetN ⊆ E) :
    ⊢ inv budgetN (budgetInv (GF := GF) bud) -∗ termLB bud t1 -∗ termLB bud t2 -∗
      tickCred bud (if P then 1 else 0) ={E}=∗
      ⌜uint.Z t1 + 1 < 2 ^ 64 ∧ uint.Z t2 + 1 < 2 ^ 64⌝ ∗
      ∃ tb : w64, termLB bud tb ∗
        ⌜max (uint.Z t1) (uint.Z t2) + (if P then 1 else 0) ≤ uint.Z tb⌝ := by
  iintro #Hinv #Hl1 #Hl2 Hcr
  imod termLB_bound bud t1 E HE $$ Hinv Hl1 with %Hb1
  imod termLB_bound bud t2 E HE $$ Hinv Hl2 with %Hb2
  have Hmx : ∃ tm : w64, uint.Z tm = max (uint.Z t1) (uint.Z t2) ∧
      (tm = t1 ∨ tm = t2) := by
    rcases Int.le_total (uint.Z t1) (uint.Z t2) with h | h
    · exact ⟨t2, by rw [Int.max_eq_right h], .inr rfl⟩
    · exact ⟨t1, by rw [Int.max_eq_left h], .inl rfl⟩
  obtain ⟨tm, Htm, Htm'⟩ := Hmx
  ihave #Hlm : termLB bud tm $$ []
  · rcases Htm' with rfl | rfl
    · iexact Hl1
    · iexact Hl2
  by_cases hP : P
  · simp only [hP, ↓reduceIte]
    imod budget_spend bud tm E HE $$ Hinv Hcr Hlm with ⟨%Hb, #Hl⟩
    imodintro
    isplitr
    · ipureintro; omega
    iexists tm + W64 1
    iframe Hl
    ipureintro
    have : uint.Z (tm + W64 1) = uint.Z tm + 1 := by word
    omega
  · simp only [hP, ↓reduceIte]
    imodintro
    isplitr
    · ipureintro; omega
    iexists tm
    iframe Hlm
    ipureintro
    omega

end budget

/-! ## The node's ghost names and channel payloads -/

/-- Ghost names (and the storage) of one node. -/
structure NodeNames [GooseExts] where
  raft : RaftNames
  bud : BudgetNames
  /-- the node's `Storage` (`RNState.storage`), for the append right and its receipt -/
  stor : Storage
  propc : ChanNames
  recvc : ChanNames
  confc : ChanNames
  /-- (2026-10-13) `confstatec`: the `ConfState` `run` answers a conf change with -/
  confstatec : ChanNames
  readyc : ChanNames
  advancec : ChanNames
  tick : ChanNames
  done : ChanNames
  stop : ChanNames
  status : ChanNames
  /-- the committed log handed out so far: `run`'s half and the driver's -/
  dlv : GName
  /-- `run`'s record of its last `Ready` `(delivered, committed entries, entries)`; (D22l) and the
  hard state after it; (D22 S-d4) and its snapshot's loan, if any (`RNState.slent`) -/
  rof : GName
  /-- (2026-10-15, stage N) the `RawNode`'s mode (`RNState.mode`): static, or dynamic with its
  decoder and initial configuration -/
  mode : RNMode
  /-- (2026-10-15) the committed log handed out so far, as a `mono_list`: `run` holds the
  authority, the driver lower bounds (`dlvLb`), by which `run` checks a conf change's entry -/
  dlm : GName
  /-- (2026-10-15) the configuration index and configuration as of the last applied conf change
  (`(ca, cfg)`): halves, `run`'s and the driver's (`nodeCfg`) -/
  cap : GName
  /-- (2026-10-15) a conf change's expected answer `(k + 1, cs')`, by which the driver
  recognizes `run`'s answer on `confstatec`: the driver holds it whole between changes -/
  ccq : GName
  /-- (2026-10-15) the configuration index of `cap`, as a monotone nat: `run` holds the
  authority, the driver lower bounds, by which `run` checks A1 at `Advance` -/
  cam : GName
  /-- (D19i part 1) the driver's request on `advancec` when it arrives first: the length of the
  committed log it was handed, whole with the driver between `Advance`s, a half in the channel
  while its offer waits (`advInv`); (D22 S-d4) `none` after a snapshot `Ready`, which asks for
  no floor (`reqOf`) -/
  req : GName
  /-- (2026-10-22, D38a) the node's id (`isNode`'s): the sender of the messages its `Ready`s hand
  out (`isRaftMsg`, whose `MsgApp`s are from it) -/
  id : w64
  /-- (D22 S-d4, 2026-10-21) **the application may deliver a `MsgSnap`** (`netP`), a parameter of
  `StartNode`/`RestartNode`: only outside the no-snapshot mode and in the static mode (`runCfg`);
  with it a `Ready` may hand out a snapshot (`readyDataL`). `false` for the server, putget,
  putget3 and the kv example. -/
  snapIn : Bool := false

def tickN : Namespace := nroot.@"raft_tick"

-- (2026-10-16, stage R5, D6) `propDataN`, the proposed slices' invariant's namespace, is gone.

section node
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

-- (2026-10-16, stage R5) `propMsg esl` (the Goose value) is `propMsgM` (`InvRawnode.lean`),
-- the message's scalars; `propDataInv` (the proposed slices, D6) is gone.

/-- A proposal forwarded by a peer (2026-10-10), as `Node.Step` takes it: its batch owned
(`appendEntry` stamps it; a transport delivers a copy), its context (until 2026-10-13 not
the leader-transfer marker), and what it carries as a protocol message (each entry's data,
`entData`, so its update was deposited). (2026-10-16, stage R5: the message at `ml`, owned as
`raft.Step` takes a proposal, `msgIn ml 1`, its entries' slots owned.) (2026-10-22, D38a) With no
responses (`raft.Step`'s `Hnors`: the leader may forward it on). -/
def fwdP (γ : NodeNames) (ml : Loc) : IProp GF :=
  iprop(∃ st : MsgSt, msgIn ml (DFrac.own 1) st ∗ ⌜st.msg.Type' = MsgProp ∧ st.resps = []⌝ ∗
    isMessage γ.raft (absMsg .propose st.msg st.ents) ∗
    -- (2026-10-19, D21 M6) its entries' tickets (`entTk`), which the leader consumes
    ([∗list] e ∈ st.ents, entTk γ.raft e))

-- (2026-10-26, raft's signature, stage 1) `errProposalDropped` moved to `Proof.go_etcd_io.raft.v3.ApiCtx`.

-- (2026-10-26, raft's signature, stage 1) `errProposalDropped_persistent` moved to `Proof.go_etcd_io.raft.v3.ApiCtx`.

-- (2026-10-26, raft's signature, stage 1) `stepErr` moved to `Proof.go_etcd_io.raft.v3.ApiCtx`.

-- (2026-10-26, raft's signature, stage 1) `stepErr_persistent` moved to `Proof.go_etcd_io.raft.v3.ApiCtx`.

/-- A proposal on `propc`: the message `Propose` builds, with its one-entry batch owned,
the data read-only and its record (`entData`, 2026-10-10), and its result channel, of
which `run` is the producer (a `Handoff`: `run` sends the error, `stepErr`, and closes); or
(2026-10-10) a proposal forwarded by a peer (`Node.Step`), with no result channel.
(2026-10-16, stage R5: the message at `pm.m'`, owned (`msgIn`), holding `propMsgM` and the one
entry `propEntryM d`, D6: the data's bytes `d`. Stage R7c: the result channel's value is
`stepErr`; until then nothing was promised of it.) -/
@[no_expose] def propP (γ : NodeNames) (pm : msgWithResult) : IProp GF :=
  iprop((∃ (d : List w8) (γr : HandoffNames),
    msgIn pm.m' (DFrac.own 1) ⟨propMsgM, [propEntryM d], none, [], []⟩ ∗
    propData γ.raft (propEntryM d) ∗ entTk γ.raft (propEntryM d) ∗
    isHandoff γr pm.result' stepErr iprop(True) iprop(True) ∗
    handoffProducer γr false) ∨
    (⌜pm.result' = zero_val GoChan⌝ ∗ fwdP γ pm.m'))

/-- A message from the network on `recvc`, for node `id`: what `RawNode.Step` takes
(`NetMsgOk`, its entries read-only with their capacity, its context, its abstraction sent;
since 2026-10-13 a read-index request with its read credit; until 2026-10-14, stage R, only
with more than one voter) and a term within the budget. Also (2026-10-13) the local messages that go through
`recvc` too: a read-index request (`node.ReadIndex`), a transfer request
(`TransferLeadership`), `ForgetLeader` and the reports (`ReportUnreachable`,
`ReportSnapshot`). Since 2026-10-13 a `MsgTimeoutNow` too, with one tick credit
(`tickCred`): it makes the node campaign at once, one term past its own or the message's,
which the budget must cover as it covers a tick's campaign (`budget_spend`), so whoever
delivers it pays like a tick; and the context may be the leader-transfer marker (a
transfer campaign's vote request). (2026-10-16, stage R5: the message at `ml`, owned as
`raft.Step` takes it, `msgIn ml □ st`; the facts over its state `st`.) -/
def netP (γ : NodeNames) (id : w64) (ml : Loc) : IProp GF :=
  iprop(∃ st : MsgSt, msgIn ml DFrac.discard st ∗ ⌜NetMsgOk id st⌝ ∗
      -- (2026-10-17) a pre-vote request only in a cluster started from a bootstrap log, whose
      -- nodes are past term `0` (`RawNode.Step`'s premise); (2026-10-19, D21 M2r) a leader-transfer
      -- request only outside the cluster's no-transfer mode, where leader transfer is off (D22 S-a:
      -- `RaftNames.reNoXfer`, until then the no-snapshot mode's flag); (D22 S-d4, 2026-10-21) a
      -- snapshot only at a node that takes one (`NodeNames.snapIn`; from D22 S-c to S-d4 none)
      ⌜(st.msg.Type' = MsgPreVote → γ.raft.reBoot ≠ []) ∧
        (st.msg.Type' = MsgTransferLeader → γ.raft.reNoXfer = false) ∧
        (st.msg.Type' = MsgSnap → γ.snapIn = true)⌝ ∗
      -- (D22 S-d4) but a snapshot's, whose abstraction is `absSnap` (`RawNode.Step`'s `#Hmsg`)
      □ (∀ ty, ⌜mtypeOf st.msg.Type' = some ty⌝ -∗ ⌜ty ≠ .snap⌝ -∗
        isMessage γ.raft (absMsg ty st.msg st.ents st.ctx)) ∗
      -- (D22 S-d4) a snapshot's facts and certificate (`RawNode.Step`'s `"#Hsnap"`): the snapshot
      -- the message holds, its index below `2^61`, its abstraction certified (`isMessageC`, which a
      -- sender's `isRaftMsg` gives)
      □ (⌜st.msg.Type' = MsgSnap⌝ -∗
         ∃ (sv : SnapshotM) (scfg : CSLists),
           ⌜st.snap = some sv ∧ scfg = sv.Metadata'.ConfState'.lists ∧
             uint.Z sv.Metadata'.Index' < 2^61⌝ ∗
           isMessageC γ.raft (absSnap st.msg sv scfg) ∗
           -- (D22 S-r, 2026-10-21) and its data certificate (the sender's `msgDat`)
           snapDataOk γ.raft sv.Metadata'.Index' sv.Data' ∗
           -- (2026-10-26, D22 J2, R-loc) and its receiver-local fact (`snapLocal`: for a server,
           -- its index saved in the member's snapshot directory, `snapSaved`)
           snapLocal γ.raft id sv.Metadata'.Index') ∗
      termLB γ.bud st.msg.Term' ∗
      rdCred γ.raft (if st.msg.Type' = MsgReadIndex then 1 else 0) ∗
      tickCred γ.bud (if st.msg.Type' = MsgTimeoutNow then 1 else 0))

/-- (2026-10-13) A local message on `recvc` with no entries, no context and no term (a
transfer request, `ForgetLeader`'s, a report): no credit (but empty ones), no protocol
fact. (2026-10-16, stage R5: over the message's state.) -/
theorem netP_local (γ : NodeNames) (id : w64) (ml : Loc) (st : MsgSt)
    (Hty : st.msg.Type' = MsgTransferLeader ∨ st.msg.Type' = MsgForgetLeader ∨
      st.msg.Type' = MsgUnreachable ∨ st.msg.Type' = MsgSnapStatus)
    (Ht : st.msg.Term' = W64 0) (He : st.ents = []) (Hc : st.ctx = []) (Hr : st.resps = [])
    -- (2026-10-19, D21 M2r) a transfer request only outside the cluster's no-transfer mode
    (Hxt : st.msg.Type' = MsgTransferLeader → γ.raft.reNoXfer = false) :
    ⊢ msgIn (GF := GF) ml DFrac.discard st -∗
      termLB γ.bud (W64 0) -∗ rdCred γ.raft 0 -∗ tickCred γ.bud 0 -∗
      netP γ id ml := by
  have Hun : UnstampedType st.msg.Type' := by
    rcases Hty with h | h | h | h <;> simp [UnstampedType, h]
  have Hnr : st.msg.Type' ≠ MsgReadIndex := by
    rcases Hty with h | h | h | h <;> rw [h] <;>
      simp [MsgReadIndex, MsgTransferLeader, MsgForgetLeader, MsgUnreachable, MsgSnapStatus]
  have Hnt : st.msg.Type' ≠ MsgTimeoutNow := by
    rcases Hty with h | h | h | h <;> rw [h] <;>
      simp [MsgTimeoutNow, MsgTransferLeader, MsgForgetLeader, MsgUnreachable, MsgSnapStatus]
  have Hmt : mtypeOf st.msg.Type' = none := by
    rcases Hty with h | h | h | h <;> rw [h] <;> rfl
  have Hok : NetMsgOk id st := by
    refine ⟨?_, fun h => absurd Hun h, fun _ => Ht, fun h => ?_, fun h => ?_, fun _ => ⟨He, Hc⟩,
      fun h => ?_, Hr⟩
    · rcases Hty with h | h | h | h <;> rw [h] <;> simp [netStepTypes]
    · exfalso
      rcases Hty with h' | h' | h' | h' <;> rw [h'] at h <;>
        simp [MsgApp, MsgHeartbeat, MsgHeartbeatResp,MsgCheckQuorum, MsgReadIndexResp, MsgTransferLeader,
          MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgSnap] at h
    · exfalso
      rcases Hty with h' | h' | h' | h' <;> rw [h'] at h <;>
        simp [MsgAppResp, MsgTransferLeader, MsgForgetLeader, MsgUnreachable, MsgSnapStatus] at h
    · exfalso
      rcases Hty with h' | h' | h' | h' <;> rw [h'] at h <;>
        simp [MsgPreVote, MsgTransferLeader, MsgForgetLeader, MsgUnreachable, MsgSnapStatus] at h
  iintro Hm #Hlb Hcr Htc
  unfold netP
  iexists st
  iframe Hm
  isplitr
  · ipureintro; exact Hok
  have Hns : st.msg.Type' ≠ MsgSnap := by
    rcases Hty with h' | h' | h' | h' <;> rw [h'] <;>
      simp [MsgSnap, MsgTransferLeader, MsgForgetLeader, MsgUnreachable, MsgSnapStatus]
  isplitr
  · ipureintro; refine ⟨fun h => ?_, Hxt, fun h => absurd h Hns⟩
    exfalso
    rcases Hty with h' | h' | h' | h' <;> rw [h'] at h <;>
      simp [MsgPreVote, MsgTransferLeader, MsgForgetLeader, MsgUnreachable, MsgSnapStatus] at h
  rw [Ht, ite_eq_right Hnr, ite_eq_right Hnt]
  isplitr
  · imodintro
    iintro %ty %Hty'
    rw [Hmt] at Hty'
    cases Hty'
  isplitr
  · imodintro
    iintro %h
    exact absurd h Hns
  iframe Hlb Hcr Htc

/-- What `Node.Step` takes (2026-10-10): a message from the network for the receive
channel (`netP`), or a proposal forwarded by a peer (`fwdP`). -/
def stepP (γ : NodeNames) (id : w64) (ml : Loc) : IProp GF :=
  iprop(netP γ id ml ∨ fwdP γ ml)

/-- What a `Ready` gives the driver, after the committed log `d` handed out before it: the
committed entries `ce` to apply next (`isCommitted` of `d ++ ce`), the entries `es` to
append with the right to (`appendRight`), the messages to send (each legitimately sent,
of a term within the budget, and (2026-10-13) with its read credit, one for a
`MsgReadIndex`, for the receiver's `Step`), no snapshot, and (2026-10-13) the read states, read-only,
each `readStateOk`: its context the bytes of a read created knowing a committed log of length
at most its index (`readOk`; until 2026-10-16 a proposed slice, `isPropData`). (2026-10-16, stage R5: D8,
the messages handed out, `ms : List QMsg` -- the pointers `rd.Messages` holds and their
states -- each owned at `readyDq` (a response at half: `acceptReady` reads the other half);
the entries `entsRO`; the read states `readStatesPts`, their contexts bytes (D6); the hard
state `hsOpt` (`nil`, or `hardState()`'s fresh one the application may persist); the snapshot
`nil`.) (2026-10-16, stage R7a, D10: the soft state `softStateRO`, `nil` or its `Lead`/`RaftState`
read-only, which the server reads.) -/
def readyData (γ : NodeNames) (rd : Ready) (d ce es : List EntryM)
    (ms : List QMsg) (p p' : HardStateM) : IProp GF :=
  iprop(entsRO rd.CommittedEntries' ce ∗ isCommitted γ.raft (d ++ ce) ∗
    entsRO rd.Entries' es ∗ appendRight γ.stor es ∗
    rd.Messages' ↦* ms.map QMsg.loc ∗
    ([∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st ∗ isRaftMsg γ.raft γ.id q.st ∗
      termLB γ.bud q.st.msg.Term') ∗
    ([∗list] q ∈ ms, rdCred γ.raft (if q.st.msg.Type' = MsgReadIndex then 1 else 0)) ∗
    -- (2026-10-19, D21 M6) each forwarded proposal's tickets (`stTks`)
    ([∗list] q ∈ ms, stTks γ.raft q.st) ∗
    (∃ sts : List ReadStateM, readStatesPts rd.ReadStates' sts ∗
      [∗list] st ∈ sts, readStateOk γ.raft st) ∗
    -- (D22 S-b) with its witness: a non-`nil` one is the node's hard state at the `Ready`, its
    -- term and commit index (`commitWit`), the commit index bounding the committed log handed out;
    -- (D22l) the witness of `prevHardSt` after the `Ready`, `p'` (`phsNext p h`, `p` the last
    -- non-empty one handed out, `RNState.phs`): a `nil` or empty one leaves it `p`
    (∃ h : HardStateM, hsOpt rd.HardState' h ∗ ⌜p' = phsNext p h⌝) ∗
    hsWit γ.raft p' (d ++ ce).length ∗
    -- (2026-10-16, stage R7a, D10) the soft state: `nil`, or `Lead`/`RaftState` read-only
    softStateRO rd.SoftState' ∗
    ⌜rd.Snapshot' = null⌝ ∗
    -- (2026-10-18, D19b stage 5) the indices handed out are within the log (`readyIdx`)
    readyIdx γ.raft d ce es)

/-- (D22 S-d4, 2026-10-21) The committed log handed out after a `Ready` that came after `d` with
the committed entries `ce`: `d ++ ce`, or, with a snapshot (the loan `l`), the committed log up to
the snapshot (`SnapLoan.dlv`; a snapshot `Ready` hands out no committed entries). -/
def dlvAfter (d ce : List EntryM) : Option SnapLoan → List EntryM
  | none => d ++ ce
  | some l => l.dlv

/-- (D22 S-d4) What `run` has handed the driver of the committed log: `RNState.delivered`, or while
a snapshot `Ready` is lent (`RNState.slent`) the committed log up to its snapshot, which `Advance`
makes `delivered` (`advRS`). -/
def rsDlv (rs : RNState) : List EntryM :=
  match rs.slent with
  | none => rs.delivered
  | some l => l.dlv

theorem rsDlv_none {rs : RNState} (h : rs.slent = none) : rsDlv rs = rs.delivered := by
  unfold rsDlv; rw [h]

/-- (D22 S-d4, 2026-10-21) **What a `Ready` with a snapshot gives the driver** (the loan `l`):
`readyData`'s messages, read states, hard and soft state, committed log `d ++ ce` (with `ce = []`)
and the entries `es` to append, and in place of the right to append them (and of `rd.Snapshot`
`nil`) the snapshot -- at a node that takes snapshots (`snapIn`, so outside the no-snapshot mode
and in the static mode: what a client that never delivers a `MsgSnap`, or is in the no-snapshot
or the dynamic mode, refutes, `readyDataL_none`) -- half of it (`ownSnapS l.ptr ½`, every pointer field set, `rdSnapOut`;
the node's queued acknowledgement shares the pointer), the committed log up to it (`isCommitted
l.dlv`, `LoanOut`: `|l.dlv|` its index, extending `d`), the storage itself (`readyOut`: nothing
pending, at the loan's floor) and the snapshot's certificate in the storage's registry. The
application runs `ApplySnapshot` then `Append(es)` on the storage and gives it back with its half
of the snapshot at `Advance` (`advReceipt`, `snapReceipt`). -/
def readySnapData (γ : NodeNames) (rd : Ready) (d ce es : List EntryM)
    (ms : List QMsg) (p p' : HardStateM) (l : SnapLoan) : IProp GF :=
  iprop(entsRO rd.CommittedEntries' ce ∗ isCommitted γ.raft (d ++ ce) ∗
    entsRO rd.Entries' es ∗
    rd.Messages' ↦* ms.map QMsg.loc ∗
    ([∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st ∗ isRaftMsg γ.raft γ.id q.st ∗
      termLB γ.bud q.st.msg.Term') ∗
    ([∗list] q ∈ ms, rdCred γ.raft (if q.st.msg.Type' = MsgReadIndex then 1 else 0)) ∗
    ([∗list] q ∈ ms, stTks γ.raft q.st) ∗
    (∃ sts : List ReadStateM, readStatesPts rd.ReadStates' sts ∗
      [∗list] st ∈ sts, readStateOk γ.raft st) ∗
    (∃ h : HardStateM, hsOpt rd.HardState' h ∗ ⌜p' = phsNext p h⌝) ∗
    hsWit γ.raft p' (d ++ ce).length ∗
    softStateRO rd.SoftState' ∗
    readyIdx γ.raft d ce es ∗
    -- the snapshot, at a node that takes snapshots
    ⌜γ.snapIn = true ∧ γ.raft.reNoSnap = false ∧ γ.mode = .static⌝ ∗
    -- (D22 S-d4 item 4) every pointer field set: what `MemoryStorage.ApplySnapshot` takes
    ownSnapS l.ptr (DFrac.own (1 : Qp).half) l.snap ∗ isCommitted γ.raft l.dlv ∗
    -- (2026-10-26, D22 J2, R-loc) the snapshot local to the node (`snapLocal`: for a server, its
    -- index saved in the member's snapshot directory, which `snapDirInv` turns into its file)
    snapLocal γ.raft γ.id l.snap.Metadata'.Index' ∗
    ⌜l.ptr = rd.Snapshot' ∧ ce = [] ∧ d <+: l.dlv ∧
      -- (D22 S-r, 2026-10-21) past the committed log handed out before
      d.length < l.dlv.length ∧
      l.dlv.length = (uint.Z l.snap.Metadata'.Index').toNat ∧
      0 < uint.Z l.snap.Metadata'.Index' ∧ uint.Z l.snap.Metadata'.Index' < 2^61 ∧
      uint.Z l.fl ≤ uint.Z l.snap.Metadata'.Index' ∧ LogIndicesOk (snapId l.snap) es⌝ ∗
    readyOut γ.stor es (some l))

/-- (D22 S-d4) A `Ready`'s data, with or without a snapshot (`L`). -/
def readyDataL (γ : NodeNames) (rd : Ready) (d ce es : List EntryM)
    (ms : List QMsg) (p p' : HardStateM) : Option SnapLoan → IProp GF
  | none => readyData γ rd d ce es ms p p'
  | some l => readySnapData γ rd d ce es ms p p' l

/-- (D22 S-d4) A client that cannot be handed a snapshot -- one in raft's no-snapshot mode, in the
dynamic mode, or at a node that takes no `MsgSnap` (`snapIn` off) -- gets `readyData` as before. -/
theorem readyDataL_none (γ : NodeNames) (rd : Ready) (d ce es : List EntryM)
    (ms : List QMsg) (p p' : HardStateM) (L : Option SnapLoan)
    (H : γ.raft.reNoSnap = true ∨ γ.mode.isDyn = true ∨ γ.snapIn = false) :
    readyDataL (GF := GF) γ rd d ce es ms p p' L ⊢ ⌜L = none⌝ ∗ readyData γ rd d ce es ms p p' := by
  cases L with
  | none =>
    simp only [readyDataL]
    iintro Hd
    isplitr
    · ipureintro; first | rfl | trivial
    iexact Hd
  | some l =>
    simp only [readyDataL, readySnapData]
    iintro Hd
    icases Hd with ⟨-, -, -, -, -, -, -, -, -, -, -, -, %Hs, -⟩
    exfalso
    obtain ⟨H1, H2, H3⟩ := Hs
    rcases H with h | h | h
    · rw [h] at H2; cases H2
    · rw [H3] at h; cases h
    · rw [h] at H1; cases H1

/-- A `Ready` on `readyc` (see the file header): `run`'s half of `dlv` at `d`, the other half
of its record, and the data. (D22 S-d4, 2026-10-21) The record has the `Ready`'s snapshot, if any
(the loan `L`, `RNState.slent`), so that `run` recognizes its own loan at `Advance`; the lower bound
is of the committed log handed out after the `Ready` (`dlvAfter`). -/
@[no_expose] def readyP (γ : NodeNames) (rd : Ready) : IProp GF :=
  iprop(∃ (d ce es : List EntryM) (ms : List QMsg) (p p' : HardStateM) (L : Option SnapLoan),
    dghostVar γ.dlv (DFrac.own (1 : Qp).half) (d, p) ∗
    dghostVar γ.rof (DFrac.own (1 : Qp).half) (d, ce, es, p', L) ∗
    readyDataL γ rd d ce es ms p p' L ∗
    -- (2026-10-15, stage N) the committed log handed out, a lower bound
    monoListLbOwn γ.dlm (dlvAfter d ce L))

/-- (D22 S-d4) `readyP` for a client that cannot be handed a snapshot (`readyDataL_none`): as until
then, the record at no loan. -/
theorem readyP_none (γ : NodeNames) (rd : Ready)
    (H : γ.raft.reNoSnap = true ∨ γ.mode.isDyn = true ∨ γ.snapIn = false) :
    readyP (GF := GF) γ rd ⊢
      ∃ (d ce es : List EntryM) (ms : List QMsg) (p p' : HardStateM),
        dghostVar γ.dlv (DFrac.own (1 : Qp).half) (d, p) ∗
        dghostVar γ.rof (DFrac.own (1 : Qp).half) (d, ce, es, p', (none : Option SnapLoan)) ∗
        readyData γ rd d ce es ms p p' ∗ monoListLbOwn γ.dlm (d ++ ce) := by
  iintro HP
  unfold readyP
  icases HP with ⟨%d, %ce, %es, %ms, %p, %p', %L, Hd, Hrof, Hdata, #Hlb⟩
  icases readyDataL_none γ rd d ce es ms p p' L H $$ Hdata with ⟨%HL, Hdata⟩
  subst HL
  iexists d, ce, es, ms, p, p'
  rw [show d ++ ce = dlvAfter d ce none from rfl]
  iframe Hd Hrof Hdata Hlb

/-- (D22 S-d4) The driver's receipt at `Advance` for the `Ready`'s storage hand-out: of the append
of its entries (`appendReceipt`), or after a snapshot `Ready` the storage at the snapshot and the
half of the snapshot (`snapReceipt`, which `RawNode.Advance` takes, `loanRet`). -/
def advReceipt (st : Storage) (es : List EntryM) : Option SnapLoan → IProp GF
  | none => appendReceipt st es
  | some l => snapReceipt st l es

/-- An `Advance` on `advancec`: a `dlv` half after the last `Ready`, `run`'s record back,
and the receipt of the append of the `Ready`'s entries. (D22 S-d4, 2026-10-21) For the `Ready`'s
loan `L`: the committed log handed out after it (`dlvAfter`), and the receipt for it
(`advReceipt`). -/
@[no_expose] def advanceP (γ : NodeNames) (L : Option SnapLoan) : IProp GF :=
  iprop(∃ (d ce es : List EntryM) (p' : HardStateM),
    dghostVar γ.dlv (DFrac.own (1 : Qp).half) (dlvAfter d ce L, p') ∗
    dghostVar γ.rof (DFrac.own (1 : Qp).half) (d, ce, es, p', L) ∗ advReceipt γ.stor es L ∗
    -- (2026-10-15, stage N) **A1**, in the dynamic mode: no conf entry of the committed log
    -- handed out past the driver's configuration index `ca` (a lower bound of `run`'s)
    ∃ ca : Nat, monoNatLbOwn γ.cam ca ∗
      ⌜γ.mode.isDyn = true → NoConfIn (dlvAfter d ce L) ca (dlvAfter d ce L).length⌝)

/-- (D22 S-d4) The driver's request at `advancec` (`NodeNames.req`): the floor at least the
committed log it was handed (`some`), or after a snapshot `Ready` nothing (`none`): the storage was
the application's, and `run` raises no floor. -/
def reqOf (L : Option SnapLoan) (ds : List EntryM) : Option Nat :=
  match L with
  | none => some ds.length
  | some _ => none

/-- (D22 S-d4) What `run` answers the request with (`advInv`'s `RcvCommit`, `node.Advance`'s
post): for `some k` the floor's witness at `k` (D22 S-d4 item 3: also when a snapshot was restored
since the `Ready`, `StorExtOk`), for `none` nothing. -/
def reqWit (γ : NodeNames) : Option Nat → IProp GF
  | none => iprop(True)
  | some k => iprop(∃ x : w64, storFloor γ.stor x ∗ ⌜(k : Int) ≤ uint.Z x⌝)

instance reqWit_persistent (γ : NodeNames) (q : Option Nat) :
    Persistent (reqWit (GF := GF) γ q) := by
  cases q <;> unfold reqWit <;> infer_instance

/-- (D22 S-d4) The floor's witness after a `Ready` without a snapshot. (Until D22 S-d4 item 3 it
needed a client that cannot be handed a snapshot, `H`, now unused.) -/
theorem reqWit_none (γ : NodeNames) (ds : List EntryM)
    (_H : γ.raft.reNoSnap = true ∨ γ.mode.isDyn = true ∨ γ.snapIn = false) :
    reqWit (GF := GF) γ (reqOf none ds) ⊢
      ∃ x : w64, storFloor γ.stor x ∗ ⌜(ds.length : Int) ≤ uint.Z x⌝ := by
  iintro Hw
  unfold reqOf reqWit
  iexact Hw

/-- The tick channel: one credit per buffered tick. -/
@[no_expose] def tickInv (γ : NodeNames) : IProp GF :=
  iprop(∃ l : List Unit, ownChan γ.tick Unit (.Buffered l) ∗ tickCred γ.bud l.length)

/-- The committed log handed out so far is at least `ds` (2026-10-15, stage N; persistent): what
the driver knows of `run`'s, for a conf change's entry. -/
@[no_expose] def dlvLb (γ : NodeNames) (ds : List EntryM) : IProp GF :=
  monoListLbOwn γ.dlm ds

instance dlvLb_persistent (γ : NodeNames) (ds : List EntryM) :
    Persistent (dlvLb (GF := GF) γ ds) := by
  unfold dlvLb; infer_instance

/-- The driver's view of the configuration (2026-10-15, stage N): the configuration index `ca`
and the configuration `cfg` as of the last conf change it applied (`node.ApplyConfChange`;
`cap`'s half, a lower bound of `cam`), and the answer slot `ccq`, whole. `RestartNode` hands it
out at `0` and the initial configuration; in the static mode it never moves. -/
@[no_expose] def nodeCfg (γ : NodeNames) (ca : Nat) (cfg : CCState) : IProp GF :=
  iprop(dghostVar γ.cap (DFrac.own (1 : Qp).half) (ca, cfg) ∗
    (∃ x : Nat × CCState, dghostVar γ.ccq (DFrac.own (1 : Qp).half) x ∗
      dghostVar γ.ccq (DFrac.own (1 : Qp).half) x) ∗ monoNatLbOwn γ.cam ca)

/-- `run`'s side of what it shares with the driver about the configuration (2026-10-15, stage
N): the node's mode is `γ.mode`; the authority of the committed log handed out (`dlm`); the
configuration as of the last applied conf change, `(ca, rs.cfg)` (`cap`'s half, `cam`'s
authority at `ca`); `Advance` may have moved the configuration index past `ca`, over no conf
entry. (D22 S-d4, 2026-10-21) A node that takes snapshots (`snapIn`) is outside the no-snapshot
mode and in the static mode; one that does not has no snapshot pending or lent (from D22 S-c to
S-d4 none at all); while a snapshot `Ready` is lent the committed log handed out is the loan's
(`rsDlv`), which extends `delivered`. -/
@[no_expose] def runCfg (γ : NodeNames) (rs : RNState) : IProp GF :=
  iprop(⌜rs.mode = γ.mode ∧ rs.capplied ≤ rs.delivered.length ∧
      -- (D19i part 1) the floor not raised past `applied` (`RNState.flw`): `run` raises it only
      -- in its `advancec` arm, right before `Advance`
      rs.flw = false ∧
      -- (D22 S-d4) no snapshot pending (`RNState.psnap`) or lent (`RNState.slent`) at a node that
      -- takes none (until then, from D22 S-c, at any node)
      (γ.snapIn = false → rs.psnap = false ∧ rs.slent = none) ∧
      (γ.snapIn = true → γ.raft.reNoSnap = false ∧ γ.mode = .static) ∧
      (∀ l, rs.slent = some l → rs.delivered <+: l.dlv)⌝ ∗
    monoListAuthOwn γ.dlm 1 (rsDlv rs) ∗
    ∃ ca : Nat, dghostVar γ.cap (DFrac.own (1 : Qp).half) (ca, rs.cfg) ∗
      monoNatAuthOwn γ.cam 1 ca ∗ ⌜ca ≤ rs.capplied ∧ NoConfIn rs.delivered ca rs.capplied⌝)

/-- (D22 S-d4) `runCfg` reads only these fields of the node's state. -/
theorem runCfg_congr (γ : NodeNames) {rs rs' : RNState} (hm : rs'.mode = rs.mode)
    (hc : rs'.capplied = rs.capplied) (hd : rs'.delivered = rs.delivered) (hf : rs'.flw = rs.flw)
    (hp : rs'.psnap = rs.psnap) (hs : rs'.slent = rs.slent) (hcfg : rs'.cfg = rs.cfg) :
    runCfg (GF := GF) γ rs ⊢ runCfg γ rs' := by
  unfold runCfg rsDlv
  rw [hm, hc, hd, hf, hp, hs, hcfg]

/-! ### `advancec` (D19i part 1): the floor raised at the rendezvous

`node.Advance` returns as soon as `run` takes its send, before `run`'s `rn.Advance` moves
`applied`, and the application may then compact its storage up to what it applied. So the floor
is raised (`ownRawNode_raise_floor`, to `applying`: the committed log handed out) at the
rendezvous itself, and the floor's witness goes to the sender. `advancec` has its own protocol
over the channel's states (`advInv`), in place of a handshake's fixed reply:

- `run` first (`RcvPending`): `run` deposits its node (`advDep`), the means to raise the floor;
  the sender, meeting it (`RcvPending → SndCommit`), absorbs its append receipt, raises the
  floor, checks the committed log `run` handed out against its own lower bound (`dlvLb`), keeps
  the witness, and leaves the raised node (`advRet`) for `run`, which takes it back when its
  receive completes (`SndCommit → Idle`);
- the sender first (`SndPending`): its payload and its request (`req`, the length of its log)
  wait; `run`, meeting it (`SndPending → RcvCommit`), raises the floor itself and leaves the
  witness against the request, which the sender takes when its send completes.

(D22 S-d4, 2026-10-21) After a snapshot `Ready` (the loan `L`, in `rof`) the receipt is the storage
at the snapshot (`snapReceipt`), which `RawNode.Advance` takes: it passes to `run` in `advRet`
(`loanRet`), nothing is absorbed, no floor raised, and the request is `none` (`reqOf`). After one
without, the receipt is absorbed and the floor raised, also when a snapshot was restored since
(`RNState.psnap`; D22 S-d4 item 3, `StorExtOk`).

In Perennial's channel model a receiver's `RcvPending` is entered only by the sender that meets
it, in the same step as `SndCommit` (`wp_TrySend_blocking`'s `RcvWait` case; a waiting offer a
`select` rescinds never reaches the logical state), so a node deposited at `RcvPending` is not
taken back by a `select` that fires another case. -/

/-- `run`'s node at the `advancec` rendezvous, before the floor is raised: `runMid_busy`'s.
(D22 S-d4) Its record names the loan (`rs.slent`). -/
@[no_expose] def advDep (γ : NodeNames) (rn : Loc) (id : w64) : IProp GF :=
  iprop(∃ (rs : RNState) (d ce : List EntryM), ownRawNode γ.raft rn id rs ∗
    termLB γ.bud rs.tc ∗ runCfg γ rs ∗
    dghostVar γ.rof (DFrac.own (1 : Qp).half) (d, ce, rs.unpersisted, rs.phs, rs.slent) ∗
    ⌜rs.storage = γ.stor ∧ rs.unst = false ∧ rs.delivered = d ++ ce⌝)

/-- `run`'s node after the rendezvous: the `Ready`'s entries appended, the floor raised
(`flw`), the driver's payload in (its `dlv` half, `rof` back whole, A1's lower bound).
(D22 S-d4, 2026-10-21) Or, after a snapshot `Ready`, the receipt for its loan (`loanRet`), the
entries not appended here, and the floor not raised; `dlv` at the committed log handed out
(`rsDlv`, the loan's). -/
@[no_expose] def advRet (γ : NodeNames) (rn : Loc) (id : w64) : IProp GF :=
  iprop(∃ (rs : RNState) (ca_d : Nat), ownRawNode γ.raft rn id rs ∗
    termLB γ.bud rs.tc ∗ runCfg γ { rs with flw := false } ∗
    dghostVar γ.dlv (DFrac.own (1 : Qp).half) (rsDlv rs, rs.phs) ∗
    (∃ x : List EntryM × List EntryM × List EntryM × HardStateM × Option SnapLoan,
      dghostVar γ.rof (DFrac.own (1 : Qp).half) x ∗ dghostVar γ.rof (DFrac.own (1 : Qp).half) x) ∗
    monoNatLbOwn γ.cam ca_d ∗ loanRet rs ∗
    ⌜rs.storage = γ.stor ∧ rs.unst = false ∧ (rs.slent = none → rs.unpersisted = []) ∧
      (γ.mode.isDyn = true → NoConfIn rs.delivered ca_d rs.delivered.length)⌝)

/-- The `advancec` protocol (see above). (D22 S-d4) The driver's payload for its `Ready`'s loan
`L`, its request `reqOf L ds`, `run`'s answer `reqWit`. -/
@[no_expose] def advInv (γ : NodeNames) (rn : Loc) (id : w64) : IProp GF :=
  iprop(∃ s, "Hch" ∷ ownChan γ.advancec Unit s ∗
    (match s with
     | .Idle => iprop(True)
     | .SndPending _ => iprop(∃ L : Option SnapLoan, advanceP γ L ∗ ∃ ds : List EntryM,
         dghostVar γ.req (DFrac.own (1 : Qp).half) (reqOf L ds) ∗ dlvLb γ ds)
     | .RcvPending => advDep γ rn id
     | .SndCommit _ => advRet γ rn id
     | .RcvCommit => iprop(∃ q : Option Nat, dghostVar γ.req (DFrac.own (1 : Qp).half) q ∗
         reqWit γ q)
     | _ => iprop(False)))

def advN : Namespace := nroot.@"raft_advancec"

/-- `advancec` (D19i part 1): the channel and its protocol. -/
@[no_expose] def isAdvChan (γ : NodeNames) (rn : Loc) (id : w64) (ch : Loc) : IProp GF :=
  iprop(isChan ch γ.advancec Unit ∗ inv advN (advInv γ rn id))

instance isAdvChan_persistent (γ : NodeNames) (rn : Loc) (id : w64) (ch : Loc) :
    Persistent (isAdvChan (GF := GF) γ rn id ch) := by
  unfold isAdvChan; infer_instance

/-- A conf change on `confc` (2026-10-13, `node.ApplyConfChange`), its changes read-only: in the
static mode, one that keeps the voters and only drops learners (`CCShrink`,
`RawNode.ApplyConfChange`'s static scope); (2026-10-15, stage N) in the dynamic mode, the driver's
view of the configuration (`cap`'s half at `(ca, cfg)`), the answer it expects (`ccq`'s half at
`(k + 1, cs')`), a lower bound `ds` of the committed log handed out, and that the change is that
of the next conf entry of `ds`, at position `k` (`DynCCPreOp`). (2026-10-16, stage R5: a
`*pb.ConfChangeV2` at `v`, read-only (`ownCCV2 v □ ccm`, R1), its content `ccm`.) -/
@[no_expose] def confcP (γ : NodeNames) (v : Loc) : IProp GF :=
  iprop(∃ ccm : CCV2M, ownCCV2 v DFrac.discard ccm ∗
    ((⌜γ.mode = .static ∧ CCShrink γ.raft.reCfg ccm.transition ccm.changes⌝) ∨
     (∃ (ds : List EntryM) (ca : Nat) (cfg : CCState) (k : Nat) (e : EntryM)
        (cs' : CCState),
        ⌜γ.mode.isDyn = true ∧ ∀ dec c0 h0 h1, γ.mode = .dyn dec c0 h0 h1 →
          DynCCPreOp dec ds ca cfg (ccm.transition, ccm.changes) k e cs'⌝ ∗
        monoListLbOwn γ.dlm ds ∗ dghostVar γ.cap (DFrac.own (1 : Qp).half) (ca, cfg) ∗
        dghostVar γ.ccq (DFrac.own (1 : Qp).half) (k + 1, cs'))))

/-- A `ConfState`'s four lists are a configuration's (2026-10-15, stage N). (2026-10-16, stage
R5: pure, over the conf state's record; until then the read-only slices of a Goose value.) -/
def confstateOk (c : ConfStateM) (cfg : CfgM) : Prop :=
  c.Voters' ≡ₚ elements cfg.incoming ∧ c.VotersOutgoing' ≡ₚ elements cfg.outgoing ∧
    c.Learners' ≡ₚ elements cfg.learners ∧ c.LearnersNext' ≡ₚ elements cfg.learnersNext ∧
    c.AutoLeave' = cfg.autoLeave

/-- The static mode's answer (2026-10-13): the voters and the learners (none of them a voter),
and no joint configuration. (2026-10-16, stage R5: pure, over the record.) -/
def confstateS (γ : NodeNames) (c : ConfStateM) : Prop :=
  c.Voters' ≡ₚ elements γ.raft.reCfg ∧ (∀ k ∈ c.Learners', k ∉ γ.raft.reCfg) ∧
    c.VotersOutgoing' = [] ∧ c.LearnersNext' = [] ∧ c.AutoLeave' = false

/-- The `ConfState` on `confstatec`: in the static mode, `confstateS`; (2026-10-15, stage N) in
the dynamic mode, the driver's view of the configuration back (`cap`'s half), the answer slot's
half at the same value (the driver's other half names the answer it expects) with the index's
lower bound, and the `ConfState` of the configuration. (2026-10-16, stage R5: the fresh
`*pb.ConfState` at `cs` `applyConfChange` returns, owned, `csPts cs 1 c true`.) -/
@[no_expose] def confstateP (γ : NodeNames) (cs : Loc) : IProp GF :=
  iprop(∃ c : ConfStateM, csPts cs (DFrac.own 1) c true ∗
    ((⌜γ.mode = .static ∧ confstateS γ c⌝) ∨
     (⌜γ.mode.isDyn = true⌝ ∗ ∃ v : Nat × CCState,
      dghostVar γ.cap (DFrac.own (1 : Qp).half) v ∗ dghostVar γ.ccq (DFrac.own (1 : Qp).half) v ∗
      monoNatLbOwn γ.cam v.1 ∗ ⌜confstateOk c v.2.cfg⌝)))

/-- See the file header. -/
@[no_expose] def isNode (γ : NodeNames) (id : w64) (n : Loc) : IProp GF :=
  iprop(∃ (nv : node) (r : Loc) (lok : GoInterfaceOk),
    "#Hn" ∷ n ↦□ nv ∗
    "#Hrnraft" ∷ nv.rn'.[RawNode, go!"raft"] ↦□ r ∗
    "#Hrid" ∷ r.[raft, go!"id"] ↦□ id ∗
    "#Hrlogger" ∷ r.[raft, go!"logger"] ↦□ (interface.ok lok : GoInterface) ∗
    "#Hlogger" ∷ isLogger lok ∗
    "#Hpropc" ∷ isHandshake γ.propc nv.propc' (propP γ) iprop(True) ∗
    "#Hrecvc" ∷ isHandshake γ.recvc nv.recvc' (netP γ id) iprop(True) ∗
    "#Hconfc" ∷ isHandshake γ.confc nv.confc' (confcP γ) iprop(True) ∗
    "#Hconfstatec" ∷ isHandshake γ.confstatec nv.confstatec' (confstateP γ) iprop(True) ∗
    "#Hreadyc" ∷ isHandshake γ.readyc nv.readyc' (readyP γ) iprop(True) ∗
    "#Hadvancec" ∷ isAdvChan γ nv.rn' id nv.advancec' ∗
    "#Hdone" ∷ isHandshake γ.done nv.done' (fun (_ : Unit) => iprop(False)) iprop(True) ∗
    "#Hstop" ∷ isHandshake γ.stop nv.stop' (fun (_ : Unit) => iprop(False)) iprop(True) ∗
    "#Hstatus" ∷ isHandshake γ.status nv.status' (fun (_ : GoChan) => iprop(False)) iprop(True) ∗
    "#Htickc" ∷ isChan nv.tickc' γ.tick Unit ∗
    "#Htickinv" ∷ inv tickN (tickInv γ) ∗
    "#Hbud" ∷ inv budgetN (budgetInv γ.bud) ∗
    -- the cluster's commit invariant (2026-10-10; (2026-10-16, stage R5, D6) the proposed
    -- slices' invariant `propDataInv` is gone)
    "#Hcinv" ∷ raftCommitInv γ.raft ∗
    -- (2026-10-22, D38a) the names' id is the node's
    "%Hgid" ∷ ⌜γ.id = id⌝)

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 4096 in
instance isNode_persistent (γ : NodeNames) (id : w64) (n : Loc) :
    Persistent (isNode (GF := GF) γ id n) := by
  unfold isNode; infer_instance

/-- The driver's token: the committed log it was handed so far is `ds`; (D22l) the hard state of
the last `Ready` it was handed with a non-empty one is `p` (`RNState.phs`; zero at the start). -/
@[no_expose] def nodeDriver (γ : NodeNames) (id : w64) (n : Loc) (ds : List EntryM) (p : HardStateM) :
    IProp GF :=
  iprop(isNode γ id n ∗ dghostVar γ.dlv (DFrac.own (1 : Qp).half) (ds, p) ∗ dlvLb γ ds ∗
    -- (D19i part 1) the request on `advancec` (`advInv`)
    ∃ q : Option Nat, dghostVar γ.req (DFrac.own (1 : Qp).half) q ∗
      dghostVar γ.req (DFrac.own (1 : Qp).half) q)

/-- The driver with a `Ready` in hand: it was handed the committed log `ds` (the last
`Ready`'s included) and must append `es` (the last `Ready`'s entries) before `Advance`; (D22l)
`p'` is `prevHardSt` after the `Ready` (`readyData`'s). (D22 S-d4, 2026-10-21) `L` the `Ready`'s
snapshot, if any (its loan, `run`'s record names it): `ds` is then the committed log up to the
snapshot (`dlvAfter`), and the storage is the application's until `Advance` (`advReceipt`). -/
@[no_expose] def nodeDriverBusy (γ : NodeNames) (id : w64) (n : Loc) (ds es : List EntryM)
    (p' : HardStateM) (L : Option SnapLoan := none) : IProp GF :=
  iprop(isNode γ id n ∗ dlvLb γ ds ∗
    ∃ (d ce : List EntryM) (p : HardStateM), dghostVar γ.dlv (DFrac.own (1 : Qp).half) (d, p) ∗
      dghostVar γ.dlv (DFrac.own (1 : Qp).half) (d, p) ∗
      dghostVar γ.rof (DFrac.own (1 : Qp).half) (d, ce, es, p', L) ∗ ⌜ds = dlvAfter d ce L⌝ ∗
    ∃ q : Option Nat, dghostVar γ.req (DFrac.own (1 : Qp).half) q ∗
      dghostVar γ.req (DFrac.own (1 : Qp).half) q)

/-- `readyc`, as the driver sees it (`Node.Ready()`'s result). -/
def isReadyChan (γ : NodeNames) (ch : Loc) : IProp GF :=
  isHandshake γ.readyc ch (readyP γ) iprop(True)

instance isReadyChan_persistent (γ : NodeNames) (ch : Loc) :
    Persistent (isReadyChan (GF := GF) γ ch) := by
  unfold isReadyChan; infer_instance

/-- **Receiving a `Ready`** (the driver's loop, `for rd := range node.Ready()`): with the
driver's token, the `Ready`'s data for the committed log handed out so far, and the token
busy with it. The channel is never closed. (D22 S-d4, 2026-10-21) With the `Ready`'s snapshot, if
any (`L`, `readyDataL`): the committed log handed out is then the snapshot's (`dlvAfter`). -/
theorem node_ready_receive (γ : NodeNames) (id : w64) (n ch : Loc) (ds : List EntryM)
    (p : HardStateM) :
    {{ isReadyChan γ ch ∗ nodeDriver (GF := GF) γ id n ds p }}
      (App (Val (chan.receive Ready.ty)) (Val #ch))
    {{ (rd : Ready), RET (PairV #rd #true);
        ∃ (ce es : List EntryM) (ms : List QMsg) (p' : HardStateM) (L : Option SnapLoan),
          readyDataL γ rd ds ce es ms p p' L ∗
          nodeDriverBusy γ id n (dlvAfter ds ce L) es p' L }} := by
  iintro %Φ ⟨#Hrc, Hdrv⟩ HΦ
  unfold nodeDriver
  icases Hdrv with ⟨#Hnode, Hds, -, Hreq⟩
  unfold isReadyChan
  iapply wp_handshake_receive (t := Ready.ty) γ.readyc ch (readyP γ) iprop(True) $$ [] [HΦ Hds Hreq]
  · iframe Hrc
  iintro %rd
  iintro !> HP
  unfold readyP
  icases HP with ⟨%d, %ce, %es, %ms, %p0, %p', %L, Hd, Hrof, Hdata, #Hlb⟩
  ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hd Hds
  cases Heq
  iapply HΦ
  iexists ce, es, ms, p', L
  iframe Hdata
  unfold nodeDriverBusy
  iframe Hnode
  isplitr
  · unfold dlvLb; iexact Hlb
  iexists ds, ce, p
  iframe Hd Hds Hrof Hreq
  ipureintro; rfl

/-- (D22 S-d4) **Receiving a `Ready`**, for a client that cannot be handed a snapshot (in raft's
no-snapshot mode, in the dynamic mode, or at a node that takes no `MsgSnap`): as until D22 S-d4,
`readyData` and the token busy with no loan (`readyDataL_none`). -/
theorem node_ready_receive_ns (γ : NodeNames) (id : w64) (n ch : Loc) (ds : List EntryM)
    (p : HardStateM)
    (H : γ.raft.reNoSnap = true ∨ γ.mode.isDyn = true ∨ γ.snapIn = false) :
    {{ isReadyChan γ ch ∗ nodeDriver (GF := GF) γ id n ds p }}
      (App (Val (chan.receive Ready.ty)) (Val #ch))
    {{ (rd : Ready), RET (PairV #rd #true);
        ∃ (ce es : List EntryM) (ms : List QMsg) (p' : HardStateM),
          readyData γ rd ds ce es ms p p' ∗ nodeDriverBusy γ id n (ds ++ ce) es p' }} := by
  iintro %Φ Hpre HΦ
  iapply node_ready_receive γ id n ch ds p $$ Hpre
  iintro !> %rd ⟨%ce, %es, %ms, %p', %L, Hdata, Hbusy⟩
  icases readyDataL_none γ rd ds ce es ms p p' L H $$ Hdata with ⟨%HL, Hdata⟩
  subst HL
  iapply HΦ
  iexists ce, es, ms, p'
  rw [show ds ++ ce = dlvAfter ds ce none from rfl]
  iframe Hdata Hbusy

theorem nodeDriverBusy_lb (γ : NodeNames) (id : w64) (n : Loc) (ds es : List EntryM)
    (p' : HardStateM) (L : Option SnapLoan := none) :
    ⊢ nodeDriverBusy (GF := GF) γ id n ds es p' L -∗ dlvLb γ ds := by
  iintro H
  unfold nodeDriverBusy
  icases H with ⟨-, $, -⟩

/-! ### Laws of the sealed node predicates (2026-10-26, raft's signature, stage 1)

`isNode`, `nodeDriver`, `nodeDriverBusy`, `readyP` and the channel protocols are `@[no_expose]`:
a client of raft does not see their bodies (`Spec/go_etcd_io/raft/v3/Api.lean`). What clients
need of them is stated here, in the API's vocabulary. -/

/-- The node's names are of its id (`isNode`'s `Hgid`). -/
theorem isNode_id (γ : NodeNames) (id : w64) (n : Loc) :
    isNode (GF := GF) γ id n ⊢ ⌜γ.id = id⌝ := by
  iintro #Hnode
  unfold isNode
  icases Hnode with ⟨%nv, %r, %lok, #Hnode⟩
  iNamed Hnode
  ipureintro; exact Hgid

/-- The cluster's commit invariant, from a node (what the client's ghost lemmas over the
committed log, `committed_data`, `prop_register`, `read_deposit`, open). -/
theorem isNode_commitInv (γ : NodeNames) (id : w64) (n : Loc) :
    isNode (GF := GF) γ id n ⊢ raftCommitInv γ.raft := by
  iintro #Hnode
  unfold isNode
  icases Hnode with ⟨%nv, %r, %lok, #Hnode⟩
  iNamed Hnode
  iexact Hcinv

/-- The driver's token holds the node. -/
theorem nodeDriver_isNode (γ : NodeNames) (id : w64) (n : Loc) (ds : List EntryM)
    (p : HardStateM) :
    nodeDriver (GF := GF) γ id n ds p ⊢ nodeDriver γ id n ds p ∗ isNode γ id n := by
  iintro Hdrv
  unfold nodeDriver
  icases Hdrv with ⟨#Hnode, Hds, #Hlb, Hreq⟩
  iframe Hnode Hds Hlb Hreq

/-- **Taking a `Ready`'s payload** (`readyP`, what a receive on the `Ready` channel gives,
`isReadyChan`): with the driver's token at the committed log handed out `ds`, the `Ready`'s data
for `ds`, the token busy with it, and the committed log handed out after it. What
`node_ready_receive` does after the receive, for a client that receives in a `select`. -/
theorem readyP_take (γ : NodeNames) (id : w64) (n : Loc) (rd : Ready) (ds : List EntryM)
    (p : HardStateM) :
    ⊢ readyP (GF := GF) γ rd -∗ nodeDriver γ id n ds p -∗
      ∃ (ce es : List EntryM) (ms : List QMsg) (p' : HardStateM) (L : Option SnapLoan),
        readyDataL γ rd ds ce es ms p p' L ∗ nodeDriverBusy γ id n (dlvAfter ds ce L) es p' L ∗
        dlvLb γ (dlvAfter ds ce L) := by
  iintro HP Hdrv
  unfold nodeDriver
  icases Hdrv with ⟨#Hnode, Hds, -, Hreq⟩
  unfold readyP
  icases HP with ⟨%d, %ce, %es, %ms, %p0, %p', %L, Hd, Hrof, Hdata, #Hlb⟩
  ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hd Hds
  cases Heq
  iexists ce, es, ms, p', L
  iframe Hdata
  unfold nodeDriverBusy dlvLb
  iframe Hnode Hlb
  iexists ds, ce, p
  iframe Hd Hds Hrof Hreq
  ipureintro; rfl

/-- `readyP_take` for a client that cannot be handed a snapshot (`readyDataL_none`). -/
theorem readyP_take_ns (γ : NodeNames) (id : w64) (n : Loc) (rd : Ready) (ds : List EntryM)
    (p : HardStateM) (H : γ.raft.reNoSnap = true ∨ γ.mode.isDyn = true ∨ γ.snapIn = false) :
    ⊢ readyP (GF := GF) γ rd -∗ nodeDriver γ id n ds p -∗
      ∃ (ce es : List EntryM) (ms : List QMsg) (p' : HardStateM),
        readyData γ rd ds ce es ms p p' ∗ nodeDriverBusy γ id n (ds ++ ce) es p' ∗
        dlvLb γ (ds ++ ce) := by
  iintro HP Hdrv
  icases readyP_take γ id n rd ds p $$ HP Hdrv with ⟨%ce, %es, %ms, %p', %L, Hdata, Hbusy, #Hlb⟩
  icases readyDataL_none γ rd ds ce es ms p p' L H $$ Hdata with ⟨%HL, Hdata⟩
  subst HL
  iexists ce, es, ms, p'
  rw [show ds ++ ce = dlvAfter ds ce none from rfl]
  iframe Hdata Hbusy Hlb

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
variable [GooseExts] [GooseSemantics] [GooseInterp]
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

A data's registration with its result predicate (`node_prop_register`, the client's step before
proposing it), a proposal's ghost work before it leaves the node (`node_propose_ghost`: the
update deposited); and what the committed log's entries hold, for the application applying them
(`node_committed_data`, `node_entData_heap`). (2026-10-16, stage R5, D6: no proposed slices to
record, `propDataInv` gone.) -/

section props
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- What `Node.Propose` takes for its data `d` (2026-10-21): `d` registered with the result
predicate `Q` (`propIs`, from `node_prop_register`) and the client's atomic update for `d` and
`Q` (2026-10-14, stage R), which raft fires at most once (D21 M6: each proposal is appended
once, its ticket going with it). `d` may be proposed any number of times, each with its own
update. (Until 2026-10-21 the fresh token went with the first proposal, and a retry of the same
bytes needed `propMulti`.) -/
def propArg (γ : RaftNames) (d : List w8) (Q : List EntryM → IProp GF) : IProp GF :=
  iprop(propIs γ d Q ∗ propAu1 γ d Q)

-- (2026-10-16, stage R5, D6) `propDataInv_alloc`, `propData_register` and `propData_heap` are
-- gone with the proposed slices: an entry's data, a read context, is its bytes.

end props

section nodeprops
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A proposal's ghost work before it leaves the node (`Node.Propose`): its update deposited
(a first proposal), so that its entry carries its data (`entData`). (2026-10-16, stage R5, D6:
the entry `propEntryM data` holds the bytes, which must not be empty (`Hne`: an empty one would
be a leader's own entry); no slice to record.) -/
theorem node_propose_ghost (γ : NodeNames) (id : w64) (n : Loc)
    (data : List w8) (Q : List EntryM → IProp GF) (E : CoPset)
    (HE1 : ↑raftN ⊆ E) (Hne : data ≠ []) :
    ⊢ isNode γ id n -∗ propArg γ.raft data Q ={E}=∗
      propData γ.raft (propEntryM data) ∗ entTk γ.raft (propEntryM data) := by
  iintro #Hnode Harg
  open_node Hnode
  have Htk : entTk (GF := GF) γ.raft (propEntryM data) = propTk γ.raft data := by
    unfold entTk; rw [if_pos ⟨rfl, Hne⟩]; rfl
  rw [Htk]
  unfold propArg
  icases Harg with ⟨#Hpi, Hau⟩
  ihave #Hdep := propIs_deposited $$ Hpi
  imod prop_deposit γ.raft E data Q HE1 $$ Hcinv Hpi Hau with Htk
  imodintro
  iframe Htk
  unfold propData
  iexists some data
  unfold propDataIs
  isplitr
  · ipureintro; exact ⟨rfl, Hne, rfl⟩
  iexact Hdep

/-- **Registering `d` with `Q`, at the node** (2026-10-21; `prop_register`): what a client does,
once per data, before proposing it. -/
theorem node_prop_register (γ : NodeNames) (id : w64) (n : Loc) (d : List w8)
    (Q : List EntryM → IProp GF) (E : CoPset) (HE1 : ↑raftN ⊆ E) :
    ⊢ isNode γ id n -∗ propFresh γ.raft d ={E}=∗ propIs γ.raft d Q := by
  iintro #Hnode Hfr
  open_node Hnode
  iapply prop_register γ.raft E d Q HE1 $$ Hcinv Hfr

/-- A `ReadState`'s context and `readOk` of it (2026-10-13). A client that compares the bytes
with its own context's (its `readReq γ c Lc`) learns `readOk` of its read (`readOk_prefix`).
(2026-10-16, stage R5, D6: the context is the record's bytes; until then a slice, read through
the proposed slices' invariant.) -/
theorem node_readState_data (γ : NodeNames) (id : w64) (n : Loc) (st : ReadStateM) (E : CoPset) :
    ⊢ isNode (GF := GF) γ id n -∗ readStateOk γ.raft st ={E}=∗
      readOk γ.raft st.RequestCtx' st.Index' := by
  iintro #Hnode #Hst
  iunfold readStateOk at Hst
  icases Hst with ⟨%c, %Hc, #Hok⟩
  imodintro
  rw [Hc]
  iexact Hok

/-- The data of a committed log's entries. -/
theorem node_committed_data (γ : NodeNames) (id : w64) (n : Loc) (l : List EntryM)
    (E : CoPset) (HE : ↑raftN ⊆ E) :
    ⊢ isNode γ id n -∗ isCommitted γ.raft l ={E}=∗
      ∃ ods, [∗list] e;o ∈ l;ods, entDataIs (GF := GF) γ.raft e o := by
  iintro #Hnode #Hc
  open_node Hnode
  iapply committed_data γ.raft E l HE $$ Hcinv Hc

/-- Depositing a read (`read_deposit`), at the node (2026-10-14, stage R). -/
theorem node_read_deposit (γ : NodeNames) (id : w64) (n : Loc) (c : List w8)
    (Qr : List EntryM → IProp GF) (L0 : List EntryM) :
    ⊢ isNode γ id n -∗ rdFresh γ.raft c -∗ readAu γ.raft Qr -∗ isCommitted γ.raft L0 ={⊤}=∗
      ∃ Lc, ⌜L0 <+: Lc⌝ ∗ readReq γ.raft c Lc ∗ isRead γ.raft c Qr := by
  iintro #Hnode Hfr #Hau #HL0
  open_node Hnode
  iapply read_deposit γ.raft c Qr L0 $$ Hcinv Hfr Hau HL0

end nodeprops

end EtcdGrove
end Perennial
