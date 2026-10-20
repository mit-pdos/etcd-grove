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
  the receipt is for the entries it handed out.
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

public import Proof.go_etcd_io.raft.v3.InvRawnodeReady
-- (2026-10-16, stage R5) `netStepTypes`, `NetMsgOk`, `DynCCPreOp`, `propEntryM` are
-- `InvRawnode.lean`'s (until then `RawNode__Step`'s, `RawNode__Propose`'s,
-- `RawNode__ApplyConfChange`'s)
public import Perennial.Golang.Theory.Chan.Idioms.Handshake
public import Proof.go_etcd_io.etcd.cache.v3.Handoff
public import Perennial.Ghost.MonoNat
public import Proof.go_etcd_io.raft.v3.Protocol.Facts
public import Proof.go_etcd_io.raft.v3.InvApplyConf
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
variable [FfiSyntax]

-- (2026-10-16, stage R5) the instances for `raftpb.HardState`, `ConfState`,
-- `SnapshotMetadata`, `Snapshot`, `Message`, `ConfChangeV2` are gone: the channels carry
-- pointers to them.

instance msgWithResult_countable : Pos.Countable msgWithResult :=
  countableOfLeftInverse (fun m : msgWithResult => (m.m', m.result'))
    (fun p => ⟨p.1, p.2⟩) (fun _ => rfl)

instance ready_countable : Pos.Countable Ready :=
  countableOfLeftInverse
    (fun r : Ready => (r.SoftState', r.HardState', r.ReadStates', r.Entries', r.Snapshot',
      r.CommittedEntries', r.Messages', r.MustSync', r.WitnessMessages'))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2⟩) (fun _ => rfl)

/-- (2026-10-15, stage N) a configuration, for the run loop's configuration shared with the
driver (`NodeNames.cap`). -/
instance cfgM_countable : Pos.Countable CfgM :=
  countableOfLeftInverse
    (fun c : CfgM => (c.incoming, c.outgoing, c.learners, c.learnersNext, c.autoLeave, c.wit))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2⟩) (fun _ => rfl)

instance ccState_countable : Pos.Countable CCState :=
  countableOfLeftInverse (fun c : CCState => (c.cfg, c.prs)) (fun p => ⟨p.1, p.2⟩)
    (fun _ => rfl)

end countable

/-! ## The term budget -/

/-- Ghost names of a cluster's term budget (D19b, 2026-10-18: until then also the tick credits'
`Auth Nat`, `creds`; the credits are time receipts now). -/
structure BudgetNames where
  /-- the bound `M` on every term (a monotone nat) -/
  bound : GName

def budgetN : Namespace := nroot.@"raft_budget"


section budget
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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

instance tickCred_timeless (bud : BudgetNames) (n : Nat) :
    Timeless (tickCred (GF := GF) bud n) := by
  unfold tickCred; infer_instance

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
structure NodeNames [FfiSyntax] where
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
  /-- `run`'s record of its last `Ready` `(delivered, committed entries, entries)` -/
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
  while its offer waits (`advInv`) -/
  req : GName

def tickN : Namespace := nroot.@"raft_tick"

-- (2026-10-16, stage R5, D6) `propDataN`, the proposed slices' invariant's namespace, is gone.

section node
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
`raft.Step` takes a proposal, `msgIn ml 1`, its entries' slots owned.) -/
def fwdP (γ : NodeNames) (ml : Loc) : IProp GF :=
  iprop(∃ st : MsgSt, msgIn ml (DFrac.own 1) st ∗ ⌜st.msg.Type' = MsgProp⌝ ∗
    isMessage γ.raft (absMsg .propose st.msg st.ents) ∗
    -- (2026-10-19, D21 M6) its entries' tickets (`entTk`), which the leader consumes
    ([∗list] e ∈ st.ents, entTk γ.raft e))

/-- `err` is raft's package variable `ErrProposalDropped` (`raft.go`, an `errors.New` error),
a read-only global the package initializer sets to a non-`nil` error (`isInitialized`,
`Base.lean`); the shape of `errStopped` (`InvNodeCtx.lean`). -/
def errProposalDropped (err : GoInterface) : IProp GF :=
  iprop((globalAddr ErrProposalDropped ↦□ err : IProp GF) ∗ ⌜err ≠ interface.nil⌝)

instance errProposalDropped_persistent (err : GoInterface) :
    Persistent (errProposalDropped (GF := GF) err) := by
  unfold errProposalDropped; infer_instance

/-- **The error `run` answers a proposal with** (stage R7c, 2026-10-16): `raft.Step`'s for the
`MsgProp` (`raft__Step.lean`'s `"Herr"`), `nil` or `ErrProposalDropped` (`stepFollower`'s and
`stepCandidate`'s drop; `wp_rn_raft_Step_prop`), what the result channel's handoff promises
(`propP`) and `Propose` returns (`propErr`, `InvNodeCtx.lean`). -/
def stepErr (err : GoInterface) : IProp GF :=
  iprop(⌜err = interface.nil⌝ ∨ errProposalDropped err)

instance stepErr_persistent (err : GoInterface) : Persistent (stepErr (GF := GF) err) := by
  unfold stepErr; infer_instance

theorem stepErr_nil : ⊢ stepErr (GF := GF) interface.nil := by
  unfold stepErr
  ileft
  ipureintro; rfl

/-- A proposal on `propc`: the message `Propose` builds, with its one-entry batch owned,
the data read-only and its record (`entData`, 2026-10-10), and its result channel, of
which `run` is the producer (a `Handoff`: `run` sends the error, `stepErr`, and closes); or
(2026-10-10) a proposal forwarded by a peer (`Node.Step`), with no result channel.
(2026-10-16, stage R5: the message at `pm.m'`, owned (`msgIn`), holding `propMsgM` and the one
entry `propEntryM d`, D6: the data's bytes `d`. Stage R7c: the result channel's value is
`stepErr`; until then nothing was promised of it.) -/
def propP (γ : NodeNames) (pm : msgWithResult) : IProp GF :=
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
      -- request only outside the cluster's no-snapshot mode, where leader transfer is off
      ⌜(st.msg.Type' = MsgPreVote → γ.raft.reBoot ≠ []) ∧
        (st.msg.Type' = MsgTransferLeader → γ.raft.reNoSnap = false)⌝ ∗
      □ (∀ ty, ⌜mtypeOf st.msg.Type' = some ty⌝ -∗
        isMessage γ.raft (absMsg ty st.msg st.ents st.ctx)) ∗
      termLB γ.bud st.msg.Term' ∗
      rdCred γ.raft (if st.msg.Type' = MsgReadIndex then 1 else 0) ∗
      tickCred γ.bud (if st.msg.Type' = MsgTimeoutNow then 1 else 0))

/-- (2026-10-13) A local message on `recvc` with no entries, no context and no term (a
transfer request, `ForgetLeader`'s, a report): no credit (but empty ones), no protocol
fact. (2026-10-16, stage R5: over the message's state.) -/
theorem netP_local (γ : NodeNames) (id : w64) (ml : Loc) (st : MsgSt)
    (Hty : st.msg.Type' = MsgTransferLeader ∨ st.msg.Type' = MsgForgetLeader ∨
      st.msg.Type' = MsgUnreachable ∨ st.msg.Type' = MsgSnapStatus)
    (Ht : st.msg.Term' = W64 0) (He : st.ents = []) (Hc : st.ctx = [])
    -- (2026-10-19, D21 M2r) a transfer request only outside the cluster's no-snapshot mode
    (Hxt : st.msg.Type' = MsgTransferLeader → γ.raft.reNoSnap = false) :
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
      fun h => ?_⟩
    · rcases Hty with h | h | h | h <;> rw [h] <;> simp [netStepTypes]
    · exfalso
      rcases Hty with h' | h' | h' | h' <;> rw [h'] at h <;>
        simp [MsgApp, MsgHeartbeat, MsgHeartbeatResp,MsgCheckQuorum, MsgReadIndexResp, MsgTransferLeader,
          MsgForgetLeader, MsgUnreachable, MsgSnapStatus] at h
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
  isplitr
  · ipureintro; refine ⟨fun h => ?_, Hxt⟩; exfalso
    rcases Hty with h' | h' | h' | h' <;> rw [h'] at h <;>
      simp [MsgPreVote, MsgTransferLeader, MsgForgetLeader, MsgUnreachable, MsgSnapStatus] at h
  rw [Ht, ite_eq_right Hnr, ite_eq_right Hnt]
  isplitr
  · imodintro
    iintro %ty %Hty'
    rw [Hmt] at Hty'
    cases Hty'
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
    (ms : List QMsg) : IProp GF :=
  iprop(entsRO rd.CommittedEntries' ce ∗ isCommitted γ.raft (d ++ ce) ∗
    entsRO rd.Entries' es ∗ appendRight γ.stor es ∗
    rd.Messages' ↦* ms.map QMsg.loc ∗
    ([∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st ∗ isRaftMsg γ.raft q.st ∗
      termLB γ.bud q.st.msg.Term') ∗
    ([∗list] q ∈ ms, rdCred γ.raft (if q.st.msg.Type' = MsgReadIndex then 1 else 0)) ∗
    -- (2026-10-19, D21 M6) each forwarded proposal's tickets (`stTks`)
    ([∗list] q ∈ ms, stTks γ.raft q.st) ∗
    (∃ sts : List ReadStateM, readStatesPts rd.ReadStates' sts ∗
      [∗list] st ∈ sts, readStateOk γ.raft st) ∗
    (∃ h : HardStateM, hsOpt rd.HardState' h) ∗
    -- (2026-10-16, stage R7a, D10) the soft state: `nil`, or `Lead`/`RaftState` read-only
    softStateRO rd.SoftState' ∗
    ⌜rd.Snapshot' = null⌝ ∗
    -- (2026-10-18, D19b stage 5) the indices handed out are within the log (`readyIdx`)
    readyIdx γ.raft d ce es)

/-- A `Ready` on `readyc` (see the file header): `run`'s half of `dlv` at `d`, the other half
of its record, and the data. -/
def readyP (γ : NodeNames) (rd : Ready) : IProp GF :=
  iprop(∃ (d ce es : List EntryM) (ms : List QMsg),
    dghostVar γ.dlv (DFrac.own (1 : Qp).half) d ∗
    dghostVar γ.rof (DFrac.own (1 : Qp).half) (d, ce, es) ∗ readyData γ rd d ce es ms ∗
    -- (2026-10-15, stage N) the committed log handed out, a lower bound
    monoListLbOwn γ.dlm (d ++ ce))

/-- An `Advance` on `advancec`: a `dlv` half after the last `Ready`, `run`'s record back,
and the receipt of the append of the `Ready`'s entries. -/
def advanceP (γ : NodeNames) (_ : Unit) : IProp GF :=
  iprop(∃ (d ce es : List EntryM),
    dghostVar γ.dlv (DFrac.own (1 : Qp).half) (d ++ ce) ∗
    dghostVar γ.rof (DFrac.own (1 : Qp).half) (d, ce, es) ∗ appendReceipt γ.stor es ∗
    -- (2026-10-15, stage N) **A1**, in the dynamic mode: no conf entry of the committed log
    -- handed out past the driver's configuration index `ca` (a lower bound of `run`'s)
    ∃ ca : Nat, monoNatLbOwn γ.cam ca ∗
      ⌜γ.mode.isDyn = true → NoConfIn (d ++ ce) ca (d ++ ce).length⌝)

/-- The tick channel: one credit per buffered tick. -/
def tickInv (γ : NodeNames) : IProp GF :=
  iprop(∃ l : List Unit, ownChan γ.tick Unit (.Buffered l) ∗ tickCred γ.bud l.length)

/-- The committed log handed out so far is at least `ds` (2026-10-15, stage N; persistent): what
the driver knows of `run`'s, for a conf change's entry. -/
def dlvLb (γ : NodeNames) (ds : List EntryM) : IProp GF :=
  monoListLbOwn γ.dlm ds

instance dlvLb_persistent (γ : NodeNames) (ds : List EntryM) :
    Persistent (dlvLb (GF := GF) γ ds) := by
  unfold dlvLb; infer_instance

/-- The driver's view of the configuration (2026-10-15, stage N): the configuration index `ca`
and the configuration `cfg` as of the last conf change it applied (`node.ApplyConfChange`;
`cap`'s half, a lower bound of `cam`), and the answer slot `ccq`, whole. `RestartNode` hands it
out at `0` and the initial configuration; in the static mode it never moves. -/
def nodeCfg (γ : NodeNames) (ca : Nat) (cfg : CCState) : IProp GF :=
  iprop(dghostVar γ.cap (DFrac.own (1 : Qp).half) (ca, cfg) ∗
    (∃ x : Nat × CCState, dghostVar γ.ccq (DFrac.own (1 : Qp).half) x ∗
      dghostVar γ.ccq (DFrac.own (1 : Qp).half) x) ∗ monoNatLbOwn γ.cam ca)

/-- `run`'s side of what it shares with the driver about the configuration (2026-10-15, stage
N): the node's mode is `γ.mode`; the authority of the committed log handed out (`dlm`); the
configuration as of the last applied conf change, `(ca, rs.cfg)` (`cap`'s half, `cam`'s
authority at `ca`); `Advance` may have moved the configuration index past `ca`, over no conf
entry. -/
def runCfg (γ : NodeNames) (rs : RNState) : IProp GF :=
  iprop(⌜rs.mode = γ.mode ∧ rs.capplied ≤ rs.delivered.length ∧
      -- (D19i part 1) the floor not raised past `applied` (`RNState.flw`): `run` raises it only
      -- in its `advancec` arm, right before `Advance`
      rs.flw = false⌝ ∗
    monoListAuthOwn γ.dlm 1 rs.delivered ∗
    ∃ ca : Nat, dghostVar γ.cap (DFrac.own (1 : Qp).half) (ca, rs.cfg) ∗
      monoNatAuthOwn γ.cam 1 ca ∗ ⌜ca ≤ rs.capplied ∧ NoConfIn rs.delivered ca rs.capplied⌝)

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

In Perennial's channel model a receiver's `RcvPending` is entered only by the sender that meets
it, in the same step as `SndCommit` (`wp_TrySend_blocking`'s `RcvWait` case; a waiting offer a
`select` rescinds never reaches the logical state), so a node deposited at `RcvPending` is not
taken back by a `select` that fires another case. -/

/-- `run`'s node at the `advancec` rendezvous, before the floor is raised: `runMid_busy`'s. -/
def advDep (γ : NodeNames) (rn : Loc) (id : w64) : IProp GF :=
  iprop(∃ (rs : RNState) (d ce : List EntryM), ownRawNode γ.raft rn id rs ∗
    termLB γ.bud rs.tc ∗ runCfg γ rs ∗
    dghostVar γ.rof (DFrac.own (1 : Qp).half) (d, ce, rs.unpersisted) ∗
    ⌜rs.storage = γ.stor ∧ rs.unst = false ∧ rs.delivered = d ++ ce⌝)

/-- `run`'s node after the rendezvous: the `Ready`'s entries appended, the floor raised
(`flw`), the driver's payload in (its `dlv` half, `rof` back whole, A1's lower bound). -/
def advRet (γ : NodeNames) (rn : Loc) (id : w64) : IProp GF :=
  iprop(∃ (rs : RNState) (ca_d : Nat), ownRawNode γ.raft rn id rs ∗
    termLB γ.bud rs.tc ∗ runCfg γ { rs with flw := false } ∗
    dghostVar γ.dlv (DFrac.own (1 : Qp).half) rs.delivered ∗
    (∃ x : List EntryM × List EntryM × List EntryM,
      dghostVar γ.rof (DFrac.own (1 : Qp).half) x ∗ dghostVar γ.rof (DFrac.own (1 : Qp).half) x) ∗
    monoNatLbOwn γ.cam ca_d ∗
    ⌜rs.storage = γ.stor ∧ rs.unst = false ∧ rs.unpersisted = [] ∧ rs.flw = true ∧
      (γ.mode.isDyn = true → NoConfIn rs.delivered ca_d rs.delivered.length)⌝)

/-- The `advancec` protocol (see above). -/
def advInv (γ : NodeNames) (rn : Loc) (id : w64) : IProp GF :=
  iprop(∃ s, "Hch" ∷ ownChan γ.advancec Unit s ∗
    (match s with
     | .Idle => iprop(True)
     | .SndPending _ => iprop(advanceP γ () ∗ ∃ ds : List EntryM,
         dghostVar γ.req (DFrac.own (1 : Qp).half) ds.length ∗ dlvLb γ ds)
     | .RcvPending => advDep γ rn id
     | .SndCommit _ => advRet γ rn id
     | .RcvCommit => iprop(∃ (k : Nat) (x : w64), dghostVar γ.req (DFrac.own (1 : Qp).half) k ∗
         storFloor γ.stor x ∗ ⌜(k : Int) ≤ uint.Z x⌝)
     | _ => iprop(False)))

def advN : Namespace := nroot.@"raft_advancec"

/-- `advancec` (D19i part 1): the channel and its protocol. -/
def isAdvChan (γ : NodeNames) (rn : Loc) (id : w64) (ch : Loc) : IProp GF :=
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
def confcP (γ : NodeNames) (v : Loc) : IProp GF :=
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
def confstateP (γ : NodeNames) (cs : Loc) : IProp GF :=
  iprop(∃ c : ConfStateM, csPts cs (DFrac.own 1) c true ∗
    ((⌜γ.mode = .static ∧ confstateS γ c⌝) ∨
     (⌜γ.mode.isDyn = true⌝ ∗ ∃ v : Nat × CCState,
      dghostVar γ.cap (DFrac.own (1 : Qp).half) v ∗ dghostVar γ.ccq (DFrac.own (1 : Qp).half) v ∗
      monoNatLbOwn γ.cam v.1 ∗ ⌜confstateOk c v.2.cfg⌝)))

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
    "#Hcinv" ∷ raftCommitInv γ.raft)

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 4096 in
instance isNode_persistent (γ : NodeNames) (id : w64) (n : Loc) :
    Persistent (isNode (GF := GF) γ id n) := by
  unfold isNode; infer_instance

/-- The driver's token: the committed log it was handed so far is `ds`. -/
def nodeDriver (γ : NodeNames) (id : w64) (n : Loc) (ds : List EntryM) : IProp GF :=
  iprop(isNode γ id n ∗ dghostVar γ.dlv (DFrac.own (1 : Qp).half) ds ∗ dlvLb γ ds ∗
    -- (D19i part 1) the request on `advancec` (`advInv`)
    ∃ k : Nat, dghostVar γ.req (DFrac.own (1 : Qp).half) k ∗
      dghostVar γ.req (DFrac.own (1 : Qp).half) k)

/-- The driver with a `Ready` in hand: it was handed the committed log `ds` (the last
`Ready`'s included) and must append `es` (the last `Ready`'s entries) before `Advance`. -/
def nodeDriverBusy (γ : NodeNames) (id : w64) (n : Loc) (ds es : List EntryM) :
    IProp GF :=
  iprop(isNode γ id n ∗ dlvLb γ ds ∗
    ∃ (d ce : List EntryM), dghostVar γ.dlv (DFrac.own (1 : Qp).half) d ∗
      dghostVar γ.dlv (DFrac.own (1 : Qp).half) d ∗
      dghostVar γ.rof (DFrac.own (1 : Qp).half) (d, ce, es) ∗ ⌜ds = d ++ ce⌝ ∗
    ∃ k : Nat, dghostVar γ.req (DFrac.own (1 : Qp).half) k ∗
      dghostVar γ.req (DFrac.own (1 : Qp).half) k)

/-- `readyc`, as the driver sees it (`Node.Ready()`'s result). -/
def isReadyChan (γ : NodeNames) (ch : Loc) : IProp GF :=
  isHandshake γ.readyc ch (readyP γ) iprop(True)

instance isReadyChan_persistent (γ : NodeNames) (ch : Loc) :
    Persistent (isReadyChan (GF := GF) γ ch) := by
  unfold isReadyChan; infer_instance

/-- **Receiving a `Ready`** (the driver's loop, `for rd := range node.Ready()`): with the
driver's token, the `Ready`'s data for the committed log handed out so far, and the token
busy with it. The channel is never closed. -/
theorem node_ready_receive (γ : NodeNames) (id : w64) (n ch : Loc) (ds : List EntryM) :
    {{ isReadyChan γ ch ∗ nodeDriver (GF := GF) γ id n ds }}
      (App (Val (chan.receive Ready.ty)) (Val #ch))
    {{ (rd : Ready), RET (PairV #rd #true);
        ∃ (ce es : List EntryM) (ms : List QMsg),
          readyData γ rd ds ce es ms ∗ nodeDriverBusy γ id n (ds ++ ce) es }} := by
  iintro %Φ ⟨#Hrc, Hdrv⟩ HΦ
  unfold nodeDriver
  icases Hdrv with ⟨#Hnode, Hds, -, Hreq⟩
  unfold isReadyChan
  iapply wp_handshake_receive (t := Ready.ty) γ.readyc ch (readyP γ) iprop(True) $$ [] [HΦ Hds Hreq]
  · iframe Hrc
  iintro %rd
  iintro !> HP
  unfold readyP
  icases HP with ⟨%d, %ce, %es, %ms, Hd, Hrof, Hdata, #Hlb⟩
  ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hd Hds
  subst Heq
  iapply HΦ
  iexists ce, es, ms
  iframe Hdata
  unfold nodeDriverBusy
  iframe Hnode
  isplitr
  · unfold dlvLb; iexact Hlb
  iexists d, ce
  iframe Hd Hds Hrof Hreq
  ipureintro; rfl

/-- The committed log the driver was handed is a lower bound of `run`'s (2026-10-15). -/
theorem nodeDriver_lb (γ : NodeNames) (id : w64) (n : Loc) (ds : List EntryM) :
    ⊢ nodeDriver (GF := GF) γ id n ds -∗ dlvLb γ ds := by
  iintro H
  unfold nodeDriver
  icases H with ⟨-, -, $, -⟩

theorem nodeDriverBusy_lb (γ : NodeNames) (id : w64) (n : Loc) (ds es : List EntryM) :
    ⊢ nodeDriverBusy (GF := GF) γ id n ds es -∗ dlvLb γ ds := by
  iintro H
  unfold nodeDriverBusy
  icases H with ⟨-, $, -⟩

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

A proposal's ghost work before it leaves the node (`node_propose_ghost`: the update
deposited); and what the committed log's entries hold, for the application applying them
(`node_committed_data`, `node_entData_heap`, `node_collect`). (2026-10-16, stage R5, D6: no
proposed slices to record, `propDataInv` gone.) -/

section props
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- What `Node.Propose` takes for its data `d` (`fresh`: the first proposal of `d`, with
its fresh token and the client's persistent atomic update (2026-10-14, stage R); otherwise a
retry, with `d` deposited). Since 2026-10-19 (D21 M6) a first proposal is deposited `once`
(proposed once: its ticket goes with it, so it is appended once) or not; a retry needs `d`
deposited not once (`propMulti`). A proposal deposited once takes an update fired at most once
(`propAuM`). -/
def propArg (γ : RaftNames) (d : List w8) (Q : List EntryM → IProp GF) (fresh : Bool)
    (once : Bool) : IProp GF :=
  if fresh then iprop(propFresh γ d ∗ propAuM γ d Q once) else propMulti γ d

/-- What it gives back: `d` deposited, for a first proposal the handle on the update's
results (2026-10-14, stage R: persistent, no ticket), and (D21 M6) whether it is proposed
once. -/
def propRes (γ : RaftNames) (d : List w8) (Q : List EntryM → IProp GF) (fresh : Bool)
    (once : Bool) : IProp GF :=
  iprop(deposited γ d ∗
    (if fresh then iprop(∃ γq, isProp γ d γq Q) else iprop(True)) ∗
    (if fresh && once then propOnce γ d else propMulti γ d))

-- (2026-10-16, stage R5, D6) `propDataInv_alloc`, `propData_register` and `propData_heap` are
-- gone with the proposed slices: an entry's data, a read context, is its bytes.

end props

section nodeprops
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A proposal's ghost work before it leaves the node (`Node.Propose`): its update deposited
(a first proposal), so that its entry carries its data (`entData`). (2026-10-16, stage R5, D6:
the entry `propEntryM data` holds the bytes, which must not be empty (`Hne`: an empty one would
be a leader's own entry); no slice to record.) -/
theorem node_propose_ghost (γ : NodeNames) (id : w64) (n : Loc)
    (data : List w8) (Q : List EntryM → IProp GF) (fresh once : Bool) (E : CoPset)
    (HE1 : ↑raftN ⊆ E) (Hne : data ≠ []) :
    ⊢ isNode γ id n -∗ propArg γ.raft data Q fresh once ={E}=∗
      propData γ.raft (propEntryM data) ∗ entTk γ.raft (propEntryM data) ∗
      propRes γ.raft data Q fresh once := by
  iintro #Hnode Harg
  open_node Hnode
  have Htk : entTk (GF := GF) γ.raft (propEntryM data) =
      iprop(propTk γ.raft data ∨ propMulti γ.raft data) := by
    unfold entTk; rw [if_pos ⟨rfl, Hne⟩]; rfl
  rw [Htk]
  ihave Hres : |={E}=> (propTk γ.raft data ∨ propMulti γ.raft data) ∗
      propRes γ.raft data Q fresh once $$ [Harg]
  · unfold propArg propRes
    cases fresh with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_and]
      icases Harg with #Hm
      imodintro
      isplitr; · iright; iexact Hm
      isplitr; · iapply propMulti_deposited $$ Hm
      iframe Hm
    | true =>
      simp only [↓reduceIte, Bool.true_and]
      icases Harg with ⟨Hfr, Hau⟩
      imod prop_deposit γ.raft E data Q once HE1 $$ Hcinv Hfr Hau with ⟨%γq, #Hp, Hk⟩
      ihave #Hdep := isProp_deposited $$ Hp
      cases once with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        icases Hk with #Hm
        imodintro
        isplitr; · iright; iexact Hm
        iframe Hdep Hm
        iexists γq; iexact Hp
      | true =>
        simp only [↓reduceIte]
        icases propTk_once γ.raft data $$ Hk with ⟨Hk, #Ho⟩
        imodintro
        isplitl [Hk]; · ileft; iexact Hk
        iframe Hdep Ho
        iexists γq; iexact Hp
  imod Hres with ⟨Htk, Hres⟩
  ihave #Hdep : deposited γ.raft data $$ [Hres]
  · unfold propRes
    icases Hres with ⟨#Hd, -⟩
    iexact Hd
  imodintro
  iframe Hres Htk
  unfold propData
  iexists some data
  unfold propDataIs
  isplitr
  · ipureintro; exact ⟨rfl, Hne, rfl⟩
  iexact Hdep

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

/-- A proposed entry holds its data (2026-10-16, stage R5, D6: the bytes, on the record; until
then its slice held them, read through the proposed slices' invariant). -/
theorem node_entData_heap (γ : NodeNames) (id : w64) (n : Loc) (e : EntryM)
    (d : List w8) (E : CoPset) :
    ⊢ isNode (GF := GF) γ id n -∗ entDataIs γ.raft e (some d) ={E}=∗ ⌜e.Data' = d⌝ := by
  iintro #Hnode #He
  unfold entDataIs propDataIs
  icases He with ⟨⟨%H, -⟩, -⟩
  imodintro
  ipureintro; exact H.1

/-- Collecting a proposal's result (`prop_collect`), at the node: at a committed occurrence
of its data, the result at the log before it (2026-10-14, stage R). -/
theorem node_collect (γ : NodeNames) (id : w64) (n : Loc) (d : List w8) (γq : GName)
    (Q : List EntryM → IProp GF) (L : List EntryM) (m : Nat) (e : EntryM)
    (E : CoPset) (HE : ↑raftN ⊆ E) :
    L[m]? = some e →
    ⊢ isNode γ id n -∗ isProp γ.raft d γq Q -∗ isCommitted γ.raft L -∗
      entDataIs γ.raft e (some d) ={E}=∗ ▷ ▷ □ Q (L.take m) := by
  intro Hm
  iintro #Hnode #Hp #Hc #He
  open_node Hnode
  iapply prop_collect γ.raft E d γq Q L m e HE Hm $$ Hcinv Hp Hc He

/-- Depositing a read (`read_deposit`), at the node (2026-10-14, stage R). -/
theorem node_read_deposit (γ : NodeNames) (id : w64) (n : Loc) (c : List w8)
    (Qr : List EntryM → IProp GF) (L0 : List EntryM) :
    ⊢ isNode γ id n -∗ rdFresh γ.raft c -∗ readAu γ.raft Qr -∗ isCommitted γ.raft L0 ={⊤}=∗
      ∃ Lc, ⌜L0 <+: Lc⌝ ∗ readReq γ.raft c Lc ∗ isRead γ.raft c Qr := by
  iintro #Hnode Hfr #Hau #HL0
  open_node Hnode
  iapply read_deposit γ.raft c Qr L0 $$ Hcinv Hfr Hau HL0

/-- Collecting a read's result (`read_collect`), at the node (2026-10-14, stage R). -/
theorem node_read_collect (γ : NodeNames) (id : w64) (n : Loc) (c : List w8)
    (Qr : List EntryM → IProp GF) (i : w64) (L : List EntryM) (E : CoPset)
    (HE : ↑raftN ⊆ E) :
    uint.Z i ≤ (L.length : Int) →
    ⊢ isNode γ id n -∗ readWit γ.raft c Qr i -∗ isCommitted γ.raft L ={E}=∗ ▷ ▷ □ Qr L := by
  intro HiL
  iintro #Hnode #Hw #HL
  open_node Hnode
  iapply read_collect γ.raft E c Qr i L HE HiL $$ Hcinv Hw HL

end nodeprops

end EtcdGrove
end Perennial
