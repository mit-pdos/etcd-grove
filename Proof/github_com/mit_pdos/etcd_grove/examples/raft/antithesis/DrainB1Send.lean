/-
Lean-first (no Rocq counterpart). #33 parity B1, driver group E (`node.drain`'s send loop, the sync
B1 path): **everything a `Ready` message's send needs but the loop itself** (S4's `DrainMsgs`,
`DrainSendWp` pure parts, over `RunCfg`, `netTypes` and the transfer messages):
- `netFacts_of_ready`, `netFacts_of_pend`: a protocol message to another node is in flight
  (`NetFacts`), from raft's shape (`SentMsgShape`) and the Sim's (`ReadyMsgShape`, or the pending
  message's `MsgMask`/`PendOk` the run's invariant keeps), its numbers within the bound;
- `xnetFacts_of_ready`: a transfer message is in flight (`XNetFacts`), given the facts raft's
  `Ready` post does not state (see its premises);
- `drain_peekB1`: node `j`'s binding relation (`NodeOk`) read from the run's invariant, with
  `pendFacts_of`/`xpendFacts_of` its pending messages' facts;
- `sendEvM_abs`, `sendEvM_x`, `evSend_numsOk'`, `evSendX_numsOk`, `evSend_chgOk`, `evSendX_chgOk`,
  `evSend_weight'`, `evSendX_weight`: the `send` report `sendEv` builds is the Sim's (`evSend`,
  `evSendX`) at the node's name, within the bounds, of the weight `sendEv`'s receipts and two;
- `sendFacts_of`, `sendFacts_of_x`: `node.sendMsg`'s `sendFacts`, from raft's certificate
  (`isRaftMsg`), the term's lower bound and the sent witness; `isRaftMsg_resps`: no responses;
- `msgOwnZ_ptsC`: a `Ready`'s message frozen and read as `msgPtsC` (what `sendEv`/`sendMsg` take).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB1Loop
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.MsgShapeStmt
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.MsgBounds

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- Decide a proposition about raft's message-type constants (unfolded to their literals: the
constants take the `GooseExts` instance, which `decide` cannot revert). -/
local macro "mdec" : tactic => `(tactic| ((try simp only [UnstampedType, netStepTypes, MsgProp, MsgApp,
  MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat, MsgHeartbeatResp, MsgReadIndex, MsgReadIndexResp,
  MsgPreVote, MsgPreVoteResp, MsgTimeoutNow, MsgTransferLeader, MsgForgetLeader, MsgUnreachable,
  MsgSnapStatus, MsgSnap]) <;> (try simp) <;> decide))

section pure
variable [GooseExts]

/-! ## Message types -/

/-- **The network's types in a run of B1's off features** (a copy of `HarnessStep.netTypes_cases`,
which this file does not import). -/
theorem netTypes_cases_s {md : RnMode} {t : w32} (h : t ∈ netTypes md) (hs : md.snapshots = false)
    (hf : md.forwarding = false) :
    t = MsgApp ∨ t = MsgAppResp ∨ t = MsgVote ∨ t = MsgVoteResp ∨ t = MsgHeartbeat ∨
      t = MsgHeartbeatResp ∨ t = MsgPreVote ∨ t = MsgPreVoteResp ∨ t = MsgReadIndex ∨
      t = MsgReadIndexResp := by
  have hp : md.prevote = true ∨ md.prevote = false := by cases md.prevote <;> simp
  have hr : md.reads = true ∨ md.reads = false := by cases md.reads <;> simp
  rcases hp with hp | hp <;> rcases hr with hr | hr <;>
    simp only [netTypes, antStepTypes, hp, hr, hs, hf, Bool.false_eq_true, ↓reduceIte, List.append_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil, _root_.or_false, or_assoc] at h <;>
    rcases h with h | h | h | h | h | h | h | h | h | h <;> simp_all

/-- A message's protocol reading, not a snapshot, is `absMsg` at its type. -/
theorem absMsgOf_cases_s {st : MsgSt} {q : Msg} (h : absMsgOf st = some q) (hns : q.ty ≠ .snap) :
    ∃ ty, mtypeOf st.msg.Type' = some ty ∧ q = absMsg ty st.msg st.ents st.ctx := by
  unfold absMsgOf at h
  split at h
  · cases h
  · obtain ⟨sv, -, rfl⟩ := Option.map_eq_some_iff.1 h; exact absurd rfl hns
  · rename_i ty _ hty; cases h; exact ⟨ty, hty, rfl⟩

theorem netTypes_memA {md : RnMode} {t : w32} (h : t ∈ antStepTypes) : t ∈ netTypes md :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h)))

theorem netTypes_memB {md : RnMode} {t : w32} (hp : md.prevote = true)
    (h : t ∈ [MsgPreVote, MsgPreVoteResp]) : t ∈ netTypes md :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (by rw [hp]; exact h))))

theorem netTypes_memC {md : RnMode} {t : w32} (hr : md.reads = true)
    (h : t ∈ [MsgReadIndex, MsgReadIndexResp]) : t ∈ netTypes md :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by rw [hr]; exact h)))

/-- A described type the mask's network carries (no snapshots) is one of `netTypes`. -/
theorem mtypeOf_netTypes {md : RnMode} {t : w32} {ty : MsgType} (H : mtypeOf t = some ty)
    (h : AntSim.NetTy md ty) (hs : md.snapshots = false) : t ∈ netTypes md := by
  have key : ∀ k : Int, uint.Z t = k → t = W32 k := fun k hk => by rw [← hk]; simp
  unfold mtypeOf at H
  rcases h with h | h | h | h | h | h | ⟨hp, h | h⟩ | ⟨hr, h | h⟩ | ⟨hs', -⟩
  all_goals first
    | (rw [hs] at hs'; cases hs')
    | (subst h; split at H <;> cases H <;> rename_i hk <;> rw [key _ hk] <;>
        first
          | exact netTypes_memA (by decide)
          | exact netTypes_memB hp (by decide)
          | exact netTypes_memC hr (by decide))

/-- Go's `msgType` of a described type is the binding's. -/
theorem mtypeOf_msgTypeStr {t : w32} {ty : MsgType} (H : mtypeOf t = some ty) :
    msgTypeStr t = AntSim.msgTypeStr ty := by
  have key : ∀ k : Int, uint.Z t = k → t = W32 k := fun k hk => by rw [← hk]; simp
  unfold mtypeOf at H
  split at H <;> cases H <;> rename_i hk <;> rw [key _ hk] <;> decide

theorem mtypeOf_ne_snap {t : w32} {ty : MsgType} (H : mtypeOf t = some ty) (hns : ty ≠ .snap) :
    t ≠ MsgSnap := by
  intro h; subst h; rw [show mtypeOf MsgSnap = some .snap from rfl] at H
  exact hns (Option.some.inj H).symm

/-- Without snapshots, a type the network carries is not `snap`. -/
theorem netTy_ne_snap {md : RnMode} {ty : MsgType} (h : AntSim.NetTy md ty)
    (hs : md.snapshots = false) : ty ≠ .snap := by
  intro e; subst e
  rcases h with h | h | h | h | h | h | ⟨-, h | h⟩ | ⟨-, h | h⟩ | ⟨h', -⟩ <;> try cases h
  rw [hs] at h'; cases h'

/-- A message's numbers on its Go state (S4's `DrainBounds.msgNums_st`). -/
theorem msgNums_st {K : Int} {st : MsgSt} {q : Msg} (h : absMsgOf st = some q)
    (hns : q.ty ≠ .snap) (hq : AntSim.MsgNums K q) :
    uint.Z st.msg.Index' < K ∧ uint.Z st.msg.LogTerm' < K ∧ uint.Z st.msg.Commit' < K ∧
      ∀ e ∈ st.ents, uint.Z e.Term' < K ∧ uint.Z e.Index' < K := by
  obtain ⟨ty, -, rfl⟩ := absMsgOf_cases_s h hns
  exact hq

theorem absMsgOf_dst_s {st : MsgSt} {m : Msg} (H : absMsgOf st = some m) (hns : m.ty ≠ .snap) :
    m.dst = st.msg.To' := by
  obtain ⟨ty, -, rfl⟩ := absMsgOf_cases_s H hns
  rfl

/-! ## (B1) In flight -/

/-- **A `Ready`'s protocol message to another node is in flight** (`NetFacts`, B1: no snapshots, no
forwarding): raft's shape (`SentMsgShape`: a nonzero term and sender, not self-addressed, no
responses); a type the network carries (not a proposal), without reads a heartbeat or its response
with no context, normal entries; from and to a server; its numbers within the bound. -/
theorem netFacts_of_ready {R : AntSim.RunCfg} {st : MsgSt} {q : Msg}
    (habs : absMsgOf st = some q) (hnty : AntSim.NetTy R.md q.ty)
    (hctx : R.md.reads = false → (q.ty = .heartbeat ∨ q.ty = .heartbeatResp) → q.ctx = [])
    (hnorm : AntSim.EntsNormal q.entries)
    (hdst : ∃ j : Fin R.N, q.dst = AntSim.nodeId j) (hsrc : ∃ i : Fin R.N, q.src = AntSim.nodeId i)
    (hsent : SentMsgShape st) (hnums : AntSim.MsgNums (2 ^ 61) q)
    (hterm : uint.Z st.msg.Term' < 2 ^ 61) (hs : R.md.snapshots = false)
    (hf : R.md.forwarding = false) : NetFacts R st q := by
  have hns : q.ty ≠ .snap := netTy_ne_snap hnty hs
  obtain ⟨ty, hmt, rfl⟩ := absMsgOf_cases_s habs hns
  simp only [absMsg, absMsgFrom, Msg.mkV] at hnty hctx hnorm hdst hsrc hnums
  have htys : st.msg.Type' ∈ netTypes R.md := mtypeOf_netTypes hmt hnty hs
  obtain ⟨-, hf0, hz, hnz, hft, -, -, hres⟩ := hsent
  refine ⟨?_, htys, fun hr h => hctx hr ?_, hnorm, habs, hdst, hsrc,
    hterm, hnums.1, hnums.2.1, hnums.2.2.1, fun e he => (hnums.2.2.2 e he).1⟩
  · unfold NetMsgOk
    rcases netTypes_cases_s htys hs hf with ht | ht | ht | ht | ht | ht | ht | ht | ht | ht <;>
      rw [ht] at hz hnz hft ⊢ <;>
      exact ⟨by mdec,
        fun hu => ⟨rfl, hnz (fun h => hu (by revert h; mdec)), hf0⟩,
        fun hu hn => hz (by revert hu hn; mdec),
        fun _ => .inr rfl,
        fun h => by
          first
            | (apply hft <;> first | mdec | (intro h'; revert h'; mdec)) <;> done
            | (exfalso; revert h; mdec),
        fun h hr => by
          first
            | (apply hft <;> first | mdec | (intro _; exact hr)) <;> done
            | (exfalso; revert h; mdec),
        fun h => by exfalso; revert h; mdec,
        fun h => by
          first
            | (apply hft <;> first | mdec | (intro h'; revert h'; mdec)) <;> done
            | (exfalso; revert h; mdec),
        hres⟩
  · rcases h with h | h <;> rw [h] at hmt
    · exact .inl ((Option.some.inj ((mtypeOf_MsgHeartbeat).symm.trans hmt)).symm)
    · exact .inr ((Option.some.inj ((mtypeOf_MsgHeartbeatResp).symm.trans hmt)).symm)

/-- **A pending message's Sim facts** (the run's invariant's `MsgMask` and `PendOk` for node `j`'s
view, `drain_peekB1`): a type the network carries or a proposal, without reads a heartbeat or its
response with no context, normal entries (no conf changes), to another server, from a server. -/
theorem pend_shape {R : AntSim.RunCfg} {j : Fin R.N} {v : AntSim.NodeView} {q : Msg}
    (hm : AntSim.MsgMask R q) (hp : AntSim.PendOk R.N (AntSim.nodeId j) v q)
    (hcc : R.md.confChanges = false) :
    (AntSim.NetTy R.md q.ty ∨ q.ty = .propose) ∧
    (R.md.reads = false → (q.ty = .heartbeat ∨ q.ty = .heartbeatResp) → q.ctx = []) ∧
    AntSim.EntsNormal q.entries ∧ q.dst ≠ AntSim.nodeId j ∧
    (∃ i : Fin R.N, q.dst = AntSim.nodeId i) ∧ (∃ i : Fin R.N, q.src = AntSim.nodeId i) := by
  obtain ⟨hn, -, hty, hctx⟩ := hm
  unfold AntSim.PendOk at hp
  obtain ⟨hne, hd, hp⟩ := hp
  refine ⟨hty, hctx, hn hcc, hne, hd, ?_⟩
  split at hp
  all_goals first
    | exact ⟨j, hp.1⟩
    | exact hp.2
    | exact ⟨j, hp.2.2.1⟩
    | exact ⟨j, hp.2.1.2.1⟩

/-- **A pending protocol message is in flight** (`NetFacts`): `netFacts_of_ready` at the invariant's
facts of the view's pending message (`pend_shape`). -/
theorem netFacts_of_pend {R : AntSim.RunCfg} {j : Fin R.N} {v : AntSim.NodeView} {st : MsgSt}
    {q : Msg} (habs : absMsgOf st = some q) (hm : AntSim.MsgMask R q)
    (hp : AntSim.PendOk R.N (AntSim.nodeId j) v q) (hprop : q.ty ≠ .propose)
    (hsent : SentMsgShape st) (hnums : AntSim.MsgNums (2 ^ 61) q)
    (hterm : uint.Z st.msg.Term' < 2 ^ 61) (hs : R.md.snapshots = false)
    (hf : R.md.forwarding = false) (hcc : R.md.confChanges = false) : NetFacts R st q :=
  let ⟨hty, hctx, hn, _, hd, hsrc⟩ := pend_shape hm hp hcc
  netFacts_of_ready habs (hty.resolve_right hprop) hctx hn hd hsrc hsent hnums hterm hs hf

/-- A pending message is not a snapshot (no snapshots). -/
theorem pend_ne_snap {R : AntSim.RunCfg} {q : Msg} (hm : AntSim.MsgMask R q)
    (hs : R.md.snapshots = false) : q.ty ≠ .snap := hm.2.1 hs

/-- A protocol message's Go state is not a `MsgSnap`, its entries the reading's. -/
theorem absMsgOf_st {st : MsgSt} {q : Msg} (habs : absMsgOf st = some q) (hns : q.ty ≠ .snap) :
    st.msg.Type' ≠ MsgSnap ∧ st.ents = q.entries := by
  obtain ⟨ty, hty, rfl⟩ := absMsgOf_cases_s habs hns
  exact ⟨mtypeOf_ne_snap hty hns, rfl⟩

/-- **A transfer message's numbers zero and not a rejection**: what raft's `Ready` post does not
state (raft builds `MsgTimeoutNow` with only type, ends and term, `sendTimeoutNow`, and forwards a
`MsgTransferLeader` as it received it). -/
def XZero (st : MsgSt) : Prop :=
  st.msg.Index' = W64 0 ∧ st.msg.LogTerm' = W64 0 ∧ st.msg.Commit' = W64 0 ∧ st.msg.Reject' = false

/-- **A `Ready`'s transfer message is in flight** (`XNetFacts`): raft's shape (`SentMsgShape`: no
entries, no context, a nonzero sender, no responses) and `XReadyOk` (a `MsgTimeoutNow` the node's,
stamped), its destination a server (`xdst_server`), its term within the bound; and the facts raft's
`Ready` post does not state: transfers on (`htr`), a forwarded `MsgTransferLeader`'s sender a server
(`hsrcT`), its numbers zero and not a rejection (`XZero`). -/
theorem xnetFacts_of_ready {R : AntSim.RunCfg} {γr : RaftNames} {md : RnMode} {id : w64}
    {p : PState} {st : MsgSt} {x : XMsg} (hx : xmsgOf st = some x) (hok : XReadyOk γr md id p x)
    (hsent : SentMsgShape st) (htr : R.md.transfer = true)
    (hdst : ∃ j : Fin R.N, x.dst = AntSim.nodeId j) (hid : ∃ i : Fin R.N, id = AntSim.nodeId i)
    (hsrcT : x.ty = .transferLeader → ∃ i : Fin R.N, x.src = AntSim.nodeId i)
    (hterm : uint.Z st.msg.Term' < 2 ^ 61) (hz : XZero st) : XNetFacts R st x := by
  obtain ⟨-, hf0, -, -, -, -, hxe, hres⟩ := hsent
  obtain ⟨hI, hL, hC, hR⟩ := hz
  unfold xmsgOf at hx
  by_cases h1 : st.msg.Type' = MsgTimeoutNow
  · rw [if_pos h1] at hx; cases hx
    obtain ⟨hsrc, ht0⟩ := hok.1 rfl
    obtain ⟨i, hi⟩ := hid
    refine ⟨htr, ?_, .inl ⟨h1, rfl⟩, rfl, rfl, rfl, hdst, ⟨i, hsrc.trans hi⟩, hterm, hI, hL, hC,
      (hxe (.inl h1)).1, hR⟩
    refine ⟨by rw [h1]; mdec, fun _ => ⟨rfl, ht0, hf0⟩, fun hu => ?_, fun h => ?_, fun h => ?_,
      fun h _ => ?_, fun h => ?_, fun h => ?_, hres⟩ <;> rw [h1] at * <;> exfalso <;>
      first | (revert hu; mdec) | (revert h; mdec)
  · rw [if_neg h1] at hx
    by_cases h2 : st.msg.Type' = MsgTransferLeader
    · rw [if_pos h2] at hx; cases hx
      refine ⟨htr, ?_, .inr ⟨h2, rfl⟩, rfl, rfl, rfl, hdst, hsrcT rfl, hterm, hI, hL, hC,
        (hxe (.inr (.inl h2))).1, hR⟩
      refine ⟨by rw [h2]; mdec, fun hn => absurd (Or.inr (Or.inl h2)) hn,
        fun _ h => absurd h2 h, fun _ => .inr rfl, fun h => ?_, fun h _ => ?_,
        fun _ => hxe (.inr (.inl h2)), fun h => ?_, hres⟩ <;> rw [h2] at h <;> exfalso <;>
        revert h <;> mdec
    · rw [if_neg h2] at hx; cases hx

/-! ## (B3) The `send` report -/

/-- **A `Ready` message's `msgOf` report is the protocol message's** (S4's): its reading (not a
snapshot), its numbers within `2 ^ 61`. -/
theorem msgOfSt_abs {st : MsgSt} {q : Msg} (habs : absMsgOf st = some q) (hns : q.ty ≠ .snap)
    (hnums : AntSim.MsgNums (2 ^ 61) q) (hterm : uint.Z st.msg.Term' < 2 ^ 61) (to : w64) :
    msgOfSt st to = AntSim.msgOf q to := by
  obtain ⟨hI, hL, hC, hE⟩ := msgNums_st habs hns hnums
  obtain ⟨ty, hty, rfl⟩ := absMsgOf_cases_s habs hns
  have hns' : st.msg.Type' ≠ MsgSnap := mtypeOf_ne_snap hty hns
  unfold msgOfSt AntSim.msgOf
  simp only [hns', decide_false, Bool.false_eq_true, ↓reduceIte, absMsg, absMsgFrom, Msg.mkV,
    mtypeOf_msgTypeStr hty]
  have e1 : sint.Z st.msg.Term' = uint.Z st.msg.Term' := by word
  have e2 : sint.Z st.msg.Index' = uint.Z st.msg.Index' := by word
  have e3 : sint.Z st.msg.LogTerm' = uint.Z st.msg.LogTerm' := by word
  have e4 : sint.Z st.msg.Commit' = uint.Z st.msg.Commit' := by word
  rw [e1, e2, e3, e4, entOfE_logOf' (fun e he => (hE e he).1)]
where
  entOfE_logOf' {es : List EntryM} (h : ∀ e ∈ es, uint.Z e.Term' < 2 ^ 61) :
      es.map entOfE = AntSim.logOf es := by
    unfold AntSim.logOf
    apply List.map_congr_left
    intro e he
    have := h e he
    have e6 : sint.Z e.Term' = uint.Z e.Term' := by word
    unfold entOfE AntSim.entOf
    rw [e6]

/-- **`sendEv`'s report of a protocol message, recorded at the node, is the Sim's `send`**. -/
theorem sendEvM_abs {st : MsgSt} {q : Msg} (habs : absMsgOf st = some q) (hns : q.ty ≠ .snap)
    (hnums : AntSim.MsgNums (2 ^ 61) q) (hterm : uint.Z st.msg.Term' < 2 ^ 61) (id : w64)
    (b : AntCheck.Str) :
    atNode (AntSim.nameOf id) (sendEvM b st) = AntSim.evSend id b q := by
  have hmo : msgOfSt st st.msg.To' = AntSim.msgOf q q.dst := by
    rw [absMsgOf_dst_s habs hns]; exact msgOfSt_abs habs hns hnums hterm _
  simp only [atNode, sendEvM, AntSim.evSend, hmo]

/-- **`sendEv`'s report of a transfer message, recorded at the node, is the Sim's `sendX`**. -/
theorem sendEvM_x {st : MsgSt} {x : XMsg} (hx : xmsgOf st = some x) (hz : XZero st)
    (hents : st.ents = []) (hterm : uint.Z st.msg.Term' < 2 ^ 61) (id : w64) (b : AntCheck.Str) :
    atNode (AntSim.nameOf id) (sendEvM b st) = AntSim.evSendX id b x := by
  obtain ⟨hI, hL, hC, hR⟩ := hz
  have e1 : sint.Z st.msg.Term' = uint.Z st.msg.Term' := by word
  have e0 : sint.Z (W64 0) = 0 := by decide
  unfold xmsgOf at hx
  by_cases h1 : st.msg.Type' = MsgTimeoutNow
  · rw [if_pos h1] at hx; cases hx
    simp only [atNode, sendEvM, AntSim.evSendX, msgOfSt, AntSim.xmsgOf, h1, hI, hL, hC, hR, hents,
      e1, e0, List.map_nil]
    rfl
  · rw [if_neg h1] at hx
    by_cases h2 : st.msg.Type' = MsgTransferLeader
    · rw [if_pos h2] at hx; cases hx
      simp only [atNode, sendEvM, AntSim.evSendX, msgOfSt, AntSim.xmsgOf, h2, hI, hL, hC, hR, hents,
        e1, e0, List.map_nil]
      rfl
    · rw [if_neg h2] at hx; cases hx

/-- The `send` report's numbers. -/
theorem evSend_numsOk {st : MsgSt} {q : Msg} (habs : absMsgOf st = some q) (hns : q.ty ≠ .snap)
    (hnums : AntSim.MsgNums (2 ^ 61) q) (hterm : uint.Z st.msg.Term' < 2 ^ 61) (id : w64)
    (b : AntCheck.Str) : (AntSim.evSend id b q).NumsOk := by
  obtain ⟨hI, hL, hC, hE⟩ := msgNums_st habs hns hnums
  obtain ⟨ty, -, rfl⟩ := absMsgOf_cases_s habs hns
  simp only [AntSim.evSend, AntCheck.Event.NumsOk, AntCheck.optNumOk, AntSim.msgOf,
    AntCheck.Msg.NumsOk, AntCheck.numOk, AntCheck.numBound, absMsg, absMsgFrom, Msg.mkV,
    AntCheck.entriesOk, AntSim.logOf]
  and_intros
  all_goals try exact True.intro
  all_goals try (intro _ h; cases h; done)
  intro mm hmm
  simp only [Option.some.injEq] at hmm
  subst hmm
  refine ⟨⟨by word, by word⟩, ⟨by word, by word⟩, ⟨by word, by word⟩, ⟨by word, by word⟩, ?_⟩
  intro es hes
  simp only [Option.some.injEq] at hes
  subst hes
  intro e he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
  have h1 := (hE x hx).1
  have ht : (AntSim.entOf x).term = uint.Z x.Term' := by
    unfold AntSim.entOf; split
    · rfl
    · split <;> rfl
  rw [ht]
  have h0 : 0 ≤ uint.Z x.Term' := by word
  exact ⟨by omega, h1⟩

/-- A transfer message's `send` report's numbers. -/
theorem evSendX_numsOk {x : XMsg} (hterm : uint.Z x.term < 2 ^ 61) (id : w64) (b : AntCheck.Str) :
    (AntSim.evSendX id b x).NumsOk := by
  simp only [AntSim.evSendX, AntCheck.Event.NumsOk, AntCheck.optNumOk, AntSim.xmsgOf,
    AntCheck.Msg.NumsOk, AntCheck.numOk, AntCheck.numBound, AntCheck.entriesOk]
  and_intros
  all_goals try exact True.intro
  all_goals try (intro _ h; cases h; done)
  intro mm hmm
  simp only [Option.some.injEq] at hmm
  subst hmm
  refine ⟨⟨by word, by word⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩, ?_⟩
  intro es hes
  simp only [Option.some.injEq] at hes
  subst hes
  intro e he; cases he

theorem entOf_chgSize (e : EntryM) : (AntSim.entOf e).chgSize = 0 := by
  unfold AntSim.entOf
  split
  · rfl
  · split <;> rfl

/-- The `send` report changes no name. -/
theorem evSend_chgOk (id : w64) (b : AntCheck.Str) (q : Msg) : (AntSim.evSend id b q).ChgOk 0 := by
  intro l hl e he
  simp only [AntCheck.Event.entryLists, AntSim.evSend, AntCheck.Msg.entryLists, AntSim.msgOf,
    Option.map_some, Option.getD_some, Option.getD_none, List.nil_append, List.cons_append,
    List.mem_cons, List.not_mem_nil, or_false, List.flatMap_nil, List.append_nil] at hl
  rcases hl with rfl | rfl
  · cases he
  · obtain ⟨x, -, rfl⟩ := List.mem_map.1 he
    exact Nat.le_of_eq (entOf_chgSize x)

/-- A transfer message's `send` report changes no name. -/
theorem evSendX_chgOk (id : w64) (b : AntCheck.Str) (x : XMsg) : (AntSim.evSendX id b x).ChgOk 0 := by
  intro l hl e he
  simp only [AntCheck.Event.entryLists, AntSim.evSendX, AntCheck.Msg.entryLists, AntSim.xmsgOf,
    Option.map_some, Option.getD_some, Option.getD_none, List.nil_append, List.cons_append,
    List.mem_cons, List.not_mem_nil, or_false, List.flatMap_nil, List.append_nil] at hl
  rcases hl with rfl | rfl <;> cases he

/-- The `send` report's weight: `sendEv`'s receipts (`⧗ st.ents.length`) and two. -/
theorem evSend_weight {st : MsgSt} {q : Msg} (habs : absMsgOf st = some q) (hns : q.ty ≠ .snap)
    (id : w64) (b : AntCheck.Str) : (AntSim.evSend id b q).weight = st.ents.length + 2 := by
  obtain ⟨ty, -, rfl⟩ := absMsgOf_cases_s habs hns
  simp [AntSim.evSend, AntCheck.Event.weight, AntCheck.Event.size, AntCheck.Msg.size, AntSim.msgOf,
    AntSim.logOf, absMsg, absMsgFrom, Msg.mkV]

/-- A transfer message's `send` report's weight: two (`st.ents = []`). -/
theorem evSendX_weight (id : w64) (b : AntCheck.Str) (x : XMsg) :
    (AntSim.evSendX id b x).weight = 2 := by
  simp [AntSim.evSendX, AntCheck.Event.weight, AntCheck.Event.size, AntCheck.Msg.size,
    AntSim.xmsgOf]

end pure

/-! ## The run's invariant and raft's certificates -/

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

theorem setV_self_s {N : Nat} {V : Fin N → AntSim.NodeView} {j : Fin N} {v : AntSim.NodeView}
    (h : V j = v) : AntSim.setV V j v = V := by
  funext i
  unfold AntSim.setV
  split
  · rename_i hij; subst hij; exact h.symm
  · rfl

/-- **(B2) Node `j`'s binding relation, read from the run's invariant** (`view_update.law` at
`v' = v`, as `view_quiet`): some checker state and sent list at which node `j`, at its view `v`, is
related (`NodeOk`): its pending messages' `MsgMask`, `PendOk`, `XPendOk` (`pendFacts_of`). -/
theorem drain_peekB1 (h_vu : view_update.law (GF := GF)) (h_lo : nodeLive_over.law (GF := GF))
    (γ : AntNames) (j : Fin γ.R.N) (v : AntSim.NodeView) :
    inv antN (antInv (GF := GF) γ) ∗ viewFrag γ j v ∗ nodeLive γ j ⊢
      |={⊤}=> ⌜∃ (S : AntCheck.State) (net : List Msg), AntSim.NodeOk γ.R γ.dec S net j v⌝ ∗
        viewFrag γ j v ∗ nodeLive γ j := by
  iintro ⟨#Hinv, Hv, Hl⟩
  iinv Hinv with >Hi Hclose
  iunfold antInv at Hi
  icases Hi with (Hi | Hover)
  · iunfold antOpen at Hi
    icases Hi with ⟨%evs, %S, %V, %net, %xnet, %G, Hstr, Hviews, Hnet, Hxnet, %Hpure, #HF⟩
    imod h_vu (⊤ \ ↑antN) γ j V v v $$ [Hv Hviews] with ⟨%HVj, Hv, Hviews⟩
    · iframe Hv Hviews
    rw [setV_self_s HVj]
    imod Hclose $$ [Hstr Hviews Hnet Hxnet] with -
    · inext
      iunfold antInv
      ileft
      iunfold antOpen
      iexists evs, S, V, net, xnet, G
      iframe Hstr Hviews Hnet Hxnet HF
      ipureintro; exact Hpure
    imodintro
    iframe Hv Hl
    ipureintro
    exact ⟨S, net, by rw [← HVj]; exact Hpure.1.2.1.2.2.2.2 j⟩
  · iexfalso
    iapply h_lo γ j
    iframe Hl Hover

/-- **The pending messages' facts** out of `NodeOk`. -/
theorem pendFacts_of {R : AntSim.RunCfg} {dec : CCDec} {S : AntCheck.State} {net : List Msg}
    {j : Fin R.N} {v : AntSim.NodeView} (h : AntSim.NodeOk R dec S net j v) :
    (∀ q ∈ v.pend, AntSim.MsgMask R q ∧ AntSim.PendOk R.N (AntSim.nodeId j) v q) ∧
      (∀ x ∈ v.xpend, AntSim.XPendOk R.N (AntSim.nodeId j) v.ps x) :=
  ⟨fun q hq => ⟨h.facts.2.2.2.2.2.2.1 q hq, h.2.2.2.2.2.2.2.2.2.2.1 q hq⟩,
    h.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- Raft's shape of a message it hands out. -/
theorem isRaftMsg_shape_s (γ : RaftNames) (id : w64) (st : MsgSt) :
    isRaftMsg (GF := GF) γ id st ⊢ ⌜SentMsgShape st⌝ := by
  unfold isRaftMsg
  iintro ⟨%H, -⟩
  ipureintro; exact H

/-- **(B4) No responses** (`node.sendMsg`'s premise). -/
theorem isRaftMsg_resps (γ : RaftNames) (id : w64) (st : MsgSt) :
    isRaftMsg (GF := GF) γ id st ⊢ ⌜st.resps = []⌝ := by
  iintro #H
  ihave %Hs := isRaftMsg_shape_s γ id st $$ H
  ipureintro; exact Hs.2.2.2.2.2.2.2

/-- **Raft's certificate of a message it hands out** (`isMessage` of its protocol reading, not a
snapshot). -/
theorem isRaftMsg_isMessage_s (γ : RaftNames) (id : w64) (st : MsgSt) (q : Msg)
    (habs : absMsgOf st = some q) (hns : q.ty ≠ .snap) :
    isRaftMsg (GF := GF) γ id st ⊢ □ isMessage γ q := by
  obtain ⟨ty, hty, rfl⟩ := absMsgOf_cases_s habs hns
  have hns' : ty ≠ .snap := hns
  iintro #H
  unfold isRaftMsg
  icases H with ⟨-, ⟨%a, %Ha, #H⟩, -⟩
  rcases Ha with ⟨Hn, -⟩ | ⟨ty', Hty', -, rfl⟩ | ⟨sv, Hs, -, -⟩
  · rw [hty] at Hn; cases Hn
  · rw [hty] at Hty'; cases Hty'
    simp only [Option.toList_some]
    ihave #H := BigSepL.bigSepL_singleton.1 $$ H
    imodintro
    iapply isMessageC_isMessage $$ H
  · rw [hty] at Hs; cases Hs; exact absurd rfl hns'

theorem sentW_of_lb (γ : AntNames) (net : List Msg) (m : Msg) (h : m ∈ net) :
    sentLb (GF := GF) γ net ⊢ sentW γ m := by
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem h
  unfold sentLb sentW monoListIdxOwn
  iintro #H
  iexists i, net
  iframe H
  ipureintro; rw [List.getElem?_eq_getElem hi, he]

theorem xsentW_of_lb (γ : AntNames) (xnet : List XMsg) (x : XMsg) (h : x ∈ xnet) :
    xsentLb (GF := GF) γ xnet ⊢ xsentW γ x := by
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem h
  unfold xsentLb xsentW monoListIdxOwn
  iintro #H
  iexists i, xnet
  iframe H
  ipureintro; rw [List.getElem?_eq_getElem hi, he]

/-- **(B4) A protocol message's `sendFacts`**: in flight (`NetFacts`), raft's certificate, its
term's lower bound, sent. -/
theorem sendFacts_of (γ : AntNames) (id : w64) (st : MsgSt) (q : Msg) (habs : absMsgOf st = some q)
    (hns : q.ty ≠ .snap) (hnf : NetFacts γ.R st q) :
    isRaftMsg (GF := GF) γ.raft.raftNames id st ∗ rnTermLB γ.raft st.msg.Term' ∗ sentW γ q ⊢
      sendFacts γ st := by
  iintro ⟨#Hr, Ht, #Hs⟩
  ihave #Hm := isRaftMsg_isMessage_s γ.raft.raftNames id st q habs hns $$ Hr
  iunfold sendFacts
  iright
  ileft
  iexists q
  isplitr
  · ipureintro; exact hnf
  isplitr
  · iexact Hm
  isplitl [Ht]
  · iexact Ht
  iexact Hs

/-- **(B4) A transfer message's `sendFacts`**: in flight (`XNetFacts`), its term's lower bound, sent,
and raft's two witnesses (`isRaftMsg`'s transfer and timeout clauses). -/
theorem sendFacts_of_x (γ : AntNames) (id : w64) (st : MsgSt) (x : XMsg)
    (hnf : XNetFacts γ.R st x) :
    isRaftMsg (GF := GF) γ.raft.raftNames id st ∗ rnTermLB γ.raft st.msg.Term' ∗ xsentW γ x ⊢
      sendFacts γ st := by
  iintro ⟨#Hr, Ht, #Hs⟩
  unfold isRaftMsg
  icases Hr with ⟨-, -, -, -, #Hxf, -, -, #Hto⟩
  iunfold sendFacts
  iright
  iright
  iexists x
  isplitr
  · ipureintro; exact hnf
  isplitl [Ht]
  · iexact Ht
  isplitr
  · iexact Hs
  isplitr
  · iexact Hxf
  iexact Hto

/-- **(B5) A `Ready`'s message frozen** (raft's `msgOwnZ` without the size flag, `maxData = none`):
read-only, as `msgPtsC`, what `sendEv`, `sendMsg` and `sent` take. -/
theorem msgOwnZ_ptsC (l : Loc) (dq : DFrac) (st : MsgSt) :
    msgOwnZ (GF := GF) false l dq st ⊢ |==> msgPtsC l DFrac.discard DFrac.discard false st := by
  unfold msgOwnZ
  iintro ⟨%c, Hc, %H⟩
  imod msgPtsCC_persist _ _ _ $$ Hc with Hc
  imodintro
  rw [← H.1]
  iapply msgPtsCC_msgPtsC _ _ _ _ c H.2.1.1
  iexact Hc

end proof

end AntHarness
end EtcdGrove
end Perennial
