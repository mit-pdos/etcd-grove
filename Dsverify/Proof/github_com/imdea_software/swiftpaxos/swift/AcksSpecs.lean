/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/AcksSpecs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The descriptor side's internal specs for the acknowledgement handlers (swift.go:
`getFastAndSlowAcksHandler`, `commonCaseFastAck`, `handleLightSlowAck`, `fastAckFromLeader`), the
swift group's (not frozen; notes/prove-swift.md §12).

* `swift.DC`: the descriptor context's parameters in one record (`swift.DC.ctx`: `descCtx`).
* `swift.leadAckP c b x`: the leader's ack in `x`'s descriptor's message sets (the sets' `PL`):
  an `*MFastAck` for `x` (read-only) and why the replica may commit `x` in `b`: it accepted `x`
  in `b` (`fastAckFromLeader` adds the leader's ack only after the local acceptance, at a
  follower and at the leader alike). Round B1 (D81): this is the leader entry's "proposal set"
  fact: an accepted row has a proposal (`rowAcc`), so the commit under it has one too.
  `commonCaseFastAck`'s leader branch is refuted by the ack's sender (`ackWhy`: a light slow
  ack's sender is not its ballot's leader, `msgOk`, change log C16).
* `swift.descSt c RC MP γd d x b Rs`: what the sets' handler is lent (the sets' `R`): the
  descriptor's fields `deliver` uses (`descF`), its epoch share (`epochRd`, the reply channel's
  object `RC`), `x`'s row token with the commit fact when the row says committed, `phase =
  COMMIT` only then, and a frame `Rs` (the other set, …). Round 33 (table rev 4/5 §3.7): why its
phase and `dep` are what they are (`phaseWhy`, `depWhy`, `rowPhaseOk`) and its kind
(`dv.seq = c.sq`).
* `swift.exIn`: the sets' `Rdone`: `x` was executed in the epoch (the descriptor may be retired:
  its owner must check `delivered.Has(x)` before touching it again, SWB-2).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DeliverE
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.MsgSet
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.hook.OptCondF

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-- The descriptor context's parameters (`swift.descCtxE`'s). -/
structure swift.DC where
  γ : sp.Names
  γc : GName
  γm : GName
  γl : GName
  γw : GName
  γv : GName
  γe : GName
  γo : GName
  γx : GName
  γxe : GName
  γxm : GName
  γxp : GName
  γdc : ChanNames
  γdl : GName
  str : swift.CommandId → GoString
  rp : Loc
  rr : Loc
  N : Nat
  r : Nat
  k : Nat
  /-- Round 20 (decision (2)): a replica-wide ghost map, descriptor ↦ its owner's current
  epoch share `q` (`descSt` holds half the element; `descGone` returns it, so the loan's
  exact fraction is known when the goroutine gives its share back). -/
  γsh : GName
  /-- round 32 (notes/lifecycle-plan.md "Revision 5", D1): the store's ledger and claims
  (`swift.StN`, DescNode.lean) -/
  γout : GName
  γcl : GName
  /-- round 46 (D-SWC2-5, D57): the execution tickets' map (`swift.xTixK`; `descCtxE`'s `γxu`) -/
  γxu : GName
  /-- round N5 (D72 (1)): the report tokens' map (`swift.repTok`, DescNode.lean) -/
  γrp : GName
  /-- round 56 (D79 (1), 52-3): the epochs' map ballot ↦ that epoch's commit-witness map `γk`
  (`swift.nodeX`, DescNode.lean; read by `retWhy (.rest d γi)`) -/
  γcg : GName
  /-- round 33 (table rev 4/5 §3.0, D34; instantiated per epoch and owner kind in Phase 2):
  the owner kind (`true`: the run loop's sequential descriptor, run inline) -/
  sq : Bool
  /-- the owner's loan environment at its share `q` (loan token, registry share with its
  receipt, the descriptors' invariants) -/
  env : Loc → Qp → IProp netDistGF
  /-- what a retired descriptor's caller gets back (seq: the `γS` element, C4) -/
  ret : Loc → swift.CommandId → IProp netDistGF
  /-- the owner kind's frame (`active`, `stopChan`, `γi`, `γsh` halves; goroutine: `γj` receipt) -/
  kf : Loc → swift.CommandId → IProp netDistGF
  /-- round 34 (table rev 6, G-slot): the ledger's slot of the owner, carried by `rowTokO`:
  `slot none` the registry share that goes out with the token, `slot (some K)` the ledger's
  receipt of the key `K` taken out of the store -/
  slot : Option (Nat × sp.CmdId) → IProp netDistGF

/-- The store's parameters of the record (`swift.nodeInvD`'s). -/
abbrev swift.DC.sn (c : swift.DC) : swift.StN := ⟨c.γxm, c.γout, c.γcl, c.str, c.N, c.r, c.γxu, c.γrp, c.γcg⟩

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions] [hook.Assumptions]

/-- **A record's base** (round 35, table rev 7b §3.12, G-hrec): the record with its owner-kind
fields at fixed placeholders (`RunX.dc` is the base of every owner record `RunX.dcK g k`). What a
persistent spec proved before the owner kind is known (the sets' handler at `newDesc`) holds for
every record with this base (`acksHdOkB`). -/
def swift.DC.base (c : swift.DC) : swift.DC :=
  { c with
    sq := false
    env := fun _ _ => iprop(True)
    ret := fun _ _ => iprop(True)
    kf := fun _ _ => iprop(True)
    slot := fun _ => iprop(True) }

/-- `descCtxE` of the record (round 46, D-SWC2-6: `descCtx` replaced). -/
def swift.DC.ctx (c : swift.DC) : IProp netDistGF :=
  swift.descCtxE c.γ c.γc c.γm c.γl c.γw c.γv c.γe c.γo c.γx c.γxe c.γxm c.γxp c.γxu c.γrp c.γcg c.γout c.γcl c.γdc
    c.γdl c.str c.rp c.rr c.N c.r c.k

instance swift.DC.ctx_persistent (c : swift.DC) : Persistent c.ctx := by
  unfold swift.DC.ctx; infer_instance

/-- The context reads only base fields (round 35, G-hrec). -/
theorem swift.DC.ctx_base (c : swift.DC) : c.ctx = c.base.ctx := rfl

/-- The leader's ack in `x`'s descriptor's sets (see the file header). -/
def swift.leadAckP (c : swift.DC) (b : Nat) (x : swift.CommandId) (lm : GoInterface) :
    IProp netDistGF :=
  iprop(∃ (l : Loc) (fa : swift.MFastAck),
    ⌜lm = interface.mkOk (go.GoType.PointerType swift.MFastAck.ty) #l ∧ fa.CmdId' = x ∧
      sp.bal fa.Ballot' = b ∧ 0 ≤ sint.Z fa.Ballot'⌝ ∗
    l ↦□ fa ∗ (∃ D : List swift.CommandId, fa.Dep' ↦*□ D) ∗ sp.accepted c.γ c.r b (toCmdId x))

instance swift.leadAckP_persistent (c : swift.DC) (b : Nat) (x : swift.CommandId)
    (lm : GoInterface) : Persistent (swift.leadAckP c b x lm) := by
  unfold swift.leadAckP; infer_instance

/-- `leadAckP` reads only base fields (round 35, G-hrec). -/
theorem swift.leadAckP_base (c c' : swift.DC) (h : c'.base = c.base) :
    swift.leadAckP c' = swift.leadAckP c := by
  show swift.leadAckP c'.base = swift.leadAckP c.base
  rw [h]

/-- Facts of `x`'s row (round 10): an accepted row has its `accepted` fact (a repeated
acceptance, `"recheck"` or a second leader ack, skips the ghost step), and a pre-accepted row's
descriptor has its proposal (round 14: also a row with its path; `handlePropose` sets `propose`
before pre-accepting, `preaccept_dstep` needs both unset; round 15: a set proposal is a
read-only `*GPropose`, `handlePropose` reads its `Proxy` after `Recall`; so at the
leader, whose own ack witnesses its pre-acceptance, `afterPropagate`'s condition is true).
Round B1 (D81): also an accepted or committed row's descriptor has its proposal (a row is
accepted only inside `afterPropagate`'s guarded closure or by `handleSyncEntry`, which sets
`propose`; it is committed under the leader entry's acceptance, `leadAckP`). -/
def swift.rowAcc (c : swift.DC) (b : Nat) (x : swift.CommandId) (dv : swift.DescV)
    (rv : swift.RowV) : IProp netDistGF :=
  iprop((⌜rv.2.2.1 = false⌝ ∨ sp.accepted c.γ c.r b (toCmdId x)) ∗
    ⌜rv.1.isSome ∨ rv.2.1.isSome ∨ rv.2.2.1 = true ∨ rv.2.2.2 = true → dv.propose ≠ null⌝ ∗
    (⌜dv.propose = null⌝ ∨ ∃ gv : replica.defs.GPropose, dv.propose ↦□ gv))

instance swift.rowAcc_persistent (c : swift.DC) (b : Nat) (x : swift.CommandId) (dv : swift.DescV)
    (rv : swift.RowV) : Persistent (swift.rowAcc c b x dv rv) := by
  unfold swift.rowAcc; infer_instance

/-- **The owner's epoch fields at its share `q`, without its `γsh` half** (round 24, D20 (1);
round 33, table rev 4/5 §3.0): `q` of `status` and of `FQ` (with its quorum, whose members are
in `b`'s fast quorum `AQ`; fixedMajority: `FQ = qs.AQ(ballot)`; and **E7**: `b`'s leader is a
member), the owned reader of `delivered`, the owner's loan environment `c.env d q`, and (round 43,
table §3R11b, D51 (c)) the loan's epoch pin `ghostVar c.γxp q b` at the same `q`. What a
retired descriptor gives back with `epochRd q` (`descGone`). -/
def swift.shOwnR (c : swift.DC) (d : Loc) (b : Nat) (q : Qp) : IProp netDistGF :=
  iprop((∃ st : w64, typedPointsto (swift.fld c.rp go!"status") st (DFrac.own q)) ∗
    (∃ (fq : GoInterface) (szF : Nat) (memF : w32 → Prop),
      typedPointsto (swift.fld c.rp go!"FQ") fq (DFrac.own q) ∗ replica.mset.quorumIs fq szF memF ∗
      ⌜(∀ i : w32, memF i → sp.rid i ∈ sp.AQ c.N b) ∧
        (∀ i : w32, 0 ≤ sint.Z i → sp.rid i = sp.leaderOf c.N b → memF i)⌝) ∗
    swift.ownRdr c.rp c.γdl ∗ c.env d q ∗
    -- round 43 (table §3R11b, D51 (c)): the loan's epoch pin at the loan's `q`
    ghostVar c.γxp q b)

/-- **The owner's epoch fields at its share `q`** (see `shOwnR`): half of its `γsh` element (at
`q`) and `shOwnR`. They travel with `epochRd q` (`descSt`). -/
def swift.shOwn (c : swift.DC) (d : Loc) (b : Nat) (q : Qp) : IProp netDistGF :=
  iprop(ghostMapElem c.γsh d (DFrac.own (1 : Qp).half) q ∗ swift.shOwnR c d b q)

/-- **A sequential descriptor retired** (round 10; round 33, table rev 4/5 T14/T16, C4): only
the run loop's sequential descriptors retire inside a call (`⌜c.sq⌝`); `x` executed in epoch
`b`, the kind's residue `c.ret d x`, and the epoch share back (`epochRd q` with `shOwnR`: its
`γsh` half went into the freed descriptor). -/
def swift.descGone (c : swift.DC) (b : Nat) (x : swift.CommandId) (d : Loc) : IProp netDistGF :=
  iprop(⌜c.sq = true⌝ ∗ swift.exIn c.γxm b x ∗ c.ret d x ∗
    ∃ (q : Qp) (bw : w32) (stp rcp : Loc), swift.epochRd c.γe c.γxe c.rp c.rr q b bw stp rcp ∗
      swift.shOwnR c d b q)

/-- A retired descriptor's owner (round 10; round 24: `descGone`, whose `shOwn` has the
`status` share a stored closure run after the retirement still reads). -/
def swift.descDone (c : swift.DC) (b : Nat) (x : swift.CommandId) (d : Loc) : IProp netDistGF :=
  swift.descGone c b x d

/-- **The owner's slot of the key `K` with its ticket** (round 46, D-SWC2-5/D57): the ledger's
slot `c.slot (some K)` and the key's ticket or its use (`swift.tixOr`), both of which travel with
the row token (`rowTokO`, `takeLaw`). -/
def swift.slotT (c : swift.DC) (K : Nat × sp.CmdId) : IProp netDistGF :=
  iprop(c.slot (some K) ∗ swift.tixOr c.γxu c.γxm K)

/-- **`x`'s row token, optional until the proposal or the sync entry delivers it** (G7, D23/D25;
round 28): the token, or no token yet (the row empty, no proposal) with the deferred commit's
justification when the descriptor says committed (`leadAckP`'s: the replica is `b`'s leader or
accepted `x` in `b`). A descriptor is created by any message (acks, dependency lookups, sync
entries) but its token comes only with `handle_stepD` (the proposal) or `takeSync_stepD`. -/
def swift.rowTokO (c : swift.DC) (b : Nat) (x : swift.CommandId) (dv : swift.DescV)
    (rv : swift.RowV) : IProp netDistGF :=
  iprop((swift.rowTok c.γo b (toCmdId x) rv ∗ swift.slotT c (b, toCmdId x)) ∨
    (⌜rv = swift.rowEmpty ∧ dv.propose = null⌝ ∗
      (⌜dv.phase ≠ swift.phCOMMIT⌝ ∨ ⌜c.r = sp.leaderOf c.N b⌝ ∨
        sp.accepted c.γ c.r b (toCmdId x)) ∗ c.slot none))

/-- **The take, as a law of the record** (round 34, table rev 6 G-slot; T11 :512, T24): with the
owner's environment (its loan refutes a stopped epoch), the free slot and a claim of `K`, the
stored token of `K` with its record, and the slot holding `K`'s receipt. Proved for each concrete
record from `swift.store_take` (Store.lean); the generic install steps use it from their
context. -/
def swift.takeLaw (c : swift.DC) : IProp netDistGF :=
  iprop(□ ∀ (d : Loc) (q : Qp) (K : Nat × sp.CmdId) (ck : swift.ClK),
    c.env d q -∗ c.slot none -∗ swift.claimTok c.γcl K ck -∗
      |={⊤}=> ∃ rv : swift.RowV, swift.rowTok c.γo K.1 K.2 rv ∗
        swift.retWhy c.γ c.γxm c.γcg c.str c.N c.r K rv (swift.recOf ck) ∗ c.env d q ∗
        swift.slotT c K)

instance swift.takeLaw_persistent (c : swift.DC) : Persistent (swift.takeLaw c) := by
  unfold swift.takeLaw; infer_instance

/-- The descriptor's state its sets' handler is lent (see the file header; round 33: with
`phaseWhy`, `depWhy` (G-ldr), `rowPhaseOk` and `dv.seq = c.sq`; round 37, table rev 8b K1: the
incarnation's slot builder `slotB`, which every caller of `deliver` needs). -/
def swift.descSt (c : swift.DC) (RC : Loc → w32 → IProp netDistGF) (MP : GoInterface → IProp netDistGF)
    (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat) (Rs : IProp netDistGF) :
    IProp netDistGF :=
  iprop(∃ (q : Qp) (bw : w32) (stp rcp : Loc) (dv : swift.DescV) (rv : swift.RowV),
    swift.epochRd c.γe c.γxe c.rp c.rr q b bw stp rcp ∗
    swift.shOwn c d b q ∗ RC rcp bw ∗ swift.descF d γd MP dv ∗
    swift.rowTokO c b x dv rv ∗
    (⌜rv.2.2.2 = false⌝ ∨ sp.committed c.γ c.r b (toCmdId x)) ∗
    -- round 47 (46-2, D61 (2)): `deliver.specE`'s reply facts, paired with `rowAcc` (one slot, so
    -- the patterns that skip it with `-` are unchanged)
    (swift.rowAcc c b x dv rv ∗ swift.repPre c.γ c.N c.r b x dv) ∗
    ⌜dv.phase = swift.phCOMMIT → rv.2.2.2 = true ∨ dv.propose = null⌝ ∗
    swift.phaseWhy c.γ c.N c.r b x dv ∗ swift.depWhy c.γ c.γxm c.N c.r b x dv ∗
    ⌜swift.rowPhaseOk c.N c.r b dv rv ∧ dv.seq = c.sq⌝ ∗ □ swift.slotB MP c.γxm b x ∗ Rs)

/-- An ack in `x`'s descriptor's sets (their `P`): an `*MFastAck` for `x` from replica `k`,
read-only. (What the accept closure and the handler need of it; the protocol witnesses are
not needed: the commit is justified by the leader's ack, `leadAckP`.) -/
def swift.ackP (x : swift.CommandId) (k : w32) (m : GoInterface) : IProp netDistGF :=
  iprop(∃ (l : Loc) (fa : swift.MFastAck),
    ⌜m = interface.mkOk (go.GoType.PointerType swift.MFastAck.ty) #l ∧ fa.CmdId' = x ∧
      fa.Replica' = k⌝ ∗ l ↦□ fa ∗ (∃ D : List swift.CommandId, fa.Dep' ↦*□ D))

/-- The sets' accept relation (no guarantee needed). -/
def swift.ackA : GoInterface → GoInterface → IProp netDistGF := fun _ _ => iprop(True)

/-- The set `x`'s descriptor's handler is lent with the slow set (`slow`, at `s`; the other
at `f`) or the fast one: `descSt` over the sets' fields, the other set's data (quorum `qO` of
size `szO`, members `memO`; handler `hd`), and the owner's other fields `Do`. -/
def swift.setR (c : swift.DC) (RC : Loc → w32 → IProp netDistGF) (MP : GoInterface → IProp netDistGF)
    (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat) (Do : IProp netDistGF)
    (s f : Loc) (qO : GoInterface) (szO : Nat) (memO : w32 → Prop) (hd : GoFunc) (slow : Bool) :
    IProp netDistGF :=
  swift.descSt c RC MP γd d x b iprop(swift.dfld d go!"slowPathH" ↦ s ∗
    swift.dfld d go!"fastPathH" ↦ f ∗
    replica.mset.ownD (if slow then f else s) qO szO memO (swift.ackP x) swift.ackA
      (swift.leadAckP c b x) iprop(True) hd ∗ Do)

/-- `afterPropagate`'s condition's state (round 10): the other half of `propose`
(`func() bool { return desc.propose != nil }`, newDesc). -/
def swift.proposeHalf (d : Loc) (v : Bool) : IProp netDistGF :=
  iprop(∃ p : Loc, typedPointsto (swift.dfld d go!"propose") p (DFrac.own (1 : Qp).half) ∗
    ⌜decide (p ≠ null) = v⌝)

/-- **The spec-free part of `afterPropagate`** (round 33, table rev 4 §3.6b, C3): the field, the
`OptCondF` with its stored functions `fs`, the condition's state `proposeHalf d v`, and the
stored acks' ballots. It travels down the inline chain (a sequential retirement frees it). -/
def swift.ocfRes (d cf : Loc) (cond : GoFunc) (fs : List GoFunc) (v : Bool) : IProp netDistGF :=
  iprop(swift.dfld d go!"afterPropagate" ↦ cf ∗ hook.ocf.ownOcf cf cond fs ∗ swift.proposeHalf d v ∗
    ∃ (sb : GoSlice) (bs : List w32), swift.dfld d go!"storedBallots" ↦ sb ∗ sb ↦* bs ∗
      ownSliceCap w32 sb (DFrac.own 1) ∗ ⌜bs.Nodup ∧ fs.length ≤ bs.length⌝)

/-- `ocfRes` at the true condition with nothing stored, with the condition's spec (what `Call`/
`Recall` give the chain's closures). -/
def swift.ocfRes0 (d : Loc) : IProp netDistGF :=
  iprop(∃ (cf : Loc) (cond : GoFunc), swift.ocfRes d cf cond [] true ∗
    □ hook.ocf.condOk cond (swift.proposeHalf d))

/-- **A message set `Free` can run on** (round 41, gap 41-1; moved here from SlotSpecs.lean in round
42, D48 (3)): the set's data with its closures' specs (`freeOk`) at handler resource `True` (the
descriptors' sets, table §3R11.4). -/
def swift.msetF (ms : Loc) : IProp netDistGF :=
  iprop(∃ (q : GoInterface) (sz : Nat) (mem : w32 → Prop) (P : w32 → GoInterface → IProp netDistGF)
      (A : GoInterface → GoInterface → IProp netDistGF) (PL : GoInterface → IProp netDistGF)
      (hd : GoFunc),
    replica.mset.ownD ms q sz mem P A PL iprop(True) hd)

/-- **The sequential descriptor's slot capability over its owner frame `F`** (round 33, table
rev 4/5 G-cap, C3; stored in `descOwn`): a goroutine's (`c.sq = false`: never retires inside a
call), or the slot case's spec from the fields, `x` executed, the `γsh` half, the row token,
the sets, the `OptCondF` part (any state), `F` and the loan environment: it retires the
descriptor and gives `c.ret d x` and the environment back. -/
def swift.slotCap (c : swift.DC) (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc)
    (x : swift.CommandId) (b : Nat) (F : IProp netDistGF) : IProp netDistGF :=
  iprop(⌜c.sq = false⌝ ∨ □ ∀ (s : w64) (dv : swift.DescV) (rv : swift.RowV) (q : Qp)
      (sl fa cf : Loc) (cond : GoFunc) (fs : List GoFunc) (v : Bool),
    {{ MP (interface.mkOk go.int #s) ∗ swift.descF d γd MP dv ∗ ⌜dv.seq = true ∧ dv.propose ≠ null⌝ ∗
        swift.exIn c.γxm b x ∗ ghostMapElem c.γsh d (DFrac.own (1 : Qp).half) q ∗
        swift.rowTokO c b x dv rv ∗
        swift.dfld d go!"slowPathH" ↦ sl ∗ swift.dfld d go!"fastPathH" ↦ fa ∗
        swift.msetF sl ∗ swift.msetF fa ∗ swift.ocfRes d cf cond fs v ∗ F ∗
        c.env d q }}
      (App (App (App (Val (c.rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"handleMsg"))
        (Val #(interface.mkOk go.int #s))) (Val #d)) (Val #x))
    {{ RET #true; c.ret d x ∗ c.env d q }})

/-- **The slot capability at the handler's level** (G-cap): over the set `ms` the handler is
lent and the frame `Rs` it is lent with. -/
def swift.slotCapR (c : swift.DC) (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc)
    (x : swift.CommandId) (b : Nat) (ms : Loc) (Rs : IProp netDistGF) : IProp netDistGF :=
  iprop(⌜c.sq = false⌝ ∨ □ ∀ (s : w64) (dv : swift.DescV) (rv : swift.RowV) (q : Qp),
    {{ MP (interface.mkOk go.int #s) ∗ swift.descF d γd MP dv ∗ ⌜dv.seq = true ∧ dv.propose ≠ null⌝ ∗
        swift.exIn c.γxm b x ∗ ghostMapElem c.γsh d (DFrac.own (1 : Qp).half) q ∗
        swift.rowTokO c b x dv rv ∗ swift.msetF ms ∗ Rs ∗ c.env d q }}
      (App (App (App (Val (c.rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"handleMsg"))
        (Val #(interface.mkOk go.int #s))) (Val #d)) (Val #x))
    {{ RET #true; c.ret d x ∗ c.env d q }})

instance swift.slotCap_persistent (c : swift.DC) (MP : GoInterface → IProp netDistGF)
    (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat) (F : IProp netDistGF) :
    Persistent (swift.slotCap c MP γd d x b F) := by
  unfold swift.slotCap; infer_instance

instance swift.slotCapR_persistent (c : swift.DC) (MP : GoInterface → IProp netDistGF)
    (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat) (ms : Loc) (Rs : IProp netDistGF) :
    Persistent (swift.slotCapR c MP γd d x b ms Rs) := by
  unfold swift.slotCapR; infer_instance

/-- The handler's spec (round 22: the frame `Rs` is chosen per use, not at the handler's
creation: `newDesc` states it for the slow set's frame, which mentions the fast set, created
after the handler). Round 33 (table rev 4/5 G-cap): given the frame's slot capability
`slotCapR` (a sequential retirement frees the descriptor from the frame it is lent). Round 42
(D48 (3)): the lent set's resource is `True`, so the set lent to the slot case is `msetF`. -/
def swift.acksHdOk (c : swift.DC) (RC : Loc → w32 → IProp netDistGF) (MP : GoInterface → IProp netDistGF)
    (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat) (hd : GoFunc) : IProp netDistGF :=
  iprop(□ ∀ (Rs : IProp netDistGF) (ms : Loc) (q : GoInterface) (sz : Nat) (mem : w32 → Prop)
      (P : w32 → GoInterface → IProp netDistGF) (A : GoInterface → GoInterface → IProp netDistGF),
      swift.slotCapR c MP γd d x b ms Rs -∗
      replica.mset.handlerOkQ ms q hd sz mem P A (swift.leadAckP c b x) iprop(True)
        (swift.descSt c RC MP γd d x b Rs) (swift.descGone c b x d))

instance swift.acksHdOk_persistent (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat)
    (hd : GoFunc) : Persistent (swift.acksHdOk c RC MP γd d x b hd) := by
  unfold swift.acksHdOk; infer_instance

/-- `x`'s descriptor's owner state in epoch `b` (between messages): the two message sets
(slow at `s` over `SQ`, fast at `f` over `FQ`, one handler `hd` for both with its specs), the
handler's lent state with the slow set's (`setR … true`: `descSt`, the fields, the fast set's
data, `Do`), the slow set's data. (Round 24: the read share of `status` is `descSt`'s
`shOwn`.) Round 33 (table rev 4/5 G-cap): the handler's frame-polymorphic spec `acksHdOk` and
the slot capability `slotCap` for the frame `Do` (instead of two `handlerOkQ` at the rest
frame); callers of `Add` instantiate `acksHdOk` at their actual frame. -/
def swift.descOwn (c : swift.DC) (RC : Loc → w32 → IProp netDistGF) (MP : GoInterface → IProp netDistGF)
    (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat) (Do : IProp netDistGF) :
    IProp netDistGF :=
  iprop(∃ (s f : Loc) (qS qF : GoInterface) (szS szF : Nat) (memS memF : w32 → Prop) (hd : GoFunc),
    swift.acksHdOk c RC MP γd d x b hd ∗ swift.slotCap c MP γd d x b Do ∗
    replica.mset.ownD s qS szS memS (swift.ackP x) swift.ackA (swift.leadAckP c b x) iprop(True) hd ∗
    swift.setR c RC MP γd d x b Do s f qF szF memF hd true)

/-- The leader's fast ack at `l` (read-only) and its witness: it represents the wire ack `f`
(sender, ballot, command, dependencies) and `f`'s protocol witness (`sp.fastAckOk`: the leader
pre-accepted `x` with these dependencies), and its checksum read-only (round 11: the deferred
`SHashesEq`). What `fastAckFromLeader` needs of the leader's ack. -/
def swift.leadWit (c : swift.DC) (l : Loc) (fa : swift.MFastAck) : IProp netDistGF :=
  iprop(∃ f : sp.FastAck, l ↦□ fa ∗
    ⌜fa.Replica' = f.rep ∧ fa.Ballot' = f.bal ∧ toCmdId fa.CmdId' = f.id⌝ ∗
    fa.Dep' ↦*□ (f.dep.map ofCmdId) ∗ sp.fastAckOk c.γ f ∗
    (∃ hs : List swift.SHash, fa.Checksum' ↦*□ hs))

instance swift.leadWit_persistent (c : swift.DC) (l : Loc) (fa : swift.MFastAck) :
    Persistent (swift.leadWit c l fa) := by unfold swift.leadWit; infer_instance

/-- The leader's ack's witness gated by its ballot (round 13): the ack is of another ballot
than the descriptor's epoch `b`, or `leadWit`. (A stale ack of the current leader, e.g. an
`MOptAcks` slow entry of an earlier ballot, reaches `fastAckFromLeader`, whose closure returns at
the ballot check; only an ack of `b` needs the witness.) -/
def swift.leadWitB (c : swift.DC) (b : Nat) (l : Loc) (fa : swift.MFastAck) : IProp netDistGF :=
  iprop(⌜sp.bal fa.Ballot' ≠ b⌝ ∨ swift.leadWit c l fa)

instance swift.leadWitB_persistent (c : swift.DC) (b : Nat) (l : Loc) (fa : swift.MFastAck) :
    Persistent (swift.leadWitB c b l fa) := by unfold swift.leadWitB; infer_instance

/-- Why an ack from replica `k` of ballot `bw` for `x` may enter `x`'s descriptor's sets in
epoch `b` (round 13; `commonCaseFastAck` returns unless `bw` is the replica's ballot): the ack is
of another ballot, or its sender is not `b`'s leader. Round B1 (D81): the two disjuncts that let
the leader's ack in through `commonCaseFastAck` (the replica is `b`'s leader, or it accepted `x`)
are gone: no caller used them (`handleFastAck` sends the leader's ack to `fastAckFromLeader`, a
light slow ack's sender is not its ballot's leader), and `leadAckP` now needs the acceptance. -/
def swift.ackWhy (c : swift.DC) (b : Nat) (x : swift.CommandId) (k bw : w32) : IProp netDistGF :=
  iprop(⌜sp.bal bw ≠ b⌝ ∨ ⌜sp.rid k ≠ sp.leaderOf c.N b⌝)

instance swift.ackWhy_persistent (c : swift.DC) (b : Nat) (x : swift.CommandId) (k bw : w32) :
    Persistent (swift.ackWhy c b x k bw) := by unfold swift.ackWhy; infer_instance

/-- The owner's fields a leader ack's closure writes besides `descF` and the sets (round 10):
`waitingAck` (nil, or the ballot's leader's ack for `x` with its witness, waiting for N2:
`"recheck"` calls `fastAckFromLeader` with it) and `slowPath`. (Round 24: the read share of
`FQ` is `descSt`'s `shOwn`.) -/
def swift.descCore (c : swift.DC) (d : Loc) (x : swift.CommandId) (b : Nat) : IProp netDistGF :=
  iprop(∃ (wa : Loc) (sl : Bool),
    swift.dfld d go!"waitingAck" ↦ wa ∗ swift.dfld d go!"slowPath" ↦ sl ∗
    (⌜wa = null⌝ ∨ ∃ fa : swift.MFastAck,
      ⌜fa.CmdId' = x ∧ sp.rid fa.Replica' = sp.leaderOf c.N b⌝ ∗ swift.leadWit c wa fa))

/-- Who set `proposeDep` (round 14): nobody (`nil`, `newDesc`'s), or a proposal message of `x`
in `b` (`handlePropose`'s P4 prefix, with the message's hashes in `hs`): its dependencies and
hashes read-only, its facts and (change log C22, round 25) its number `numIs` at `seqnum` (`sq`) as the run loop gave it. Round 30 (G15, D27): or a sync entry's
(`handleSyncEntry` writes `proposeDep = e.dep`): its dependencies read-only and the replica's
`sp.accepted` of `x` in `b` (the entry's payload); `handlePropose` keeps it when `proposeDep` is
set, and refutes it with the proposal's fresh row token (`swift.accepted_row`) once `propose` is
nil. (Round 33: moved here from HandlePropose.lean.) Round 47 (46-2, D61 (2); prove-swift §52's
unchecked source): with nobody's or a sync entry's `proposeDep`, `hs` is still `newDesc`'s nil
(`handlePropose` writes `hs` only with the first `proposeDep`, `handleSyncEntry` never), so a sync
entry's descriptor has no hashes (`dv.Hs = []`). -/
def swift.pdOk (c : swift.DC) (b : Nat) (x : swift.CommandId) (pd hs0 : GoSlice) (sq : w64) :
    IProp netDistGF :=
  iprop(⌜pd = slice.nil ∧ hs0 = slice.nil⌝ ∨
    (∃ (cc : sp.Cmd) (ld : Bool) (s : sp.Seq) (B D P : List sp.CmdId) (H : swift.SHash),
      ⌜pd ≠ slice.nil⌝ ∗ pd ↦*□ (D.map ofCmdId) ∗ hs0 ↦*□ [H] ∗
      swift.propFacts c.γ c.N c.r b ld (toCmdId x) cc s B D P H ∗
      sp.numIs c.γ c.r b (toCmdId x) (if ld then sq else W64 (-1))) ∨
    (∃ D : List sp.CmdId, ⌜pd ≠ slice.nil ∧ hs0 = slice.nil⌝ ∗ pd ↦*□ (D.map ofCmdId) ∗
      sp.accepted c.γ c.r b (toCmdId x) ∗
      -- round 58 (D82 (2)): the entry's `MSync` and the replica's prefix `syncSeq M` (for `pdW`)
      ∃ M : sp.SyncMsg, sp.syncIs c.γ b M ∗ sp.locLb c.γ c.r b (sp.syncSeq M) ∗
        ⌜toCmdId x ∈ (sp.syncSeq M).map Prod.fst ∧ (∀ d ∈ D, d ∈ sp.depsIn (sp.syncSeq M) (toCmdId x)) ∧
          D.length < 2 ^ 62⌝))

instance swift.pdOk_persistent (c : swift.DC) (b : Nat) (x : swift.CommandId) (pd hs0 : GoSlice)
    (sq : w64) : Persistent (swift.pdOk c b x pd hs0 sq) := by
  unfold swift.pdOk; infer_instance

/-- The owner's fields outside `descOwnF`'s: `proposeDep`, `seqnum`, and the other half of `hs`
(`descF` has one), with `pdOk` (round 14's proposal halves received, `propsHeld`, are gone with
D16). Round 33 (table rev 4/5 G-def, PF14): and `defered` (written by `newDesc` only, read by
the slot case; `freeDesc` needs it). Moved here from HandlePropose.lean. -/
def swift.descRest (c : swift.DC) (b : Nat) (x : swift.CommandId) (d : Loc) : IProp netDistGF :=
  iprop(∃ (pd hs0 : GoSlice) (sq : w64) (df : GoFunc),
    swift.dfld d go!"proposeDep" ↦ pd ∗ swift.dfld d go!"seqnum" ↦ sq ∗
    typedPointsto (swift.dfld d go!"hs") hs0 (DFrac.own (1 : Qp).half) ∗
    swift.dfld d go!"defered" ↦ df ∗ swift.pdOk c b x pd hs0 sq)

/-- The spec of a leader ack's closure (`fastAckFromLeader`'s `func()`, run by `afterPropagate`)
of `x`'s descriptor in epoch `b` (round 10): from the owner state with the spec-free `OptCondF`
part at the true condition and nothing stored (`ocfRes0`, round 33, table rev 4 §3.6b: `Call`/
`Recall` hand the object back before they run the functions, and the chain passes it down so a
retirement can free it), or, at a follower, from a retired descriptor (an earlier function of
the same run retired it; the closure returns at `delivered.Has`, the a430281 guard), it ends with
the owner state or retired. -/
def swift.closureOk (c : swift.DC) (RC : Loc → w32 → IProp netDistGF) (MP : GoInterface → IProp netDistGF)
    (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat) (Do : IProp netDistGF)
    (g : GoFunc) : IProp netDistGF :=
  iprop({{ iprop(((swift.descOwn c RC MP γd d x b iprop(swift.descCore c d x b ∗ Do) ∗ swift.ocfRes0 d) ∨
        (swift.descDone c b x d ∗ ⌜c.r ≠ sp.leaderOf c.N b⌝))) }}
      (App (Val #g) (Val #()))
    {{ RET #(); iprop(((swift.descOwn c RC MP γd d x b iprop(swift.descCore c d x b ∗ Do) ∗
        swift.ocfRes0 d) ∨ swift.descDone c b x d)) }})

/-- A leader ack's closure that does nothing to the descriptor (round 10): at the ballot's
leader, a stored closure is of an earlier ballot (`r.ballot != msg.Ballot`: it returns). -/
def swift.closureNop (c : swift.DC) (RC : Loc → w32 → IProp netDistGF) (MP : GoInterface → IProp netDistGF)
    (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat) (Do : IProp netDistGF)
    (g : GoFunc) : IProp netDistGF :=
  iprop({{ iprop(swift.descOwn c RC MP γd d x b iprop(swift.descCore c d x b ∗ Do)) }}
      (App (Val #g) (Val #()))
    {{ RET #(); iprop(swift.descOwn c RC MP γd d x b iprop(swift.descCore c d x b ∗ Do)) }})

/-- A stored closure's specs: `closureOk`, and at the ballot's leader `closureNop`, or (G10,
D25; round 28) the leader's own pre-acceptance of `x` in `b` (its ack of `b` stored at a
descriptor without the row token: a second incarnation of `x` in the epoch, reachable; refuted
by `handlePropose` with `handle_stepD`'s fresh token before `Recall` runs the closures). -/
def swift.storedOk (c : swift.DC) (RC : Loc → w32 → IProp netDistGF) (MP : GoInterface → IProp netDistGF)
    (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat) (Do : IProp netDistGF)
    (g : GoFunc) : IProp netDistGF :=
  iprop(□ swift.closureOk c RC MP γd d x b Do g ∗
    (⌜c.r ≠ sp.leaderOf c.N b⌝ ∨ □ swift.closureNop c RC MP γd d x b Do g ∨
      ∃ D : List sp.CmdId, sp.preacc c.γ c.r b (toCmdId x) D))

/-- A stored closure's specs with the pre-acceptance disjunct refuted (round 28, G10:
`handlePropose` with `handle_stepD`'s fresh token, for its `Recall`). -/
def swift.storedOk2 (c : swift.DC) (RC : Loc → w32 → IProp netDistGF) (MP : GoInterface → IProp netDistGF)
    (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat) (Do : IProp netDistGF)
    (g : GoFunc) : IProp netDistGF :=
  iprop(□ swift.closureOk c RC MP γd d x b Do g ∗
    (⌜c.r ≠ sp.leaderOf c.N b⌝ ∨ □ swift.closureNop c RC MP γd d x b Do g))

instance swift.storedOk2_persistent (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId)
    (b : Nat) (Do : IProp netDistGF) (g : GoFunc) :
    Persistent (swift.storedOk2 c RC MP γd d x b Do g) := by
  unfold swift.storedOk2; infer_instance

instance swift.storedOk_persistent (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId)
    (b : Nat) (Do : IProp netDistGF) (g : GoFunc) :
    Persistent (swift.storedOk c RC MP γd d x b Do g) := by
  unfold swift.storedOk; infer_instance

end defs

section defsOcf
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions] [hook.Assumptions]

/-- **The stored closures once the condition holds** (round 29, G14): nothing stored at the false
condition, or every stored closure's specs without G10's pre-acceptance disjunct (`storedOk2`).
Round 28 had `v = true → fs = []` (handlePropose's `Recall` runs them all), but `handleSyncEntry`
sets `propose` without `Recall` (recovery.go:701): closures stored before stay, with `storedOk2`
from `install_sync`. -/
def swift.ocfV (c : swift.DC) (RC : Loc → w32 → IProp netDistGF) (MP : GoInterface → IProp netDistGF)
    (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat) (Do : IProp netDistGF) (v : Bool)
    (fs : List GoFunc) : IProp netDistGF :=
  iprop(⌜v = false⌝ ∨ [∗list] g ∈ fs, swift.storedOk2 c RC MP γd d x b Do g)

instance swift.ocfV_persistent (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId)
    (b : Nat) (Do : IProp netDistGF) (v : Bool) (fs : List GoFunc) :
    Persistent (swift.ocfV c RC MP γd d x b Do v fs) := by
  unfold swift.ocfV; infer_instance

theorem swift.ocfV_nil (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId)
    (b : Nat) (Do : IProp netDistGF) (v : Bool) :
    ⊢ swift.ocfV c RC MP γd d x b Do v [] := by
  iunfold swift.ocfV
  iright; iapply BigSepL.bigSepL_nil.2; itrivial

theorem swift.ocfV_false (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId)
    (b : Nat) (Do : IProp netDistGF) (fs : List GoFunc) :
    ⊢ swift.ocfV c RC MP γd d x b Do false fs := by
  iunfold swift.ocfV
  ileft; ipureintro; rfl

/-- `x`'s descriptor's `afterPropagate` (round 10): the `OptCondF` with its condition on
`proposeHalf`, the condition's state, the stored closures with their specs (`storedOk`: at the
ballot's leader they are no-ops, of earlier ballots: its own ack of the ballot comes after its
pre-acceptance, so the condition is true then, `rowAcc`); (round 12, fork P3) the ballots of
the stored acks, `storedBallots`, duplicate-free and at least as many as the stored closures
(their bound: fewer than `2^32`); (round 28, G10; round 29, G14: `swift.ocfV`) nothing stored once the proposal is set, or only
`storedOk2` closures (a sync entry's). Round 33: the spec-free part is `ocfRes` (C3). -/
def swift.descOcf (c : swift.DC) (RC : Loc → w32 → IProp netDistGF) (MP : GoInterface → IProp netDistGF)
    (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat) (Do : IProp netDistGF) :
    IProp netDistGF :=
  iprop(∃ (cf : Loc) (cond : GoFunc) (fs : List GoFunc) (v : Bool),
    swift.ocfRes d cf cond fs v ∗
    □ hook.ocf.condOk cond (swift.proposeHalf d) ∗ swift.ocfV c RC MP γd d x b Do v fs ∗
    ([∗list] g ∈ fs, swift.storedOk c RC MP γd d x b Do g))

/-- `x`'s descriptor's whole owner state for the acks (round 10): `descOwn` with `descCore`
and the frame `Do`, and `afterPropagate` (`descOcf`, outside what the sets' handler is lent). -/
def swift.descOwnF (c : swift.DC) (RC : Loc → w32 → IProp netDistGF) (MP : GoInterface → IProp netDistGF)
    (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat) (Do : IProp netDistGF) :
    IProp netDistGF :=
  iprop(swift.descOwn c RC MP γd d x b iprop(swift.descCore c d x b ∗ Do) ∗
    swift.descOcf c RC MP γd d x b Do)

end defsOcf

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [hook.Assumptions]

/-- **`r.getCmdDesc(y, nil, nil)` from a descriptor's owner at its record `c`** (round 37; table rev
8 §3.14 G-hdep, plan R8.1/R8b.1; replaces round 33's `depSpecI`, stated for every `c` and unprovable
at an abstract record): `y`'s descriptor (created if needed, not if `y` was delivered: `nil`),
whose successors' lock persists; the caller's epoch share back, whole. An `IProp` per record:
proved for the owner records (`RunX.dcK g k`) by the Löb bundle (a creation forks `handleDesc`),
and a premise of the handler's spec (`acksHdOkB`). (The lock's persistence is false with the
descriptor pool, finding SWB-F4.) -/
def swift.depSpecR (c : swift.DC) : IProp netDistGF :=
  iprop(□ ∀ (d : Loc) (q : Qp) (b : Nat) (bw : w32) (stp rcp : Loc) (y : swift.CommandId),
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
        c.ctx ∗ swift.epochRd c.γe c.γxe c.rp c.rr q b bw stp rcp ∗ swift.shOwnR c d b q }}
      (App (App (App (Val (c.rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"getCmdDesc"))
        (Val #y)) (Val #interface.nil)) (Val #slice.nil))
    {{ (dd : Loc), RET #dd; swift.epochRd c.γe c.γxe c.rp c.rr q b bw stp rcp ∗ swift.shOwnR c d b q ∗
        (⌜dd = null⌝ ∨ sync.isMutex (swift.dfld dd go!"successorsL") (swift.succInv dd)) }})

instance swift.depSpecR_persistent (c : swift.DC) : Persistent (swift.depSpecR c) := by
  unfold swift.depSpecR; infer_instance

/-- **The handler's spec at every record of a base** (round 35, table rev 7b §3.12, G-hrec):
`newDesc` makes the handler before the owner's kind is known (T2), so the owner state (T8, at its
record `RunX.dcK g k`) takes the spec at its own record. Round 37 (table rev 8 G-hdep): given the
record's `depSpecR` (the handler looks its dependencies up from the owner's environment), which
the owner supplies from the Löb bundle. -/
def swift.acksHdOkB (c : swift.DC) (RC : Loc → w32 → IProp netDistGF) (MP : GoInterface → IProp netDistGF)
    (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat) (hd : GoFunc) : IProp netDistGF :=
  iprop(□ ∀ c' : swift.DC, ⌜c'.base = c.base⌝ → swift.depSpecR c' -∗ swift.acksHdOk c' RC MP γd d x b hd)

instance swift.acksHdOkB_persistent (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat)
    (hd : GoFunc) : Persistent (swift.acksHdOkB c RC MP γd d x b hd) := by
  unfold swift.acksHdOkB; infer_instance

/-- `getFastAndSlowAcksHandler(r, desc)`: the handler of `x`'s descriptor's two message sets
(epoch `b`): with the leader's ack (`leadAckP`) it commits `x` (the ghost commit unless the row
already says committed, SWB-3), records `x` as a successor of each dependency's descriptor, and
delivers `x`; it gives back what it was lent, or `exIn` (`x` executed; a sequential descriptor
retired by its history slot, SWB-2). Any quorum, any acks' predicates, any state of the closures. -/
abbrev swift.getFastAndSlowAcksHandler.specI (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) : Prop :=
  ∀ (c : swift.DC) (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      c.ctx }}
    (App (App (Val (@! swift.getFastAndSlowAcksHandler)) (Val #c.rp)) (Val #d))
  {{ (hd : GoFunc), RET #hd; swift.acksHdOkB c RC MP γd d x b hd }}

/-- `r.commonCaseFastAck(msg, desc)` by `x`'s descriptor's owner: a non-leader's fast ack or a
slow ack (`Dep = nil`) for `x`, added to the slow set (a slow ack) and the fast set; either
may complete a quorum and run the handler. If the sender is the ballot's leader the ack goes
in as the leader's (`isLeader`), so then the replica must have accepted `x` (or be the
leader). Afterwards the owner state, or `x` executed (a sequential descriptor retired). The caller's
epoch pin (round 43, D51 (c): in `shOwnR`, at the loan's `q`) says the epoch is still `b` when
the retired descriptor's caller checks `delivered` (SWB-5). Round 33 (table rev 5, C3): the `OptCondF` part `ocfRes` (any state)
is a separate premise, which the callee adds to `Add`'s frame (a sequential retirement frees it). -/
abbrev swift.Replica.commonCaseFastAck.specIc (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (c : swift.DC) : Prop :=
  ∀ (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat) (Do : IProp netDistGF)
    (l : Loc) (fa : swift.MFastAck) (cf : Loc) (cond : GoFunc) (fs : List GoFunc) (v : Bool),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      c.ctx ∗ swift.descOwn c RC MP γd d x b Do ∗ swift.ocfRes d cf cond fs v ∗
      l ↦□ fa ∗ (∃ D : List swift.CommandId, fa.Dep' ↦*□ D) ∗
      ⌜fa.CmdId' = x⌝ ∗ swift.ackWhy c b x fa.Replica' fa.Ballot' }}
    (App (App (Val (c.rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"commonCaseFastAck"))
      (Val #l)) (Val #d))
  {{ RET #(); ((swift.descOwn c RC MP γd d x b Do ∗ swift.ocfRes d cf cond fs v) ∨
      swift.descDone c b x d) }}

/-- `swift.Replica.commonCaseFastAck.specI` at every record (round 44, D53 (1): the per-record form `swift.Replica.commonCaseFastAck.specIc`). -/
abbrev swift.Replica.commonCaseFastAck.specI (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) : Prop :=
  ∀ c : swift.DC, swift.Replica.commonCaseFastAck.specIc RC MP c

/-- `newFastAck()` on a replica (**hypothesis**: the fast-ack pool may be on, `poolLevel > 1`;
the pool's objects are owned): a fresh `*MFastAck`. -/
abbrev swift.newFastAckR.spec : Prop :=
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift }}
    (App (Val (@! swift.newFastAck)) (Val #()))
  {{ (l : Loc), RET #l; ∃ fa : swift.MFastAck, l ↦ fa }}

/-- `r.handleLightSlowAck(msg, desc)` by `x`'s descriptor's owner: a slow ack for `x` from
`msg.Replica` (read-only), as a fast ack without dependencies through `commonCaseFastAck`.
(The sender is not the ballot's leader, or the replica accepted `x`: the frozen witness of a
light slow ack does not say the former, HUB-REQUEST SWB-H1.) Round 33 (C3): with `ocfRes` as
`commonCaseFastAck`. -/
abbrev swift.Replica.handleLightSlowAck.specIc (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (c : swift.DC) : Prop :=
  ∀ (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat) (Do : IProp netDistGF)
    (l : Loc) (sa : swift.MLightSlowAck) (cf : Loc) (cond : GoFunc) (fs : List GoFunc) (v : Bool),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      c.ctx ∗ (∃ u : Bool, globalAddr swift.useFastAckPool ↦□ u) ∗
      swift.descOwn c RC MP γd d x b Do ∗ swift.ocfRes d cf cond fs v ∗
      l ↦□ sa ∗ ⌜sa.CmdId' = x⌝ ∗
      swift.ackWhy c b x sa.Replica' sa.Ballot' }}
    (App (App (Val (c.rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"handleLightSlowAck"))
      (Val #l)) (Val #d))
  {{ RET #(); ((swift.descOwn c RC MP γd d x b Do ∗ swift.ocfRes d cf cond fs v) ∨
      swift.descDone c b x d) }}

/-- `swift.Replica.handleLightSlowAck.specI` at every record (round 44, D53 (1): the per-record form `swift.Replica.handleLightSlowAck.specIc`). -/
abbrev swift.Replica.handleLightSlowAck.specI (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) : Prop :=
  ∀ c : swift.DC, swift.Replica.handleLightSlowAck.specIc RC MP c

end specs

section specsOcf
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [hook.Assumptions]

/-- `r.fastAckFromLeader(msg, desc)` by `x`'s descriptor's owner, `msg` the ballot's leader's
fast ack for `x` with its witness (round 10: over the whole owner state `descOwnF`; any ballot
of the ack, the closure checks it). `AC`: the replica's further fields the closure reads
(persistent; `swift.ackCtx`, FastAck.lean). -/
abbrev swift.Replica.fastAckFromLeader.specIc (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (AC : swift.DC → IProp netDistGF) (c : swift.DC) : Prop :=
  ∀ (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat) (Do : IProp netDistGF)
    (l : Loc) (fa : swift.MFastAck),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      c.ctx ∗ □ AC c ∗ swift.descOwnF c RC MP γd d x b Do ∗ l ↦□ fa ∗
      (∃ D : List swift.CommandId, fa.Dep' ↦*□ D) ∗ ⌜fa.CmdId' = x⌝ ∗ ⌜sp.rid fa.Replica' = sp.leaderOf c.N b⌝ ∗ swift.leadWitB c b l fa }}
    (App (App (Val (c.rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"fastAckFromLeader"))
      (Val #l)) (Val #d))
  {{ RET #(); swift.descOwnF c RC MP γd d x b Do ∨ swift.descDone c b x d }}

/-- `swift.Replica.fastAckFromLeader.specI` at every record (round 44, D53 (1): the per-record form `swift.Replica.fastAckFromLeader.specIc`). -/
abbrev swift.Replica.fastAckFromLeader.specI (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (AC : swift.DC → IProp netDistGF) : Prop :=
  ∀ c : swift.DC, swift.Replica.fastAckFromLeader.specIc RC MP AC c

/-- `r.handleFastAck(msg, desc)` by `x`'s descriptor's owner: the leader's ack (with its witness,
when it is the leader's) to `fastAckFromLeader`, another's to `commonCaseFastAck`. -/
abbrev swift.Replica.handleFastAck.specIc (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (AC : swift.DC → IProp netDistGF) (c : swift.DC) : Prop :=
  ∀ (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat) (Do : IProp netDistGF)
    (l : Loc) (fa : swift.MFastAck),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      c.ctx ∗ □ AC c ∗ swift.descOwnF c RC MP γd d x b Do ∗ l ↦□ fa ∗
      (∃ D : List swift.CommandId, fa.Dep' ↦*□ D) ∗ ⌜fa.CmdId' = x ∧ 0 ≤ sint.Z fa.Replica'⌝ ∗
      (⌜sp.rid fa.Replica' ≠ sp.leaderOf c.N b⌝ ∨ swift.leadWitB c b l fa) }}
    (App (App (Val (c.rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"handleFastAck"))
      (Val #l)) (Val #d))
  {{ RET #(); swift.descOwnF c RC MP γd d x b Do ∨ swift.descDone c b x d }}

/-- `swift.Replica.handleFastAck.specI` at every record (round 44, D53 (1): the per-record form `swift.Replica.handleFastAck.specIc`). -/
abbrev swift.Replica.handleFastAck.specI (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (AC : swift.DC → IProp netDistGF) : Prop :=
  ∀ c : swift.DC, swift.Replica.handleFastAck.specIc RC MP AC c

/-- **The history slot's case `r.handleMsg(slot, desc, cmdId)`** (table rev 4/5 T16a-c; both
owner kinds; replaces `slotSpecI`): from the slot, `x` executed in `b`, the descriptor's whole
owner state at rest without its epoch share's reader parts (fields, row token, `γsh` half,
sets, `descCore`, `descRest`, `ocfRes` at any state, the kind's frame `c.kf`) and, for a
goroutine, its epoch share and `shOwnR` (with its pin, round 43) (for a sequential descriptor only its
loan environment: the run loop keeps the epoch share), the slot case retires the descriptor
(`Remove`, the deposit of the token with an executed record, a goroutine's loan back and exit)
and gives the kind's residue. -/
abbrev swift.Replica.handleMsg.slotSpecD (MP : GoInterface → IProp netDistGF) : Prop :=
  ∀ (c : swift.DC) (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat) (dv : swift.DescV)
    (rv : swift.RowV) (s : w64) (q : Qp) (sl fa cf : Loc) (cond : GoFunc) (fs : List GoFunc) (v : Bool),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      c.ctx ∗ MP (interface.mkOk go.int #s) ∗ swift.exIn c.γxm b x ∗
      ⌜dv.seq = c.sq ∧ dv.propose ≠ null⌝ ∗ swift.descF d γd MP dv ∗ swift.rowTokO c b x dv rv ∗
      ghostMapElem c.γsh d (DFrac.own (1 : Qp).half) q ∗
      swift.dfld d go!"slowPathH" ↦ sl ∗ swift.dfld d go!"fastPathH" ↦ fa ∗
      swift.msetF sl ∗ swift.msetF fa ∗ swift.descCore c d x b ∗
      swift.descRest c b x d ∗ swift.ocfRes d cf cond fs v ∗ c.kf d x ∗
      (if c.sq then c.env d q else
        ∃ (bw : w32) (stp rcp : Loc), swift.epochRd c.γe c.γxe c.rp c.rr q b bw stp rcp ∗
          swift.shOwnR c d b q) }}
    (App (App (App (Val (c.rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"handleMsg"))
      (Val #(interface.mkOk go.int #s))) (Val #d)) (Val #x))
  {{ RET #true; if c.sq then c.ret d x ∗ c.env d q else c.ret d x }}

end specsOcf

section shLemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions]

/-- `shOwn`'s `status` and `FQ` shares out, and back (round 24). -/
theorem swift.shOwn_open (c : swift.DC) (d : Loc) (b : Nat) (q : Qp) :
    swift.shOwn c d b q ⊢
      ∃ (st : w64) (fq : GoInterface) (szF : Nat) (memF : w32 → Prop),
        typedPointsto (swift.fld c.rp go!"status") st (DFrac.own q) ∗
        typedPointsto (swift.fld c.rp go!"FQ") fq (DFrac.own q) ∗
        replica.mset.quorumIs fq szF memF ∗ ⌜∀ i : w32, memF i → sp.rid i ∈ sp.AQ c.N b⌝ ∗
        (typedPointsto (swift.fld c.rp go!"status") st (DFrac.own q) -∗
          typedPointsto (swift.fld c.rp go!"FQ") fq (DFrac.own q) -∗ swift.shOwn c d b q) := by
  iintro H
  iunfold swift.shOwn at H
  icases H with ⟨He, HR⟩
  iunfold swift.shOwnR at HR
  icases HR with ⟨⟨%st, Hst⟩, ⟨%fq, %szF, %memF, HFQ, #HqF, %HAQ⟩, Hrd, Henv, Hpin⟩
  iexists st, fq, szF, memF
  iframe Hst HFQ HqF
  isplitr
  · ipureintro; exact HAQ.1
  iintro Hst HFQ
  iunfold swift.shOwn
  iframe He
  iunfold swift.shOwnR
  iframe Hrd Henv Hpin
  isplitl [Hst]
  · iexists st; iexact Hst
  iexists fq, szF, memF
  iframe HFQ HqF
  ipureintro; exact HAQ

/-- **E7** (table rev 3-5): `b`'s leader is a member of `FQ`'s quorum (`shOwnR`'s fact). -/
theorem swift.shOwnR_E7 (c : swift.DC) (d : Loc) (b : Nat) (q : Qp) :
    swift.shOwnR c d b q ⊢
      ∃ (fq : GoInterface) (szF : Nat) (memF : w32 → Prop),
        typedPointsto (swift.fld c.rp go!"FQ") fq (DFrac.own q) ∗
        replica.mset.quorumIs fq szF memF ∗
        ⌜(∀ i : w32, memF i → sp.rid i ∈ sp.AQ c.N b) ∧
          (∀ i : w32, 0 ≤ sint.Z i → sp.rid i = sp.leaderOf c.N b → memF i)⌝ ∗
        (typedPointsto (swift.fld c.rp go!"FQ") fq (DFrac.own q) -∗ swift.shOwnR c d b q) := by
  iintro HR
  iunfold swift.shOwnR at HR
  icases HR with ⟨Hst, ⟨%fq, %szF, %memF, HFQ, #HqF, %HAQ⟩, Hrd, Henv, Hpin⟩
  iexists fq, szF, memF
  iframe HFQ HqF
  isplitr
  · ipureintro; exact HAQ
  iintro HFQ
  iunfold swift.shOwnR
  iframe Hst Hrd Henv Hpin
  iexists fq, szF, memF
  iframe HFQ HqF
  ipureintro; exact HAQ

/-- `shOwnR`'s reader bundle out, and back. -/
theorem swift.shOwnR_rdr (c : swift.DC) (d : Loc) (b : Nat) (q : Qp) :
    swift.shOwnR c d b q ⊢
      swift.ownRdr c.rp c.γdl ∗ (swift.ownRdr c.rp c.γdl -∗ swift.shOwnR c d b q) := by
  iintro H
  iunfold swift.shOwnR at H
  icases H with ⟨Hst, HFQ, Hrd, Henv, Hpin⟩
  iframe Hrd
  iintro Hrd
  iunfold swift.shOwnR
  iframe

/-- `shOwnR`'s loan environment out, and back. -/
theorem swift.shOwnR_env (c : swift.DC) (d : Loc) (b : Nat) (q : Qp) :
    swift.shOwnR c d b q ⊢ c.env d q ∗ (c.env d q -∗ swift.shOwnR c d b q) := by
  iintro H
  iunfold swift.shOwnR at H
  icases H with ⟨Hst, HFQ, Hrd, Henv, Hpin⟩
  iframe Henv
  iintro Henv
  iunfold swift.shOwnR
  iframe

/-- `shOwn`'s reader bundle out, and back (round 25, SW4). -/
theorem swift.shOwn_rdr (c : swift.DC) (d : Loc) (b : Nat) (q : Qp) :
    swift.shOwn c d b q ⊢
      swift.ownRdr c.rp c.γdl ∗ (swift.ownRdr c.rp c.γdl -∗ swift.shOwn c d b q) := by
  iintro H
  iunfold swift.shOwn at H
  icases H with ⟨He, HR⟩
  ihave ⟨Hrd, HRb⟩ := swift.shOwnR_rdr c d b q $$ HR
  iframe Hrd
  iintro Hrd
  iunfold swift.shOwn
  iframe He
  iapply HRb $$ Hrd

/-- `descSt`'s reader bundle out, and back (round 25, SW4). -/
theorem swift.descSt_rdr (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat)
    (Rs : IProp netDistGF) :
    swift.descSt c RC MP γd d x b Rs ⊢
      swift.ownRdr c.rp c.γdl ∗ (swift.ownRdr c.rp c.γdl -∗ swift.descSt c RC MP γd d x b Rs) := by
  iintro H
  iunfold swift.descSt at H
  icases H with ⟨%q, %bw, %stp, %rcp, %dv, %rv, Hrd, Hsh, Hrest⟩
  ihave ⟨HrdR, Hshr⟩ := swift.shOwn_rdr c d b q $$ Hsh
  iframe HrdR
  iintro HrdR
  ihave Hsh := Hshr $$ HrdR
  iunfold swift.descSt
  iexists q, bw, stp, rcp, dv, rv
  iframe

/-- `setR`'s reader bundle out, and back (round 25, SW4). -/
theorem swift.setR_rdr (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat)
    (Do : IProp netDistGF) (s f : Loc) (qO : GoInterface) (szO : Nat) (memO : w32 → Prop)
    (hd : GoFunc) (slow : Bool) :
    swift.setR c RC MP γd d x b Do s f qO szO memO hd slow ⊢
      swift.ownRdr c.rp c.γdl ∗
        (swift.ownRdr c.rp c.γdl -∗ swift.setR c RC MP γd d x b Do s f qO szO memO hd slow) := by
  unfold swift.setR
  exact swift.descSt_rdr c RC MP γd d x b _

/-- `descGone`'s reader bundle out, and back (round 25, SW4). -/
theorem swift.descGone_rdr (c : swift.DC) (b : Nat) (x : swift.CommandId) (d : Loc) :
    swift.descGone c b x d ⊢
      swift.ownRdr c.rp c.γdl ∗ (swift.ownRdr c.rp c.γdl -∗ swift.descGone c b x d) := by
  iintro H
  iunfold swift.descGone at H
  icases H with ⟨%Hsq, #Hex, Hret, %q, %bw, %stp, %rcp, Hrd, Hsh⟩
  ihave ⟨HrdR, Hshr⟩ := swift.shOwnR_rdr c d b q $$ Hsh
  iframe HrdR
  iintro HrdR
  ihave Hsh := Hshr $$ HrdR
  iunfold swift.descGone
  iframe Hex Hret
  isplitr
  · ipureintro; exact Hsq
  iexists q, bw, stp, rcp
  iframe

/-- `descOwn`'s reader bundle out, and back (round 25, SW4). -/
theorem swift.descOwn_rdr (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat)
    (Do : IProp netDistGF) :
    swift.descOwn c RC MP γd d x b Do ⊢
      swift.ownRdr c.rp c.γdl ∗ (swift.ownRdr c.rp c.γdl -∗ swift.descOwn c RC MP γd d x b Do) := by
  iintro H
  iunfold swift.descOwn at H
  icases H with ⟨%s, %f, %qS, %qF, %szS, %szF, %memS, %memF, %hd, #HhS, #HhF, HdS, HR⟩
  ihave ⟨HrdR, HRr⟩ := swift.setR_rdr c RC MP γd d x b Do s f qF szF memF hd true $$ HR
  iframe HrdR
  iintro HrdR
  ihave HR := HRr $$ HrdR
  iunfold swift.descOwn
  iexists s, f, qS, qF, szS, szF, memS, memF, hd
  iframe HhS HhF HdS HR

/-- `shOwn_open` with the reader bundle out too (round 25, SW4). -/
theorem swift.shOwn_openR (c : swift.DC) (d : Loc) (b : Nat) (q : Qp) :
    swift.shOwn c d b q ⊢
      ∃ (st : w64) (fq : GoInterface) (szF : Nat) (memF : w32 → Prop),
        typedPointsto (swift.fld c.rp go!"status") st (DFrac.own q) ∗
        typedPointsto (swift.fld c.rp go!"FQ") fq (DFrac.own q) ∗
        replica.mset.quorumIs fq szF memF ∗ ⌜∀ i : w32, memF i → sp.rid i ∈ sp.AQ c.N b⌝ ∗
        swift.ownRdr c.rp c.γdl ∗ swift.epochPinQ c.γxp q b ∗
        (typedPointsto (swift.fld c.rp go!"status") st (DFrac.own q) -∗
          typedPointsto (swift.fld c.rp go!"FQ") fq (DFrac.own q) -∗ swift.ownRdr c.rp c.γdl -∗
          swift.epochPinQ c.γxp q b -∗ swift.shOwn c d b q) := by
  iintro H
  iunfold swift.shOwn at H
  icases H with ⟨He, HR⟩
  iunfold swift.shOwnR at HR
  icases HR with ⟨⟨%st, Hst⟩, ⟨%fq, %szF, %memF, HFQ, #HqF, %HAQ⟩, Hrd, Henv, Hpin⟩
  iexists st, fq, szF, memF
  iunfold swift.epochPinQ
  iframe Hst HFQ HqF Hrd Hpin
  isplitr
  · ipureintro; exact HAQ.1
  iintro Hst HFQ Hrd Hpin
  iunfold swift.shOwn
  iframe He
  iunfold swift.shOwnR
  iframe Hrd Henv Hpin
  isplitl [Hst]
  · iexists st; iexact Hst
  iexists fq, szF, memF
  iframe HFQ HqF
  ipureintro; exact HAQ

/-- A retired descriptor's epoch part's reader bundle out, and back (round 25, SW4; round 33:
over `shOwnR`). -/
theorem swift.grd_rdr (c : swift.DC) (b : Nat) (d : Loc) :
    (∃ (q : Qp) (bw : w32) (stp rcp : Loc), swift.epochRd c.γe c.γxe c.rp c.rr q b bw stp rcp ∗
      swift.shOwnR c d b q) ⊢
      swift.ownRdr c.rp c.γdl ∗ (swift.ownRdr c.rp c.γdl -∗
        ∃ (q : Qp) (bw : w32) (stp rcp : Loc), swift.epochRd c.γe c.γxe c.rp c.rr q b bw stp rcp ∗
          swift.shOwnR c d b q) := by
  iintro ⟨%q, %bw, %stp, %rcp, Hrd, Hsh⟩
  ihave ⟨HrdR, Hshr⟩ := swift.shOwnR_rdr c d b q $$ Hsh
  iframe HrdR
  iintro HrdR
  ihave Hsh := Hshr $$ HrdR
  iexists q, bw, stp, rcp
  iframe


/-! ### The pin with the reader (round 43, table §3R11b, D51 (c))

The SWB-5 checks (`delivered.Has` with `epochPinQ_agree`) and `markAccepted`/`depsAccepted` take the
owner's pin from the `shOwnR` they open for the reader, at its own `q`, and put both back. -/

/-- `shOwnR`'s pin out, and back at the same `q`. -/
theorem swift.shOwnR_pin (c : swift.DC) (d : Loc) (b : Nat) (q : Qp) :
    swift.shOwnR c d b q ⊢
      swift.epochPinQ c.γxp q b ∗ (swift.epochPinQ c.γxp q b -∗ swift.shOwnR c d b q) := by
  iintro H
  iunfold swift.shOwnR at H
  icases H with ⟨Hst, HFQ, Hrd, Henv, Hpin⟩
  iunfold swift.epochPinQ
  iframe Hpin
  iintro Hpin
  iunfold swift.shOwnR
  iframe

/-- `shOwnR`'s reader bundle and pin out, and back. -/
theorem swift.shOwnR_rdrP (c : swift.DC) (d : Loc) (b : Nat) (q : Qp) :
    swift.shOwnR c d b q ⊢
      swift.ownRdr c.rp c.γdl ∗ swift.epochPinQ c.γxp q b ∗
        (swift.ownRdr c.rp c.γdl -∗ swift.epochPinQ c.γxp q b -∗ swift.shOwnR c d b q) := by
  iintro H
  iunfold swift.shOwnR at H
  icases H with ⟨Hst, HFQ, Hrd, Henv, Hpin⟩
  iunfold swift.epochPinQ
  iframe Hrd Hpin
  iintro Hrd Hpin
  iunfold swift.shOwnR
  iframe

/-- `descSt`'s reader bundle and pin out at its `q`, and back. -/
theorem swift.descSt_rdrP (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat)
    (Rs : IProp netDistGF) :
    swift.descSt c RC MP γd d x b Rs ⊢
      ∃ q : Qp, swift.ownRdr c.rp c.γdl ∗ swift.epochPinQ c.γxp q b ∗
        (swift.ownRdr c.rp c.γdl -∗ swift.epochPinQ c.γxp q b -∗ swift.descSt c RC MP γd d x b Rs) := by
  iintro H
  iunfold swift.descSt at H
  icases H with ⟨%q, %bw, %stp, %rcp, %dv, %rv, Hrd, Hsh, Hrest⟩
  iunfold swift.shOwn at Hsh
  icases Hsh with ⟨He, HR⟩
  ihave ⟨HrdR, Hpin, Hshr⟩ := swift.shOwnR_rdrP c d b q $$ HR
  iexists q
  iframe HrdR Hpin
  iintro HrdR Hpin
  ihave HR := Hshr $$ HrdR Hpin
  iunfold swift.descSt
  iexists q, bw, stp, rcp, dv, rv
  iframe
  iunfold swift.shOwn
  iframe

/-- `setR`'s reader bundle and pin out, and back. -/
theorem swift.setR_rdrP (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat)
    (Do : IProp netDistGF) (s f : Loc) (qO : GoInterface) (szO : Nat) (memO : w32 → Prop)
    (hd : GoFunc) (slow : Bool) :
    swift.setR c RC MP γd d x b Do s f qO szO memO hd slow ⊢
      ∃ q : Qp, swift.ownRdr c.rp c.γdl ∗ swift.epochPinQ c.γxp q b ∗
        (swift.ownRdr c.rp c.γdl -∗ swift.epochPinQ c.γxp q b -∗
          swift.setR c RC MP γd d x b Do s f qO szO memO hd slow) := by
  unfold swift.setR
  exact swift.descSt_rdrP c RC MP γd d x b _

/-- `descGone`'s reader bundle and pin out at its `q`, and back. -/
theorem swift.descGone_rdrP (c : swift.DC) (b : Nat) (x : swift.CommandId) (d : Loc) :
    swift.descGone c b x d ⊢
      ∃ q : Qp, swift.ownRdr c.rp c.γdl ∗ swift.epochPinQ c.γxp q b ∗
        (swift.ownRdr c.rp c.γdl -∗ swift.epochPinQ c.γxp q b -∗ swift.descGone c b x d) := by
  iintro H
  iunfold swift.descGone at H
  icases H with ⟨%Hsq, #Hex, Hret, %q, %bw, %stp, %rcp, Hrd, Hsh⟩
  ihave ⟨HrdR, Hpin, Hshr⟩ := swift.shOwnR_rdrP c d b q $$ Hsh
  iexists q
  iframe HrdR Hpin
  iintro HrdR Hpin
  ihave Hsh := Hshr $$ HrdR Hpin
  iunfold swift.descGone
  iframe Hex Hret
  isplitr
  · ipureintro; exact Hsq
  iexists q, bw, stp, rcp
  iframe

/-- `descOwn`'s reader bundle and pin out at its `q`, and back. -/
theorem swift.descOwn_rdrP (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat)
    (Do : IProp netDistGF) :
    swift.descOwn c RC MP γd d x b Do ⊢
      ∃ q : Qp, swift.ownRdr c.rp c.γdl ∗ swift.epochPinQ c.γxp q b ∗
        (swift.ownRdr c.rp c.γdl -∗ swift.epochPinQ c.γxp q b -∗ swift.descOwn c RC MP γd d x b Do) := by
  iintro H
  iunfold swift.descOwn at H
  icases H with ⟨%s, %f, %qS, %qF, %szS, %szF, %memS, %memF, %hd, #HhS, #HhF, HdS, HR⟩
  ihave ⟨%q, HrdR, Hpin, HRr⟩ := swift.setR_rdrP c RC MP γd d x b Do s f qF szF memF hd true $$ HR
  iexists q
  iframe HrdR Hpin
  iintro HrdR Hpin
  ihave HR := HRr $$ HrdR Hpin
  iunfold swift.descOwn
  iexists s, f, qS, qF, szS, szF, memS, memF, hd
  iframe HhS HhF HdS HR

/-- A retired descriptor's epoch part's reader bundle and pin out, and back. -/
theorem swift.grd_rdrP (c : swift.DC) (b : Nat) (d : Loc) :
    (∃ (q : Qp) (bw : w32) (stp rcp : Loc), swift.epochRd c.γe c.γxe c.rp c.rr q b bw stp rcp ∗
      swift.shOwnR c d b q) ⊢
      ∃ q' : Qp, swift.ownRdr c.rp c.γdl ∗ swift.epochPinQ c.γxp q' b ∗
        (swift.ownRdr c.rp c.γdl -∗ swift.epochPinQ c.γxp q' b -∗
          ∃ (q : Qp) (bw : w32) (stp rcp : Loc), swift.epochRd c.γe c.γxe c.rp c.rr q b bw stp rcp ∗
            swift.shOwnR c d b q) := by
  iintro ⟨%q, %bw, %stp, %rcp, Hrd, Hsh⟩
  ihave ⟨HrdR, Hpin, Hshr⟩ := swift.shOwnR_rdrP c d b q $$ Hsh
  iexists q
  iframe HrdR Hpin
  iintro HrdR Hpin
  ihave Hsh := Hshr $$ HrdR Hpin
  iexists q, bw, stp, rcp
  iframe


/-- `rowTokO` with the proposal set: the token (G7, round 28). -/
theorem swift.rowTokO_tok (c : swift.DC) (b : Nat) (x : swift.CommandId) (dv : swift.DescV)
    (rv : swift.RowV) (h : dv.propose ≠ null) :
    swift.rowTokO c b x dv rv ⊢
      swift.rowTok c.γo b (toCmdId x) rv ∗ swift.slotT c (b, toCmdId x) := by
  iintro H
  iunfold swift.rowTokO at H
  icases H with (H | ⟨%Hn, -⟩)
  · iexact H
  · exact absurd Hn.2 h

/-- `rowTokO` of a token (with its slot, round 34). -/
theorem swift.rowTokO_of (c : swift.DC) (b : Nat) (x : swift.CommandId) (dv : swift.DescV)
    (rv : swift.RowV) :
    swift.rowTok c.γo b (toCmdId x) rv ∗ swift.slotT c (b, toCmdId x) ⊢
      swift.rowTokO c b x dv rv := by
  iintro H; iunfold swift.rowTokO; ileft; iexact H

/-- `rowTokO_of`, curried (round 34). -/
theorem swift.rowTokO_of2 (c : swift.DC) (b : Nat) (x : swift.CommandId) (dv : swift.DescV)
    (rv : swift.RowV) :
    ⊢ swift.rowTok c.γo b (toCmdId x) rv -∗ swift.slotT c (b, toCmdId x) -∗
      swift.rowTokO c b x dv rv := by
  iintro H Hs; iunfold swift.rowTokO; ileft; iframe

/-- `rowTokO` across a change of the descriptor's values keeping `propose` and the committed
phase. -/
theorem swift.rowTokO_mono (c : swift.DC) (b : Nat) (x : swift.CommandId) (dv dv' : swift.DescV)
    (rv : swift.RowV) (hp : dv'.propose = dv.propose)
    (hph : dv'.phase = swift.phCOMMIT → dv.phase = swift.phCOMMIT) :
    swift.rowTokO c b x dv rv ⊢ swift.rowTokO c b x dv' rv := by
  iintro H
  iunfold swift.rowTokO at H
  iunfold swift.rowTokO
  icases H with (H | ⟨%Hn, (%Hc | %Hc | #Hc), Hs⟩)
  · ileft; iexact H
  · iright; iframe Hs; isplitr
    · ipureintro; exact ⟨Hn.1, by rw [hp]; exact Hn.2⟩
    · ileft; ipureintro; exact fun h => Hc (hph h)
  · iright; iframe Hs; isplitr
    · ipureintro; exact ⟨Hn.1, by rw [hp]; exact Hn.2⟩
    · iright; ileft; ipureintro; exact Hc
  · iright; iframe Hs; isplitr
    · ipureintro; exact ⟨Hn.1, by rw [hp]; exact Hn.2⟩
    · iright; iright; iexact Hc

/-- `rowTokO` at any phase, given the deferred commit's justification: the token (the caller
does the ghost commit), or tokenless at the new values. -/
theorem swift.rowTokO_commit (c : swift.DC) (b : Nat) (x : swift.CommandId) (dv dv' : swift.DescV)
    (rv : swift.RowV) (hp : dv'.propose = dv.propose) :
    swift.rowTokO c b x dv rv ∗ (⌜c.r = sp.leaderOf c.N b⌝ ∨ sp.accepted c.γ c.r b (toCmdId x)) ⊢
      (swift.rowTok c.γo b (toCmdId x) rv ∗ swift.slotT c (b, toCmdId x)) ∨
        (⌜rv = swift.rowEmpty ∧ dv.propose = null⌝ ∗ swift.rowTokO c b x dv' rv) := by
  iintro ⟨H, #Hj⟩
  iunfold swift.rowTokO at H
  icases H with (H | ⟨%Hn, -, Hs⟩)
  · ileft; iexact H
  · iright; isplitr
    · ipureintro; exact Hn
    iunfold swift.rowTokO; iright; iframe Hs; isplitr
    · ipureintro; exact ⟨Hn.1, by rw [hp]; exact Hn.2⟩
    · iright; iexact Hj

/-- With the condition's state at `true` (the proposal set), the token (G7, round 28). -/
theorem swift.rowTokO_tokP (c : swift.DC) (b : Nat) (x : swift.CommandId) (d : Loc)
    (γd : ChanNames) (MP : GoInterface → IProp netDistGF) (dv : swift.DescV) (rv : swift.RowV) :
    swift.descF d γd MP dv ∗ swift.proposeHalf d true ∗ swift.rowTokO c b x dv rv ⊢
      swift.descF d γd MP dv ∗ swift.proposeHalf d true ∗
        (swift.rowTok c.γo b (toCmdId x) rv ∗ swift.slotT c (b, toCmdId x)) ∗
        ⌜dv.propose ≠ null⌝ := by
  iintro ⟨Hd, HPc, Htok⟩
  iunfold swift.descF at Hd
  icases Hd with ⟨Hph, Hcmd, #Hvs, Hdep, #HD, Hhs, #HHs, Hprop, Hseq, Hmsgs, #Hmb, #HsL, %Hop⟩
  iunfold swift.proposeHalf at HPc
  icases HPc with ⟨%p, Hp, %Hpv⟩
  icombine Hprop Hp gives %Heq
  have hp : dv.propose ≠ null := by rw [Heq]; simpa using Hpv
  ihave Htok := swift.rowTokO_tok c b x dv rv hp $$ Htok
  iframe Htok
  isplitl [Hph Hcmd Hdep Hhs Hprop Hseq Hmsgs]
  · iunfold swift.descF; iframe Hph Hcmd Hdep Hhs Hprop Hseq Hmsgs Hvs HD HHs Hmb HsL
    ipureintro; exact Hop
  isplitl [Hp]
  · iunfold swift.proposeHalf; iexists p; iframe Hp; ipureintro; exact Hpv
  ipureintro; exact hp

/-- **The owner's ticket for `deliver`** (round 46, D-SWC2-6): `rowTokO`'s ticket (or `x`'s
execution) when the proposal is set, nothing before; and back from what `deliver` returns. -/
theorem swift.rowTokO_tix (c : swift.DC) (b : Nat) (x : swift.CommandId) (dv : swift.DescV)
    (rv : swift.RowV) :
    swift.rowTokO c b x dv rv ⊢
      swift.tixD c.γxu c.γxm b x dv ∗ (swift.tixD c.γxu c.γxm b x dv -∗ swift.rowTokO c b x dv rv) := by
  iintro H
  by_cases hp : dv.propose = null
  · isplitr
    · iunfold swift.tixD; ileft; ipureintro; exact hp
    iintro -; iexact H
  iunfold swift.rowTokO at H
  icases H with (⟨Ht, Hsx⟩ | ⟨%Hn, -⟩)
  · iunfold swift.slotT at Hsx
    icases Hsx with ⟨Hs, Hx⟩
    ihave Hx := swift.tixOr_to c.γxu c.γxm b x $$ Hx
    isplitl [Hx]
    · iunfold swift.tixD; iright; iexact Hx
    iintro Hx
    iunfold swift.tixD at Hx
    icases Hx with (%Hn | Hx)
    · exact absurd Hn hp
    ihave Hx := swift.tixOr_of c.γxu c.γxm b x $$ Hx
    iunfold swift.rowTokO; ileft; iframe Ht; iunfold swift.slotT; iframe Hs Hx
  · exact absurd Hn.2 hp

/-- **A claim and the token of its key exclude each other** (round 34, table rev 6): the claimed
key's token is in the store (`storeOk`'s claims clause). -/
theorem swift.claim_tok_false (c : swift.DC) (K : Nat × sp.CmdId) (ck : swift.ClK)
    (rv : swift.RowV) :
    c.ctx ∗ swift.claimTok c.γcl K ck ∗ swift.rowTok c.γo K.1 K.2 rv ⊢ |={⊤}=> False := by
  iintro ⟨#Hctx, Hcl, Htok⟩
  iunfold swift.DC.ctx at Hctx
  iunfold swift.descCtxE at Hctx
  icases Hctx with ⟨%me, %fr, %lg, %dm, %dc, %ex, %dr, %oe, %γa, %γrm, %rc, %γrc, -, -, %Hids, -, -,
    -, -, -, #Hninv, -⟩
  iinv Hninv with Hi Hclose
  iunfold swift.nodeInvD at Hi
  imod Hi
  icases Hi with ⟨%st, %O, Hst, Hw2, He, HO, HS, HX, %Hacc, %Hok⟩
  iunfold swift.storeD at HS
  icases HS with ⟨%Rt, %Out, %Cl, %U, Ha, Hc, Hm, Hu, %h, %hU⟩
  iunfold swift.claimTok at Hcl
  ihave %Hl := ghost_map_lookup $$ Hc Hcl
  have hR : PartialMap.get? Rt K = some (swift.recOf ck) := h.2.2.2.2 K ck Hl
  icases (BigSepM.bigSepM_delete hR).1 $$ Hm with ⟨⟨%rv', Ht', -⟩, -⟩
  iunfold swift.rowTok at Htok Ht'
  ihave %Hne := ghostMapElem_ne c.γo (K.1, K.2) (K.1, K.2) (DFrac.own 1) rv rv' $$ Htok Ht'
  exact absurd rfl Hne

/-- A `fresh` claim's record: the empty row (round 34). -/
theorem swift.retWhy_fresh (γ : sp.Names) (γxm γcg : GName) (str : swift.CommandId → GoString)
    (N r : Nat) (K : Nat × sp.CmdId) (rv : swift.RowV) :
    swift.retWhy γ γxm γcg str N r K rv (swift.recOf .fresh) ⊢ ⌜rv = swift.rowEmpty⌝ := by
  simp only [swift.recOf, swift.retWhy]; exact .rfl

/-- A `sync` claim's record: the sync row and the sync order's membership (round 34). -/
theorem swift.retWhy_sync (γ : sp.Names) (γxm γcg : GName) (str : swift.CommandId → GoString)
    (N r : Nat) (K : Nat × sp.CmdId) (rv : swift.RowV) :
    swift.retWhy γ γxm γcg str N r K rv (swift.recOf .sync) ⊢
      ⌜rv = swift.rvSync⌝ ∗ swift.syncIn γ K.1 K.2 := by
  simp only [swift.recOf, swift.retWhy]; exact .rfl

end shLemmas

section capLemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions] [hook.Assumptions]

/-- **`rowPhaseOk` after the handler's `COMMIT`** (:736): every clause holds at phase 3. -/
theorem swift.rowPhaseOk_commit (N r b : Nat) (dv : swift.DescV) (rv rv' : swift.RowV)
    (h : swift.rowPhaseOk N r b dv rv) :
    swift.rowPhaseOk N r b { dv with phase := swift.phCOMMIT } rv' := by
  unfold swift.rowPhaseOk at *
  simp only [swift.phCOMMIT]
  refine ⟨fun hp => ⟨Or.inr trivial, (h.1 hp).2⟩, fun _ => ⟨by decide, fun h0 => absurd h0 (by decide),
    fun h0 => absurd h0 (by decide), fun h0 => absurd h0 (by decide), fun _ => by decide,
    fun _ => Or.inl (by decide)⟩⟩

/-- `depWhy` across a write of the phase (`dep` and `propose` unchanged): its `START` escape is
at a follower (`rowPhaseOk`'s E7 clause). Round 53 (52-1): at a follower with a proposal, from a
phase at most `PRE_ACCEPT` only to such a phase (`hph`; the follower's later phases come with
the leader's `dep`, `swift.depWhy_adopt`). -/
theorem swift.depWhy_phase (γ : sp.Names) (γxm : GName) (N r b : Nat) (x : swift.CommandId) (dv : swift.DescV)
    (rv : swift.RowV) (ph : w64) (h : swift.rowPhaseOk N r b dv rv)
    (hph : r ≠ sp.leaderOf N b → dv.propose ≠ null → uint.nat dv.phase ≤ 1 → uint.nat ph ≤ 1) :
    (⌜r = sp.leaderOf N b ∧ dv.phase = W64 3⌝ -∗ swift.syncIn γ b (toCmdId x) -∗
        |={⊤}=> ⌜ph = W64 3⌝) ∗
      swift.depWhy γ γxm N r b x dv ⊢ |={⊤}=> swift.depWhy γ γxm N r b x { dv with phase := ph } := by
  iintro ⟨Hs3, H⟩
  iunfold swift.depWhy at H
  iunfold swift.depWhy
  icases H with ((%Hp | ⟨%Hxl, #Hx⟩) | ⟨%Hg, #H⟩ | ⟨%Hs, #H⟩ | ⟨%Hl, #H⟩)
  · imodintro; ileft; ileft; ipureintro
    by_cases hpn : dv.propose = null
    · exact Or.inr (Or.inl hpn)
    rcases Hp with Hp | Hp | Hp
    · exact Or.inl ⟨Hp.1, hph Hp.1 hpn Hp.2⟩
    · exact absurd Hp hpn
    · have hl : r ≠ sp.leaderOf N b := ((h.2 hpn).2.1 Hp).2
      exact Or.inl ⟨hl, hph hl hpn (by rw [Hp]; decide)⟩
  · imodintro; ileft; iright; isplitr
    · ipureintro; exact Hxl
    iexact Hx
  · imodintro
    by_cases hpn : dv.propose = null
    · ileft; ileft; ipureintro; exact Or.inr (Or.inl hpn)
    iright; ileft
    isplitr
    · ipureintro
      by_cases hl : r = sp.leaderOf N b
      · exact Or.inl hl
      · rcases Hg with Hg | Hg
        · exact Or.inl Hg
        · exact Or.inr (hph hl hpn Hg)
    iexact H
  · -- round 56 (D79 (2)): the sync disjunct needs the new phase at `COMMIT` (`Hs3`)
    ihave Hh := Hs3 $$ [] H
    · ipureintro; exact Hs
    imod Hh with %h3
    imodintro
    iright; iright; ileft; isplitr
    · ipureintro; exact ⟨Hs.1, h3⟩
    iexact H
  · imodintro; iright; iright; iright; isplitr
    · ipureintro; exact Hl
    iexact H

/-- `phaseWhy` at a phase other than `PRE_ACCEPT`. -/
theorem swift.phaseWhy_ne1 (γ : sp.Names) (N r b : Nat) (x : swift.CommandId) (dv : swift.DescV)
    (h : dv.phase ≠ W64 1) : ⊢ swift.phaseWhy γ N r b x dv := by
  iunfold swift.phaseWhy; ileft; ipureintro; exact h

/-- **The handler's `slotOk` from its capability** (G-cap): a goroutine's (`dv.seq = false`), or
the slot case over `deliver`'s frame (the handler's set data `Ro`, as `ownAny`). The post records
that the descriptor is sequential. -/
theorem swift.slotCapR_slotOk (c : swift.DC) (MP : GoInterface → IProp netDistGF) (γd : ChanNames)
    (d : Loc) (x : swift.CommandId) (b : Nat) (ms : Loc) (Rs Ro : IProp netDistGF) (dv : swift.DescV)
    (rv : swift.RowV) (q : Qp) (hseq : dv.seq = c.sq) (hRo : Ro ⊢ swift.msetF ms) :
    swift.slotCapR c MP γd d x b ms Rs ⊢
      ⌜dv.seq = false⌝ ∨ swift.slotOk MP γd c.γxm c.rp d b x dv
        iprop(Rs ∗ Ro ∗ swift.rowTokO c b x dv rv ∗
          ghostMapElem c.γsh d (DFrac.own (1 : Qp).half) q ∗ c.env d q)
        iprop(⌜c.sq = true⌝ ∗ c.ret d x ∗ c.env d q) := by
  iintro Hc
  iunfold swift.slotCapR at Hc
  icases Hc with (%h | #Hc)
  · ileft; ipureintro; rw [hseq]; exact h
  iright
  iunfold swift.slotOk
  iintro %s
  imodintro
  iintro %Φ ⟨Hm, Hd, %Hs, #Hex, HRs, HRo, Htok, Hsh, Henv⟩ HΦ
  ihave HRo := hRo $$ HRo
  iapply Hc $$ [Hm Hd Htok Hsh Henv HRo HRs]
  · iframe Hm Hd Htok Hsh Henv HRo HRs Hex
    ipureintro; exact Hs
  inext
  iintro ⟨Hret, Henv⟩
  iapply HΦ
  iframe Hret Henv
  ipureintro; rw [← hseq]; exact Hs.1

/-- `slotCapR_slotOk` with the row token lent out for its ticket (round 46, D-SWC2-6): the frame
holds `rowTokO` back from the ticket (`rowTokO_tix`), which `x`'s execution gives. -/
theorem swift.slotCapR_slotOkT (c : swift.DC) (MP : GoInterface → IProp netDistGF) (γd : ChanNames)
    (d : Loc) (x : swift.CommandId) (b : Nat) (ms : Loc) (Rs Ro : IProp netDistGF) (dv : swift.DescV)
    (rv : swift.RowV) (q : Qp) (hseq : dv.seq = c.sq) (hRo : Ro ⊢ swift.msetF ms) :
    swift.slotCapR c MP γd d x b ms Rs ⊢
      ⌜dv.seq = false⌝ ∨ swift.slotOk MP γd c.γxm c.rp d b x dv
        iprop(Rs ∗ Ro ∗ (swift.tixD c.γxu c.γxm b x dv -∗ swift.rowTokO c b x dv rv) ∗
          ghostMapElem c.γsh d (DFrac.own (1 : Qp).half) q ∗ c.env d q)
        iprop(⌜c.sq = true⌝ ∗ c.ret d x ∗ c.env d q) := by
  iintro Hc
  iunfold swift.slotCapR at Hc
  icases Hc with (%h | #Hc)
  · ileft; ipureintro; rw [hseq]; exact h
  iright
  iunfold swift.slotOk
  iintro %s
  imodintro
  iintro %Φ ⟨Hm, Hd, %Hs, #Hex, HRs, HRo, Htokw, Hsh, Henv⟩ HΦ
  ihave HRo := hRo $$ HRo
  ihave Htok := Htokw $$ [Hex]
  · iunfold swift.tixD; iright; iright; iexact Hex
  iapply Hc $$ [Hm Hd Htok Hsh Henv HRo HRs]
  · iframe Hm Hd Htok Hsh Henv HRo HRs Hex
    ipureintro; exact Hs
  inext
  iintro ⟨Hret, Henv⟩
  iapply HΦ
  iframe Hret Henv
  ipureintro; rw [← hseq]; exact Hs.1

/-- `repPre` reads only `propose`, `c`, `Hs` and `D` (round 47). -/
theorem swift.repPre_congr (γ : sp.Names) (N r b : Nat) (x : swift.CommandId) (dv dv' : swift.DescV)
    (h1 : dv'.propose = dv.propose) (h2 : dv'.c = dv.c) (h3 : dv'.Hs = dv.Hs) (h4 : dv'.D = dv.D) :
    swift.repPre γ N r b x dv ⊢ swift.repPre γ N r b x dv' := by
  unfold swift.repPre swift.replyPre swift.ldrPrefix; rw [h1, h2, h3, h4]

/-- `repPre` before the proposal (round 47). -/
theorem swift.repPre_null (γ : sp.Names) (N r b : Nat) (x : swift.CommandId) (dv : swift.DescV)
    (h : dv.propose = null) : ⊢ swift.repPre γ N r b x dv := by
  iunfold swift.repPre; ileft; ipureintro; exact h

/-- A set's data at handler resource `True` is `msetF` (round 42, D48 (3)). -/
theorem swift.msetF_of (ms : Loc) (q : GoInterface) (sz : Nat) (mem : w32 → Prop)
    (P : w32 → GoInterface → IProp netDistGF) (A : GoInterface → GoInterface → IProp netDistGF)
    (PL : GoInterface → IProp netDistGF) (hd : GoFunc) :
    replica.mset.ownD ms q sz mem P A PL iprop(True) hd ⊢ swift.msetF ms := by
  iintro H
  iunfold swift.msetF
  iexists q, sz, mem, P, A, PL, hd
  iexact H

/-- `msetF` forgets to `ownAny` (round 42, D48 (3)). -/
theorem swift.msetF_ownAny (ms : Loc) : swift.msetF ms ⊢ replica.mset.ownAny ms := by
  iintro H
  iunfold swift.msetF at H
  icases H with ⟨%q, %sz, %mem, %P, %A, %PL, %hd, H⟩
  iapply replica.mset.ownD_ownAny $$ H

/-- **The handler-level capability from `descOwn`'s** (G-cap; table rev 5 C3): any frame `Rs`
that, with the set the handler is lent, gives back the sets' fields, both sets' data, an
`OptCondF` part and the owner frame `F`. -/
theorem swift.slotCap_R (c : swift.DC) (MP : GoInterface → IProp netDistGF) (γd : ChanNames)
    (d : Loc) (x : swift.CommandId) (b : Nat) (F : IProp netDistGF) (ms : Loc) (Rs : IProp netDistGF)
    (h : Rs ∗ swift.msetF ms ⊢ ∃ (sl fa cf : Loc) (cond : GoFunc) (fs : List GoFunc) (v : Bool),
      swift.dfld d go!"slowPathH" ↦ sl ∗ swift.dfld d go!"fastPathH" ↦ fa ∗
      swift.msetF sl ∗ swift.msetF fa ∗ swift.ocfRes d cf cond fs v ∗ F) :
    swift.slotCap c MP γd d x b F ⊢ swift.slotCapR c MP γd d x b ms Rs := by
  iintro Hc
  iunfold swift.slotCap at Hc
  iunfold swift.slotCapR
  icases Hc with (%h0 | #Hc)
  · ileft; ipureintro; exact h0
  iright
  imodintro
  iintro %s %dv %rv %q
  imodintro
  iintro %Φ ⟨Hm, Hd, %Hs, #Hex, Hsh, Htok, Hms, HRs, Henv⟩ HΦ
  ihave ⟨%sl, %fa, %cf, %cond, %fs, %v, Hsl, Hfa, Hosl, Hofa, Hocf, HF⟩ := h $$ [HRs Hms]
  · iframe HRs Hms
  iapply Hc $$ [Hm Hd Hsh Htok Hsl Hfa Hosl Hofa Hocf HF Henv]
  · iframe Hm Hd Hsh Htok Hsl Hfa Hosl Hofa Hocf HF Henv Hex
    ipureintro; exact Hs
  iexact HΦ

end capLemmas

end Perennial.github_com.imdea_software.swiftpaxos
