/-
The protocol invariant `Inv : Sys → Prop` (`notes/stage1-plan.md`, "Proof architecture", A), its
conjuncts, and the consequence laws the Iris layer uses (`inv_init`, `inv_step_*`,
`step_crt_mono`, `inv_exec_first`, `inv_exec_again`, `fire_kv_step`, `kv_step_det`; stage 2:
the execution laws per key the slot's command touches, a SCAN's range included).

The invariant speaks of the system's state and of the ghost history `S.hist` (votes, proposals,
commits, attribute computations with their conflicts-map records, own prepare reports, sends,
each with its replica, in order). It is organized as named conjuncts, each with a docstring:

* (wf) well-formedness the code's indexing relies on (no panic: `wf`, `msgWf`, `replyTargets`,
  `noTPA`, fix B11);
* (a) ballots, votes, replies and the leader's bookkeeping (`lbInv`, `prepReplyHighest`, fix B12);
* (b) agreement: one decided value per instance, Paxos with a fast path at the leader's initial
  ballot, recovery = SOSP'13 Sec. 4.4 with fast quorum 2F (decisions.md D2) and "the leader replied
  => it no longer acts at its ballot" (fix R-LEAD);
* (c) dependencies (fixes E3, R-PREP, B3, B13);
* (d) execution (fixes E2, B2, B8);
* (e) client ops.

This is a draft of the riskiest statement of the project: the prover is expected to strengthen it
(auxiliary conjuncts) and may find conjuncts false of the code; see the report (`notes/`) for the
places most likely to need it.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.InvDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.Laws

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

/-! ## Laws -/

theorem inv_init : Inv Sys.init := inv_init'

theorem inv_step_clientPropose (S : Sys) (i : Nat) (p : Proposal) (hS : Inv S) (hi : i < nR)
    (hp : p.cid ∉ S.ops.map (·.2.cid)) :
    Inv { S with ops := S.ops ++ [(i, p)],
                 proposeChan := upd S.proposeChan i (S.proposeChan i ++ [p]) } :=
  inv_step_clientPropose' S i p hS hp

theorem inv_step_propose (S : Sys) (i : Nat) (batch : List Proposal) (hS : Inv S) (hi : i < nR)
    (hidle : S.idle i) (hb : batch ≠ []) (hsub : batch.Subperm (S.proposeChan i))
    (hfull : rowFull (S.rep i) = true → batch.length = 1) :
    Inv (S.propose i batch) :=
  -- a full row drops the proposal (R-CAP); else a fresh instance starts (`Proof/HPropose.lean`)
  ProposeProof.inv_step_propose' S i batch hS hi hidle hb hsub

theorem inv_step_deliver (S : Sys) (fr i n : Nat) (m : Msg) (hS : Inv S)
    (hi : i < nR) (hfr : fr < nR) (hidle : S.idle i) (hm : (S.sent fr i)[n]? = some m)
    (hn : (fr, i, n) ∉ S.delivered) :
    Inv (S.deliver fr i n m) :=
  -- split by message kind (`Proof/Deliver.lean`): the no-op deliveries are proved, each
  -- protocol handler has its own (open) law; the PrepareReply case is no longer false of the
  -- model (G1's fix R-PROM is mirrored) and its riskiest part, the decision's safety, is proved
  -- (`DecideProof.decide_safe`)
  inv_step_deliver' S fr i n m hS hi hfr hidle hm hn

theorem inv_step_recover (S : Sys) (i : Nat) (x : InstId) (hS : Inv S) (hi : i < nR)
    (hidle : S.idle i) (hq : x.q < nR) (hx : (x.i : Int) ≤ zz ((S.rep i).crtInstance x.q)) :
    Inv (S.applyStep i (hRecover (S.rep i) x)) :=
  RecoverProof.inv_step_recover' S i x hS hi hidle hq hx

theorem inv_step_bcast (S : Sys) (i : Nat) (b : Bcast) (a : Bool) (hS : Inv S) (hi : i < nR)
    (hb : S.pending i = some b) (hp : b.peers ≠ []) :
    Inv (S.bcastStep i b a) :=
  inv_step_bcast' S i b a hS hb hp

theorem inv_step_beTheLeader (S : Sys) (i : Nat) (hS : Inv S) (hi : i < nR) :
    Inv { S with rep := upd S.rep i (hBeTheLeader (S.rep i)) } :=
  inv_step_beTheLeader' S i hS

theorem inv_step_peerOrder (S : Sys) (i : Nat) (o : List Nat) (hS : Inv S) (hi : i < nR)
    (ho : Sys.peerOrderOk i o) :
    Inv { S with rep := upd S.rep i { S.rep i with peerOrder := o } } :=
  inv_step_peerOrder' S i o hS ho

theorem inv_step_flush (S : Sys) (i to : Nat) (m : Msg) (rest : List Msg) (hS : Inv S)
    (h : S.outbox i to = m :: rest) :
    Inv { S with sent := upd S.sent i (upd (S.sent i) to (S.sent i to ++ [m])),
                 outbox := upd S.outbox i (upd (S.outbox i) to rest) } :=
  inv_step_flush' S i to m rest hS h

theorem inv_step_lose (S : Sys) (i to : Nat) (m : Msg) (rest : List Msg) (hS : Inv S)
    (h : S.outbox i to = m :: rest) :
    Inv { S with outbox := upd S.outbox i (upd (S.outbox i) to rest) } :=
  inv_step_lose' S i to m rest hS h

theorem inv_step_execSCC (S : Sys) (i : Nat) (C : List InstId) (hS : Inv S) (hi : i < nR)
    (hidle : S.idle i) (hC : sccReady (S.rep i) C) : Inv (S.startSCC i C) :=
  inv_step_execSCC' S i C hS hi hidle hC

theorem inv_step_execCmd (S : Sys) (i : Nat) (x : InstId) (rest : List InstId) (w : InstRec)
    (hS : Inv S) (hi : i < nR) (hcur : S.execCur i = x :: rest) (hw : (S.rep i).inst x = some w)
    (hidx : S.execIdx i < (w.cmds.getD []).length) : Inv (S.execCmd i x w) :=
  ExecOrd.inv_step_execCmd'' hS hi hcur hw hidx

theorem inv_step_instDone (S : Sys) (i : Nat) (x : InstId) (rest : List InstId) (w : InstRec)
    (hS : Inv S) (hi : i < nR) (hcur : S.execCur i = x :: rest) (hw : (S.rep i).inst x = some w)
    (hidx : S.execIdx i = (w.cmds.getD []).length) : Inv (S.instDone i x rest) :=
  ExecOrd.inv_step_instDone'' hS hi hcur hw hidx

theorem inv_step_execBump (S : Sys) (i q : Nat) (hS : Inv S) (hi : i < nR) (hq : q < nR)
    (he : (S.rep i).executed ⟨q, toN ((S.rep i).execedUpTo q + 1)⟩) :
    Inv { S with rep := upd S.rep i (execBump (S.rep i) q) } :=
  inv_step_execBump' S i q hS hq he

/-- Preservation by any step. -/
theorem inv_step (S S' : Sys) (hS : Inv S) (h : Step S S') : Inv S' := by
  cases h with
  | clientPropose i p hi hp => exact inv_step_clientPropose S i p hS hi hp
  | propose i batch hi hid hb hsub hfull => exact inv_step_propose S i batch hS hi hid hb hsub hfull
  | deliver fr i n m hi hfr hid hm hn => exact inv_step_deliver S fr i n m hS hi hfr hid hm hn
  | recover i x hi hid hq hx => exact inv_step_recover S i x hS hi hid hq hx
  | bcastStep i b a hi hb hp => exact inv_step_bcast S i b a hS hi hb hp
  | beTheLeader i hi => exact inv_step_beTheLeader S i hS hi
  | peerOrder i o hi ho => exact inv_step_peerOrder S i o hS hi ho
  | flush i to m rest h => exact inv_step_flush S i to m rest hS h
  | lose i to m rest h => exact inv_step_lose S i to m rest hS h
  | execSCC i C hi hid hC => exact inv_step_execSCC S i C hS hi hid hC
  | execCmd i x rest w hi hc hw hidx => exact inv_step_execCmd S i x rest w hS hi hc hw hidx
  | instDone i x rest w hi hc hw hidx => exact inv_step_instDone S i x rest w hS hi hc hw hidx
  | execBump i q hi hq he => exact inv_step_execBump S i q hS hi hq he

/-- `crtInstance` only grows (what makes a recovery request, an in-range instance at most the
executor's snapshot of `crtInstance`, still in range when the run loop takes it). -/
theorem step_crt_mono (S S' : Sys) (hS : Inv S) (h : Step S S') (i q : Nat) :
    zz ((S.rep i).crtInstance q) ≤ zz ((S'.rep i).crtInstance q) :=
  step_crt_mono' S S' hS.1 h i q

/-- The command of the executor's current slot at replica `i` (the head `x` of `execCur i`, record
`w`). -/
def curCmd (S : Sys) (i : Nat) (w : InstRec) : WCmd := (w.cmds.getD []).getD (S.execIdx i) default

/-- The replica that executes a slot not yet executed anywhere computes exactly the abstract
state's output: for every key the slot's command touches, its executed writes of the key are the
global ones, so its store's values for those keys are the abstract ones, and the output it
computes (`execCmd`) is `outOf` the global sequences, the one `fire` records. -/
theorem inv_exec_first (S : Sys) (i : Nat) (x : InstId) (rest : List InstId) (w : InstRec)
    (hS : Inv S) (hi : i < nR) (hcur : S.execCur i = x :: rest) (hw : (S.rep i).inst x = some w)
    (hidx : S.execIdx i < (w.cmds.getD []).length) (hc : (curCmd S i w).op ≠ opNONE)
    (hnew : ((x, S.execIdx i), curCmd S i w) ∉ S.gexec (curCmd S i w).key) :
    ∀ k, Sys.touches (curCmd S i w) k → Sys.writes (S.gexec k) = Sys.writes (S.lexec i k) :=
  ExecOrd.exec_first hS.1 hS.2.exec hi hcur hw rfl rfl hidx hc hnew

/-- A later execution of a slot computes the recorded output: for every key the command touches,
the replica's executed writes of the key are the global writes before the slot, and the slot's
op fired with the output against the global sequences before it. -/
theorem inv_exec_again (S : Sys) (i : Nat) (x : InstId) (rest : List InstId) (w : InstRec)
    (hS : Inv S) (hi : i < nR) (hcur : S.execCur i = x :: rest) (hw : (S.rep i).inst x = some w)
    (hidx : S.execIdx i < (w.cmds.getD []).length) (hc : (curCmd S i w).op ≠ opNONE)
    (hold : ((x, S.execIdx i), curCmd S i w) ∈ S.gexec (curCmd S i w).key) :
    (∀ k, Sys.touches (curCmd S i w) k →
      ∃ pre post, S.gexec k = pre ++ ((x, S.execIdx i), curCmd S i w) :: post ∧
        Sys.writes pre = Sys.writes (S.lexec i k)) ∧
      ∀ p, S.slotOp (x, S.execIdx i) = some p →
        S.fired p.cid = some (Sys.outOf (fun k => Sys.before (S.gexec k) ((x, S.execIdx i),
          curCmd S i w)) (curCmd S i w)) :=
  ExecOrd.exec_again hS.1 hS.2.exec hi hcur hw rfl rfl hidx hc hold

/-- The abstract state's step at a first execution: firing a slot whose op's input is `inp`
(`cmdOf inp` its command, its range the model's) is the key-value model's step from `S.kv` with
the recorded output. -/
theorem fire_kv_step (S : Sys) (e : Slot × WCmd) (inp : KvsInput (List w8))
    (hcmd : e.2 = cmdOf inp) (hval : inpRangeOk inp)
    (hnew : e ∉ S.gexec e.2.key) :
    (kvScan w8).step S.kv inp (S.fire e).kv (Sys.outOf S.gexec e.2) :=
  fire_kv_step' S e inp hcmd hval hnew

/-- The prefix `before` names (review T2-1): in a global sequence (whose slots are distinct), the
part before an entry is the `pre` of any split at it. -/
theorem before_eq (S : Sys) (hS : Inv S) (k : w64) (pre post : List (Slot × WCmd))
    (e : Slot × WCmd) (h : S.gexec k = pre ++ e :: post) : Sys.before (S.gexec k) e = pre :=
  ExecOrd.before_split hS.1 k pre post e h

/-- Sequences with the same writes have the same last PUT (review T2-1). -/
theorem lastPut_eq_of_writes (a b : List (Slot × WCmd)) (h : Sys.writes a = Sys.writes b) :
    Sys.lastPut a = Sys.lastPut b := by
  rw [ExecOrd.lastPut_writes a, ExecOrd.lastPut_writes b, h]

/-- A SCAN touches the keys of its range (review T2-1). -/
theorem rangeKeys_touches (c : WCmd) (k : w64) (hc : c.op = opSCAN) (hk : k ∈ rangeKeys c) :
    Sys.touches c k := Or.inr ⟨hc, hk⟩

/-- The key-value model's step is deterministic (B14: with `fire_kv_step`, the state and output
`escrow_fire`'s step chose are the model's `fire` ones). -/
theorem kv_step_det (σ : w64 → Option (List w8)) (inp : KvsInput (List w8))
    (σ1 σ2 : w64 → Option (List w8)) (o1 o2 : KvsOutput (List w8))
    (h1 : (kvScan w8).step σ inp σ1 o1) (h2 : (kvScan w8).step σ inp σ2 o2) :
    σ1 = σ2 ∧ o1 = o2 := by
  cases inp <;> simp_all [kvScan]

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
