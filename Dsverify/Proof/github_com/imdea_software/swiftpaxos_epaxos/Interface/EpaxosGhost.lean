/-
The epaxos package's ghost interface (over the global ghost state): the protocol's ghost `Sys`
(`sysAuth`, `repFrag`), the re-proposal tokens (`inChan`), `crtInstance`'s lower bounds
(`crtLb`, what a recovery request carries), the outboxes (`outboxFrag`), the pending broadcast
(`pendFrag`), the executor's progress in a component (`curFrag`), the global protocol invariant
`epInv γ` and its laws, and what a replica id gets at registration (`epRepStart`, part of
`Registry.lean`'s `repStart`).

(A file of its own, importing only the client side and the model, so that the registration
exchange can carry `epRepStart`; the heap side — `ownRep`, the instance lock, `epaxos.New`'s spec — is
`Epaxos/Interface/Epaxos.lean`.)

**The wire layer's notions used** (`Epaxos/Interface/Net.lean`): `sentHalf γ f t ms` (the
protocol layer's half of the list of messages `f` sent to `t` is in `epInv`, equal to the model's
`S.sent f t`; the framework's half is under `r.M`), `msgSent γ f t n m` (persistent: message `n`
from `f` to `t`), `sendUpd γ f t m Ψ` (what `SendMsg` runs: `ep_sendUpd` is the protocol
layer's), `delivTok γ t f n` (the one-shot delivery token, kept by `epInv` once used); and
the client connection's acceptor token `connFresh cid true` (the framework's `opTok γ cid`,
`Epaxos/Interface/Replica.lean`, which this file cannot import: `Replica.lean` is above
`Registry.lean`), kept by `epInv` for each op that entered the model.

**This layer's ghost state** (bodies chosen by the epaxos prover, `Epaxos/Proof/epaxos/GhostDefs.lean`:
per replica, a fractional mono-list of its states over an injective encoding of `RState` into
functions `Pos → Pos`, ghost variables for the outboxes, the pending broadcast and the executor's
progress, a ghost map of re-proposal tokens): `sysAuth`, `repFrag`, `inChan`, `crtLb`,
`outboxFrag`, `pendFrag`, `curFrag`, with their laws.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.Client
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Inv
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.GhostExec

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The namespace of the protocol invariant `epInv`. -/
def protoN : Namespace := ndot epN "proto"

theorem protoN_escrowN_disj : (↑protoN : CoPset) ## ↑escrowN := by
  unfold protoN escrowN; exact ndot_ne_disjoint _ (by decide)

theorem protoN_epEop : (↑protoN : CoPset) ⊆ epEop := by
  unfold protoN epEop; exact nclose_subseteq _ _

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-! ## The protocol's ghost state (this layer's; bodies in `GhostDefs.lean`) -/

/-- The authority of the ghost system `S` (held by `epInv`). -/
def sysAuth (γ : EpNames) (S : Sys) : IProp GF := sysAuthB γ S

/-- Replica `i`'s fragment: its protocol state is `σ` (exclusive; held by replica `i`'s instance
lock invariant). -/
def repFrag (γ : EpNames) (i : Nat) (σ : RState) : IProp GF := repFragB γ i σ

/-- Replica `i`'s `crtInstance[q]` is at least `n` (persistent; `crtInstance` only grows,
`step_crt_mono`): what the executor's recovery request for `(q, k)`, `k ≤ n`, carries through
`instancesToRecover` to the run loop (`ep_recover`). -/
def crtLb (γ : EpNames) (i q : Nat) (n : w32) : IProp GF := crtLbB γ i q n

instance crtLb_persistent (γ : EpNames) (i q : Nat) (n : w32) : Persistent (crtLb (GF := GF) γ i q n) := by
  unfold crtLb; infer_instance

/-- The re-proposal token of `p` at replica `i` (exclusive): `handleCommit`'s re-proposal of a
proposal whose slot was decided a no-op (`Out.repropose`) puts `p` back on `ProposeChan` with this
token in place of the op token the framework's `proposal` carries (the op token was used when
`p` first entered the model): the framework's `ProposeChan` predicate (`proposal`,
`Epaxos/Interface/Replica.lean`) carries `opTok γ cid ∨ inChan γ id ⟨cid, cmdOf inp⟩`. Consumed by
`handlePropose` (`ep_propose`). -/
def inChan (γ : EpNames) (i : Nat) (p : Proposal) : IProp GF := inChanB γ i p

/-- Replica `i`'s outbox to `to` is `ms` (exclusive): the messages its current handler decided to
send and has not yet handed to `SendMsg` (empty whenever the instance lock is free). -/
def outboxFrag (γ : EpNames) (i to : Nat) (ms : List Msg) : IProp GF :=
  outboxFragB γ i to ms

/-- Replica `i`'s pending broadcast is `ob` (exclusive; `none` whenever the instance lock is
free). -/
def pendFrag (γ : EpNames) (i : Nat) (ob : Option Bcast) : IProp GF := pendFragB γ i ob

/-- Replica `i`'s executor is executing the component whose rest is `cur`, at command `idx` of its
head (exclusive; `[]`, `0` whenever the instance lock is free). -/
def curFrag (γ : EpNames) (i : Nat) (cur : List InstId) (idx : Nat) : IProp GF :=
  curFragB γ i cur idx

theorem repFrag_agree (γ : EpNames) (S : Sys) (i : Nat) (σ : RState) :
    sysAuth (GF := GF) γ S -∗ repFrag γ i σ -∗ ⌜S.rep i = σ⌝ := by
  unfold sysAuth repFrag
  iintro Ha Hf
  ihave %hi := repFragB_lt γ i σ $$ Hf
  iapply sysAuthB_rep γ S i σ hi $$ Ha Hf

theorem repFrag_excl (γ : EpNames) (i : Nat) (σ σ' : RState) :
    repFrag (GF := GF) γ i σ -∗ repFrag γ i σ' -∗ False := repFragB_excl γ i σ σ'

/-- A step of replica `i`: the authority and `i`'s fragment move together; the other replicas'
states do not change; `crtInstance` does not decrease (`step_crt_mono`, what keeps `crtLb`
sound); the fields the other fragments track do not change (the outboxes, the pending
broadcasts, the executors' progress) and the channels only grow (HUB-REQUEST epaxos-1). -/
theorem sys_update (γ : EpNames) (S S' : Sys) (i : Nat) (σ : RState)
    (h : ∀ j, j ≠ i → S'.rep j = S.rep j)
    (hcrt : ∀ q, zz ((S.rep i).crtInstance q) ≤ zz ((S'.rep i).crtInstance q))
    (hrest : S'.outbox = S.outbox ∧ S'.pending = S.pending ∧ S'.execCur = S.execCur ∧
      S'.execIdx = S.execIdx ∧ ∀ j, (S.proposeChan j).Subperm (S'.proposeChan j)) :
    sysAuth (GF := GF) γ S -∗ repFrag γ i σ ==∗ sysAuth γ S' ∗ repFrag γ i (S'.rep i) := sys_updateB γ S S' i σ h hcrt hrest

/-- A step that changes no replica's state (a client proposal reaching a channel), nor the
fields the fragments track (the channels only grow; HUB-REQUEST epaxos-1). -/
theorem sys_update_norep (γ : EpNames) (S S' : Sys) (h : S'.rep = S.rep)
    (hrest : S'.outbox = S.outbox ∧ S'.pending = S.pending ∧ S'.execCur = S.execCur ∧
      S'.execIdx = S.execIdx ∧ ∀ j, (S.proposeChan j).Subperm (S'.proposeChan j)) :
    sysAuth (GF := GF) γ S ==∗ sysAuth γ S' := by
  unfold sysAuth
  iintro Ha
  imodintro
  iapply sysAuthB_chan_mono γ S S' h hrest.1 hrest.2.1 hrest.2.2.1 hrest.2.2.2.1 hrest.2.2.2.2 $$ Ha

/-- A lower bound of `crtInstance[q]`, read off replica `i`'s fragment. -/
theorem crtLb_get (γ : EpNames) (i q : Nat) (σ : RState) :
    repFrag (GF := GF) γ i σ -∗ repFrag γ i σ ∗ crtLb γ i q (σ.crtInstance q) := crtLb_getB γ i q σ

theorem crtLb_valid (γ : EpNames) (i q : Nat) (σ : RState) (n : w32) :
    repFrag (GF := GF) γ i σ -∗ crtLb γ i q n -∗ ⌜zz n ≤ zz (σ.crtInstance q)⌝ := crtLb_validB γ i q σ n

theorem crtLb_mono (γ : EpNames) (i q : Nat) (n n' : w32) (h : zz n' ≤ zz n) :
    crtLb (GF := GF) γ i q n -∗ crtLb γ i q n' := crtLb_monoB γ i q n n' h

/-- The re-proposal tokens are the model's channel content: those held are a sub-multiset of it. -/
theorem inChan_sub (γ : EpNames) (S : Sys) (i : Nat) (ps : List Proposal) :
    sysAuth (GF := GF) γ S -∗ ([∗list] p ∈ ps, inChan γ i p) -∗ ⌜ps.Subperm (S.proposeChan i)⌝ := inChan_subB γ S i ps

theorem outbox_agree (γ : EpNames) (S : Sys) (i to : Nat) (ms : List Msg) :
    sysAuth (GF := GF) γ S -∗ outboxFrag γ i to ms -∗ ⌜S.outbox i to = ms⌝ := outbox_agreeB γ S i to ms

/-- The outbox fragments move with the authority (a step that sets replica `i`'s outbox to
`to`; the other tracked fields unchanged, the channels only grow: HUB-REQUEST epaxos-1). -/
theorem outbox_update (γ : EpNames) (S S' : Sys) (i to : Nat) (ms : List Msg)
    (h : ∀ j t, (j, t) ≠ (i, to) → S'.outbox j t = S.outbox j t)
    (hrest : S'.rep = S.rep ∧ S'.pending = S.pending ∧ S'.execCur = S.execCur ∧
      S'.execIdx = S.execIdx ∧ ∀ j, (S.proposeChan j).Subperm (S'.proposeChan j)) :
    sysAuth (GF := GF) γ S -∗ outboxFrag γ i to ms ==∗ sysAuth γ S' ∗ outboxFrag γ i to (S'.outbox i to) := outbox_updateB γ S S' i to ms h hrest

theorem pend_agree (γ : EpNames) (S : Sys) (i : Nat) (ob : Option Bcast) :
    sysAuth (GF := GF) γ S -∗ pendFrag γ i ob -∗ ⌜S.pending i = ob⌝ := pend_agreeB γ S i ob

theorem cur_agree (γ : EpNames) (S : Sys) (i : Nat) (cur : List InstId) (idx : Nat) :
    sysAuth (GF := GF) γ S -∗ curFrag γ i cur idx -∗ ⌜S.execCur i = cur ∧ S.execIdx i = idx⌝ := cur_agreeB γ S i cur idx

/-- Replica `i` idle (what the instance lock's invariant holds besides the state): its outboxes
empty, no pending broadcast, no component being executed. -/
def repIdle (γ : EpNames) (i : Nat) : IProp GF :=
  iprop(([∗list] to ∈ List.range nR, outboxFrag γ i to []) ∗ pendFrag γ i none ∗ curFrag γ i [] 0)

/-- The protocol's ghost state, fresh: names (`ProtoNames`), the authority of the
initial system, each replica's initial fragment, idle. -/
theorem sys_alloc :
    ⊢ |==> ∃ pn : ProtoNames, ∀ γ : EpNames, ⌜γ.proto = pn⌝ -∗
      sysAuth (GF := GF) γ Sys.init ∗
      ([∗list] i ∈ List.range nR, repFrag γ i (RState.init i) ∗ repIdle γ i) := sys_allocB

/-! ## The handlers' outputs, as resources -/

/-- What a handler's output gives its replica `i` once the ghost step is taken (besides the
outboxes and the pending broadcast, `outsOk`): a client reply's `fired` witness with the value it
may carry (for `ReplyProposeTS` on the op's connection), a re-proposal's channel token. -/
def outOk (γ : EpNames) (i : Nat) : Out → IProp GF
  | .send _ _ => iprop(True)
  | .bcast _ => iprop(True)
  | .reply p v => iprop(∃ o, fired γ p.cid o ∗ ⌜replyValOk o v⌝)
  | .repropose p => inChan γ i p
  | .ev _ => iprop(True)

/-- The messages of `outs` to `to`, in order. -/
def sendsTo (outs : List Out) (to : Nat) : List Msg :=
  outs.filterMap (fun o => match o with | .send t m => if t = to then some m else none | _ => none)

/-- A handler's outputs as resources: its outboxes, now the direct sends of `outs` per
destination (to hand to `SendMsg` one by one, `ep_sendUpd`), its pending broadcast (`pendOf`:
to run read by read, `ep_bcastStep`), the executor's idle progress, and each output's `outOk`. -/
def outsOk (γ : EpNames) (i : Nat) (outs : List Out) : IProp GF :=
  iprop(([∗list] to ∈ List.range nR, outboxFrag γ i to (sendsTo outs to)) ∗
    pendFrag γ i (pendOf outs) ∗ curFrag γ i [] 0 ∗
    [∗list] o ∈ outs, outOk γ i o)

/-! ## The protocol invariant -/

/-- The global protocol invariant (sealed): a ghost system `S` satisfying the pure invariant `Inv`,
whose abstract key-value state is the replicas' half of the client's state (`kvHalf`), whose fired
outputs are the escrow's authority (`firedAuth`), whose sent messages are the wire layer's lists
(the protocol layer's `sentHalf`, one per direction; the outboxes are in `sysAuth`), whose delivered positions hold their consumed
delivery tokens (so a fresh token is undelivered), and each of whose client proposals is a
registered client connection (its escrow, `clientConn`) with its `PROPOSE` token (the
acceptor's `connFresh cid true`, the framework's `opTok`) consumed and the op's command. -/
def epInvDef (γ : EpNames) : IProp GF :=
  iprop(∃ S : Sys, sysAuth γ S ∗ ⌜Inv S⌝ ∗ ⌜InvX S⌝ ∗ kvHalf γ S.kv ∗
    (∃ F : GMap Nat KvO, firedAuth γ F ∗ ⌜∀ cid, F.lookup cid = S.fired cid⌝ ∗
      [∗map] cid ↦ o ∈ F, fired γ cid o) ∗
    ([∗list] fr ∈ List.range nR, [∗list] to ∈ List.range nR,
      if fr = to then iprop(True) else sentHalf γ fr to (S.sent fr to)) ∗
    ([∗list] d ∈ S.delivered, delivTok γ d.2.1 d.1 d.2.2) ∗
    ([∗list] o ∈ S.ops, connFresh o.2.cid true ∗
      ∃ (c : w64) (inp : KvI), clientConn γ o.2.cid c inp ∗ ⌜o.2.cmd = cmdOf inp⌝))

@[irreducible] def epInv (γ : EpNames) : IProp GF := epInvDef γ

theorem epInv_unseal : epInv (GF := GF) = epInvDef := by
  funext; with_unfolding_all rfl

theorem epInvDef_eq (γ : EpNames) : epInvDef (GF := GF) γ = epInvB γ := rfl
theorem repIdle_eq (γ : EpNames) (i : Nat) : repIdle (GF := GF) γ i = repIdleB γ i := rfl
theorem outsOk_eq (γ : EpNames) (i : Nat) (outs : List Out) : outsOk (GF := GF) γ i outs = outsOkB γ i outs := by
  unfold outsOk outsOkB
  have : ∀ o, outOk (GF := GF) γ i o = outOkB γ i o := fun o => by cases o <;> rfl
  simp only [this, sendsTo, sendsToB]; rfl

/-- The invariant at the start (the start allocates `inv protoN (epInv γ)` from it): the initial
system's authority, the replicas' half of the initial abstract state, the empty fired map, the
empty message lists. -/
theorem epInv_init (γ : EpNames) :
    sysAuth (GF := GF) γ Sys.init -∗ kvHalf γ (kvScan w8).init -∗ firedAuth γ ∅ -∗
      ([∗list] fr ∈ List.range nR, [∗list] to ∈ List.range nR,
        if fr = to then iprop(True) else sentHalf γ fr to []) -∗
      epInv γ := by
  rw [epInv_unseal]; exact epInv_initB γ

/-! ## The ghost steps (the laws the handlers' proofs use)

Each takes the step of the model's `Step` that the code performs: a handler's at its start (the
ghost `Sys` is advanced to the handler's result when the input is taken, before the code moves:
`notes/stage1-plan.md`, B), a broadcast's at each `r.alive(q)` read (with the value read), the
executor's at a component's start, at each command and at each instance's end; under the
instance lock (`repFrag (GF := GF) γ i σ` held), with one credit to open the invariant (two for a command:
the second for its escrow, B8). -/

section steps
variable (γ : EpNames) (E : CoPset) (i : Nat)

/-- The run loop takes message `n` from `fr` (its `msgSent` fact and delivery token): the model's
`deliver` step. -/
theorem ep_deliver (σ : RState) (fr n : Nat) (m : Msg)
    (hE : ↑protoN ⊆ E) (hi : i < nR) (hfr : fr < nR) (hne : fr ≠ i) :
    ⊢ inv protoN (epInv (GF := GF) γ) -∗ repFrag γ i σ -∗ repIdle γ i -∗ msgSent γ fr i n m -∗
      delivTok γ i fr n -∗
      £ 1 ={E}=∗ repFrag γ i (hMsg σ m).1 ∗ outsOk γ i (hMsg σ m).2 := by
  rw [epInv_unseal, epInvDef_eq, repIdle_eq, outsOk_eq]; unfold repFrag
  iintro #Hinv Hf Hidle #Hs Ht Hlc
  imod ep_deliverB γ protoN E i σ fr n m hE hi hfr hne $$ Hinv Hf Hidle Hs Ht Hlc with ⟨-, Hf, Ho⟩
  imodintro
  iframe

/-- `startRecoveryForInstance` on a request for `x` taken from `instancesToRecover` (the request
carries `crtLb`: `x.i` at most the replica's `crtInstance[x.q]` when the executor made it). -/
theorem ep_recover (σ : RState) (x : InstId) (n : w32) (hE : ↑protoN ⊆ E) (hi : i < nR)
    (hq : x.q < nR) (hn : (x.i : Int) ≤ zz n) :
    ⊢ inv protoN (epInv (GF := GF) γ) -∗ repFrag γ i σ -∗ repIdle γ i -∗ crtLb γ i x.q n -∗ £ 1 ={E}=∗
      repFrag γ i (hRecover σ x).1 ∗ outsOk γ i (hRecover σ x).2 := by
  rw [epInv_unseal, epInvDef_eq]; rw [repIdle_eq, outsOk_eq]; unfold repFrag crtLb
  iintro #Hinv Hf Hidle #Hlb Hlc
  imod ep_recoverB γ protoN E i σ x n hE hi hq hn $$ Hinv Hf Hidle Hlb Hlc with ⟨-, Hf, Ho⟩
  imodintro
  iframe

/-- A broadcast's `r.alive(q)` read for its next peer `p` returned `a` (fix B4): the model's
`bcastStep`; on `true` the message is in `p`'s outbox, for the `SendMsg` that follows
(`ep_sendUpd`). -/
theorem ep_bcastStep (σ : RState) (b : Bcast) (p : Nat) (ps : List Nat) (a : Bool)
    (hE : ↑protoN ⊆ E) (hi : i < nR) (hb : b.peers = p :: ps) :
    ⊢ inv protoN (epInv (GF := GF) γ) -∗ repFrag γ i σ -∗ pendFrag γ i (some b) -∗ outboxFrag γ i p [] -∗
      £ 1 ={E}=∗ repFrag γ i (bcastRep σ b a) ∗ pendFrag γ i (b.next a) ∗
        outboxFrag γ i p (if a then [b.m] else []) := by
  rw [epInv_unseal, epInvDef_eq]
  exact ep_bcastStepB γ protoN E i σ b p ps a hE hi hb

/-- `BeTheLeader`. -/
theorem ep_beTheLeader (σ : RState) (hE : ↑protoN ⊆ E) (hi : i < nR) :
    ⊢ inv protoN (epInv (GF := GF) γ) -∗ repFrag γ i σ -∗ £ 1 ={E}=∗ repFrag γ i (hBeTheLeader σ) := by
  rw [epInv_unseal, epInvDef_eq]
  exact ep_beTheLeaderB γ protoN E i σ hE hi

/-- `ComputeClosestPeers` fixed the peer order `o`. -/
theorem ep_peerOrder (σ : RState) (o : List Nat) (hE : ↑protoN ⊆ E) (hi : i < nR)
    (ho : Sys.peerOrderOk i o) :
    ⊢ inv protoN (epInv (GF := GF) γ) -∗ repFrag γ i σ -∗ £ 1 ={E}=∗
      repFrag γ i { σ with peerOrder := o } := by
  rw [epInv_unseal, epInvDef_eq]
  exact ep_peerOrderB γ protoN E i σ o hE hi ho

/-- The executor starts a component (Tarjan popped `C`; `sort.Sort`): the model's `execSCC`. -/
theorem ep_execSCC (σ : RState) (C : List InstId) (hE : ↑protoN ⊆ E) (hi : i < nR)
    (hC : sccReady σ C) :
    ⊢ inv protoN (epInv (GF := GF) γ) -∗ repFrag γ i σ -∗ pendFrag γ i none -∗ curFrag γ i [] 0 -∗
      £ 1 ={E}=∗ repFrag γ i σ ∗ pendFrag γ i none ∗ curFrag γ i (sccSort σ C) 0 := by
  rw [epInv_unseal, epInvDef_eq]
  exact ep_execSCCB γ protoN E i σ C hE hi hC

/-- One iteration of the executor's per-command loop (fix B8): command `idx` of instance `x`
(record `w`), the model's `execCmd`. If its slot is executed for the first time anywhere, its op
linearizes here: the escrow fires from `S.kv` (`escrow_fire` with the second credit;
`fire_kv_step`, `kv_step_det`), hence the mask with the escrows and the clients' namespace; a
client reply gets its op's `fired` witness (`inv_exec_first`, `inv_exec_again`). -/
theorem ep_execCmd (σ : RState) (x : InstId) (rest : List InstId) (w : InstRec) (idx : Nat)
    (hE : ↑protoN ⊆ E) (hEe : ↑escrowN ⊆ E) (hEc : ⊤ \ epEop ⊆ E) (hi : i < nR)
    (hw : σ.inst x = some w) (hidx : idx < (w.cmds.getD []).length) :
    ⊢ inv protoN (epInv (GF := GF) γ) -∗ repFrag γ i σ -∗ curFrag γ i (x :: rest) idx -∗ £ 2 ={E}=∗
      repFrag γ i (execCmdAt σ w idx).1 ∗ curFrag γ i (x :: rest) (idx + 1) ∗
        [∗list] o ∈ (execCmdAt σ w idx).2, outOk γ i o := by
  rw [epInv_unseal, epInvDef_eq]
  exact ep_execCmdB γ protoN E i σ x rest w idx hE hEe hEc protoN_escrowN_disj protoN_epEop
    hi hw hidx

/-- The executor ends instance `x` (`w.Status = EXECUTED`): the model's `instDone`. -/
theorem ep_instDone (σ : RState) (x : InstId) (rest : List InstId) (w : InstRec)
    (hE : ↑protoN ⊆ E) (hi : i < nR) (hw : σ.inst x = some w) :
    ⊢ inv protoN (epInv (GF := GF) γ) -∗ repFrag γ i σ -∗
      curFrag γ i (x :: rest) (w.cmds.getD []).length -∗ £ 1 ={E}=∗
      repFrag γ i (execDone σ x) ∗ curFrag γ i rest 0 := by
  rw [epInv_unseal, epInvDef_eq]
  exact ep_instDoneB γ protoN E i σ x rest w hE hi hw

/-- The executor's scan moves `ExecedUpTo[q]`. -/
theorem ep_execBump (σ : RState) (q : Nat) (hE : ↑protoN ⊆ E) (hi : i < nR) (hq : q < nR)
    (he : σ.executed ⟨q, toN (σ.execedUpTo q + 1)⟩) :
    ⊢ inv protoN (epInv (GF := GF) γ) -∗ repFrag γ i σ -∗ £ 1 ={E}=∗ repFrag γ i (execBump σ q) := by
  rw [epInv_unseal, epInvDef_eq]
  exact ep_execBumpB γ protoN E i σ q hE hi hq he

/-- The send update a handler hands to `SendMsg(to, m)` for the head `m` of its outbox: inside
(at `⊤`, holding `r.M`), the model's `flush` step: the protocol layer's half and the framework's
are appended together (`sentHalf_append`), so `m` becomes message `ms.length` from `i` to `to`
(`epInv`'s parts it touches are timeless: no credit). `SendMsg` runs it only when the peer's
writer is not `nil` (`replica.Replica.SendMsg.spec`); otherwise the caller takes `ep_sendLost`
(the handler offers both: `sendUpd … ∧ |={E}=> outboxFrag γ i to rest`). -/
theorem ep_sendUpd (to : Nat) (m : Msg) (rest : List Msg) :
    ⊢ inv protoN (epInv (GF := GF) γ) -∗ outboxFrag γ i to (m :: rest) -∗
      sendUpd γ i to m (outboxFrag γ i to rest) := by
  rw [epInv_unseal, epInvDef_eq]; unfold sendUpd
  exact ep_sendUpdB γ protoN i to m rest

/-- `SendMsg` found the peer's writer `nil` (nothing written, the send update not run): the
model's `lose` step drops the head of the outbox (no position of `sent` is taken). -/
theorem ep_sendLost (to : Nat) (m : Msg) (rest : List Msg) (hE : ↑protoN ⊆ E) :
    ⊢ inv protoN (epInv (GF := GF) γ) -∗ outboxFrag γ i to (m :: rest) ={E}=∗ outboxFrag γ i to rest := by
  rw [epInv_unseal, epInvDef_eq]
  exact ep_sendLostB γ protoN E i to m rest hE

end steps

/-! ## What a replica id gets at registration -/

/-- Replica `i`'s protocol start resources (for `Registry.lean`'s `repStart`, carried by the
registration exchange, with the framework's `repFwStart γ i`): its initial fragment, idle, and
the protocol invariant (persistent). -/
def epRepStart (γ : EpNames) (i : Nat) : IProp GF :=
  iprop(repFrag γ i (RState.init i) ∗ repIdle γ i ∗ inv protoN (epInv γ))

end ghost

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
