/-
The heap side of the epaxos package's interface, split out of `Epaxos/Interface/Epaxos.lean`
(statements unchanged, moved so that the package's proofs can import them and
`Epaxos/Interface/Epaxos.lean` can import the proofs): `ownRep` and its pieces, `ep_propose`, the
instance lock's invariant, the replica handle `isReplica (GF := GF)`. See `Epaxos/Interface/Epaxos.lean`'s
header.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.EpaxosGhost
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.Replica
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.GhostPropose

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model

attribute [local instance] GooseGlobalGS.gooseInvGS

section fld
variable [GooseExts] [GoLocalContext] [GoGlobalContext] [go.Semantics]

/-- A field of `*epaxos.Replica`. -/
abbrev efld (r : Loc) (f : GoString) : Loc := structFieldRef epaxos.Replica f r

end fld

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : TreemapHyp GF]

/-! ## Pieces -/

/-- A command slice field: `nil` for `none`, else a non-nil read-only slice with the commands. -/
def cmdsRep (sl : GoSlice) : Option (List WCmd) → IProp GF
  | none => iprop(⌜sl = slice.nil⌝)
  | some cs => iprop(⌜sl ≠ slice.nil⌝ ∗ ownCmds sl cs DFrac.discard)

/-- A client proposal `g` held in a leader's bookkeeping, with its op `p` (the framework's
`proposal γ i g` with its connection and command fixed): until the instance is executed here (and
the reply sent), the connection's reply token. -/
def propHeld (γ : EpNames) (i : Nat) (executed : Bool) (g : Loc) (p : Proposal) :
    IProp GF :=
  iprop(∃ (pp w mu : Loc) (proxy : Bool) (addr : GoString) (c : w64) (inp : KvI)
      (cv : state.Command),
    g ↦□ replica.defs.GPropose.mk pp w mu proxy addr ∗
    pp ↦□ replica.defs.Propose.mk (W32 0) (W32 (uint.Z c)) cv (W64 0) ∗ cmdOk cv (cmdOf inp) ∗
    clientConn γ p.cid c inp ∗ ⌜p.cmd = cmdOf inp⌝ ∗ clientWriter γ i w p.cid ∗
    (if executed then iprop(True) else replyTok γ i w))

/-- A stored reply's command slice: `nil` if the reply was recorded without commands
(`cmdsNil`), else a read-only slice with the commands (possibly `nil` when there are none: a
decoded empty slice). -/
def prCmds (sl : GoSlice) (cnil : Bool) (cs : List WCmd) : IProp GF :=
  if cnil then iprop(⌜sl = slice.nil⌝) else ownCmds sl cs DFrac.discard

/-- An entry of `lb.prepareReplies` (read-only, its arrays possibly shared with an instance's or
the bookkeeping's). -/
def ownPReply (l : Loc) (pr : PReply) : IProp GF :=
  iprop(∃ (cs ds : GoSlice) (dq : DFrac),
    l ↦□ epaxos.PrepareReply.mk pr.m.acceptorId pr.m.replica pr.m.inst pr.m.ballot
      pr.m.vballot pr.m.status cs pr.m.seq ds ∗
    prCmds cs pr.cmdsNil pr.m.command ∗ ds ↦*{dq} pr.m.deps)

/-- A `*LeaderBookkeeping` with image `lb`: `lb.deps` owned while `lbDepsOwned lb` (where
`mergeAttributes` writes into it), a read-only fraction otherwise (fix B7). -/
def ownLb (γ : EpNames) (i : Nat) (executed : Bool) (lbp : Loc) (lb : LbRec) :
    IProp GF :=
  iprop(∃ (y : epaxos.LeaderBookkeeping) (gs prs : List Loc),
    lbp ↦ y ∗
    ⌜y.ballot' = lb.ballot ∧ y.allEqual' = lb.allEqual ∧ y.preAcceptOKs' = lb.preAcceptOKs ∧
      y.acceptOKs' = lb.acceptOKs ∧ y.nacks' = lb.nacks ∧ y.preparing' = lb.preparing ∧
      y.tryingToPreAccept' = lb.tryingToPreAccept ∧ y.lastTriedBallot' = lb.lastTriedBallot ∧
      y.status' = lb.status ∧ y.seq' = lb.seq ∧ y.leaderResponded' = lb.leaderResponded ∧
      y.preAcceptsSent' = lb.preAcceptsSent⌝ ∗
    (match lb.clientProposals with
      | none => iprop(⌜y.clientProposals' = slice.nil⌝)
      | some ps => iprop(⌜y.clientProposals' ≠ slice.nil ∧ gs.length = ps.length⌝ ∗
          y.clientProposals' ↦*□ gs ∗
          [∗list] k ↦ g ∈ gs, propHeld γ i executed g (ps.getD k default))) ∗
    cmdsRep y.cmds' lb.cmds ∗
    (if lbDepsOwned lb then iprop(y.deps' ↦* lb.deps)
      else iprop(∃ dq : DFrac, y.deps' ↦*{dq} lb.deps)) ∗
    (y.prepareReplies' ↦* prs ∗ ownSliceCap Loc y.prepareReplies' (DFrac.own 1)) ∗ ⌜prs.length = lb.prepareReplies.length⌝ ∗
    [∗list] k ↦ l ∈ prs, ownPReply l (lb.prepareReplies.getD k default))

/-- An `*Instance` `p` with image `w`, at id `x`. -/
def ownInst (γ : EpNames) (i : Nat) (x : InstId) (p : Loc) (w : InstRec) : IProp GF :=
  iprop(∃ y : epaxos.Instance,
    p ↦ y ∗
    ⌜y.bal' = w.bal ∧ y.vbal' = w.vbal ∧ y.Status' = w.status ∧ y.Seq' = w.seq ∧
      (w.status ≠ stEXECUTED → y.Index' = W64 0)⌝ ∗
    y.id' ↦□ epaxos.instanceId.mk (W32 x.q) (W32 x.i) ∗
    cmdsRep y.Cmds' w.cmds ∗
    (∃ dq : DFrac, y.Deps' ↦*{dq} w.deps) ∗
    (match w.lb with
      | none => iprop(⌜y.lb' = null⌝)
      | some lb => iprop(⌜y.lb' ≠ null⌝ ∗ ownLb γ i (decide (w.status = stEXECUTED)) y.lb' lb)))

/-- Row `q` of `InstanceSpace`: `MAX_INSTANCE` pointers, `nil` where there is no instance. -/
def ownRow (γ : EpNames) (i q : Nat) (row : GoSlice) (σ : RState) : IProp GF :=
  iprop(∃ ptrs : List Loc, row ↦* ptrs ∗ ⌜ptrs.length = MAX_INSTANCE⌝ ∗
    [∗list] n ↦ p ∈ ptrs,
      match σ.inst ⟨q, n⟩ with
      | none => iprop(⌜p = null⌝)
      | some w => ownInst γ i ⟨q, n⟩ p w)

/-- `conflicts[q]`: a `map[state.Key]*InstPair` with image `row`. -/
def ownConflictRow (m : GoMap) (row : w64 → Option InstPair) : IProp GF :=
  iprop(∃ g : GMap w64 Loc, m ↦$ g ∗ ⌜∀ k, (g.lookup k).isSome = (row k).isSome⌝ ∗
    [∗map] k ↦ l ∈ g,
      l ↦ ((row k).map (fun p => epaxos.InstPair.mk p.last p.lastWrite)).getD zeroValDef)

/-! ## The proposal step -/

/-- What the run loop holds for a proposal `p` of a batch it took from `ProposeChan`: a fresh one
(its op token, the framework's `opTok`, and its connection's escrow), or a re-proposal (its
re-proposal token). -/
def batchElemOk (γ : EpNames) (i : Nat) (p : Proposal) : IProp GF :=
  iprop((opTok γ p.cid ∗ ∃ (c : w64) (inp : KvI), clientConn γ p.cid c inp ∗ ⌜p.cmd = cmdOf inp⌝) ∨
    inChan γ i p)

/-- `handlePropose` on a batch (the proposals the run loop received, in any order: one when the
row is full): the model's `clientPropose` steps for the fresh proposals (their op tokens go into
`epInv`), then its `propose` step on the batch, a sub-multiset of the channel (the re-proposals'
tokens, `inChan_sub`, and the fresh ones; fix B5). -/
theorem ep_propose (γ : EpNames) (E : CoPset) (i : Nat) (σ : RState) (batch : List Proposal)
    (hE : ↑protoN ⊆ E) (hi : i < nR) (hb : batch ≠ [])
    (hfull : rowFull σ = true → batch.length = 1) (hlen : batch.length < 2 ^ 62) :
    ⊢ inv protoN (epInv (GF := GF) γ) -∗ repFrag γ i σ -∗ repIdle γ i -∗
      ([∗list] p ∈ batch, batchElemOk γ i p) -∗ £ 1 ={E}=∗
      repFrag γ i (hPropose σ batch).1 ∗ outsOk γ i (hPropose σ batch).2 := by
  rw [epInv_unseal, epInvDef_eq, repIdle_eq, outsOk_eq]
  unfold batchElemOk repFrag inChan
  iintro #Hinv Hf Hidle Hb Hlc
  imod ep_proposeB γ protoN E i σ batch hE hi hb hfull hlen $$ Hinv Hf Hidle Hb Hlc with ⟨-, Hf, Ho⟩
  imodintro
  iframe

/-! ## The replica's protocol state -/

/-! ### The body of `ownRep`, by piece (the epaxos prover's refinement; see
`notes/prove-epaxos.md`): each piece speaks of one field of `RState`, so that a step changing one
field changes one piece. -/

/-- Row `q` of `InstanceSpace` over the instance map `inst` (`ownRow`, by the map). -/
def ownRowI (γ : EpNames) (i q : Nat) (row : GoSlice) (inst : InstId → Option InstRec) :
    IProp GF :=
  iprop(∃ ptrs : List Loc, row ↦* ptrs ∗ ⌜ptrs.length = MAX_INSTANCE⌝ ∗
    [∗list] n ↦ p ∈ ptrs,
      match inst ⟨q, n⟩ with
      | none => iprop(⌜p = null⌝)
      | some w => ownInst γ i ⟨q, n⟩ p w)

/-- The `InstanceSpace` rows. -/
def repInsts (γ : EpNames) (i : Nat) (r : Loc) (inst : InstId → Option InstRec) :
    IProp GF :=
  iprop(∃ (iss : GoSlice) (rows : List GoSlice),
    efld r go!"InstanceSpace" ↦□ iss ∗ iss ↦*□ rows ∗ ⌜rows.length = nR⌝ ∗
    [∗list] q ↦ row ∈ rows, ownRowI γ i q row inst)

/-- A per-row `[]int32` field (`crtInstance`, `CommittedUpTo`, `ExecedUpTo`, `lastScan`,
`lastPut`) with image `f`. -/
def repRowArr (r : Loc) (fname : GoString) (f : Nat → w32) : IProp GF :=
  iprop(∃ sl : GoSlice, efld r fname ↦□ sl ∗ sl ↦* ((List.range nR).map f))

/-- `conflicts`. -/
def repConf (r : Loc) (conf : Nat → w64 → Option InstPair) : IProp GF :=
  iprop(∃ (cfs : GoSlice) (cms : List GoMap),
    efld r go!"conflicts" ↦□ cfs ∗ cfs ↦*□ cms ∗ ⌜cms.length = nR⌝ ∗
    [∗list] q ↦ m ∈ cms, ownConflictRow m (conf q))

/-- `maxSeqPerKey`. -/
def repMsk (r : Loc) (msk : w64 → Option w32) : IProp GF :=
  iprop(∃ (m : GoMap) (g : GMap w64 w32), efld r go!"maxSeqPerKey" ↦□ m ∗ m ↦$ g ∗
    ⌜∀ k, g.lookup k = msk k⌝)

/-- The store (the framework's `r.State`). -/
def repStore (r : Loc) (store : w64 → Option (List w8)) : IProp GF :=
  iprop(∃ (rr st : Loc) (S : GMap w64 (List w8)),
    efld r go!"Replica" ↦□ rr ∗ fld rr go!"State" ↦□ st ∗ isState st S ∗
    ⌜∀ k, S.lookup k = store k⌝)

/-- The peer order. -/
def repPeer (r : Loc) (i : Nat) (po : List Nat) : IProp GF :=
  iprop(⌜po = (RState.init i).peerOrder⌝ ∨
    ∃ (rr : Loc) (L : List GoString) (ord : List w32), efld r go!"Replica" ↦□ rr ∗
      prefOrder rr i L ord ∗ ⌜L.length = nR ∧ po = ord.map (fun x => sint.nat x)⌝)

/-- No instance outside the rows, nor in the last slot of a row (fix R-CAP: `updateCommitted`'s
scan stops there). -/
def instBounds (inst : InstId → Option InstRec) : Prop :=
  ∀ x : InstId, nR ≤ x.q ∨ MAX_INSTANCE - 1 ≤ x.i → inst x = none

/-- `CommittedUpTo[q] + 1` indexes the row (`updateCommitted`'s scan). -/
def cutBounds (cut : Nat → w32) : Prop :=
  ∀ q < nR, -1 ≤ zz (cut q) ∧ zz (cut q) + 2 ≤ MAX_INSTANCE

/-- The heap image of replica `i`'s protocol state `σ` at `r` (see the file header), by piece. -/
def ownRepDef (γ : EpNames) (i : Nat) (r : Loc) (σ : RState) : IProp GF :=
  iprop(⌜instBounds σ.inst⌝ ∗ ⌜cutBounds σ.committedUpTo⌝ ∗
    repInsts γ i r σ.inst ∗
    repRowArr r go!"crtInstance" σ.crtInstance ∗
    repRowArr r go!"CommittedUpTo" σ.committedUpTo ∗
    repRowArr r go!"ExecedUpTo" σ.execedUpTo ∗
    repConf r σ.conflicts ∗ repMsk r σ.maxSeqPerKey ∗
    repRowArr r go!"lastScan" σ.lastScan ∗ repRowArr r go!"lastPut" σ.lastPut ∗
    efld r go!"maxSeq" ↦ σ.maxSeq ∗ efld r go!"IsLeader" ↦ σ.isLeader ∗
    efld r go!"maxRecvBallot" ↦ σ.maxRecvBallot ∗
    repStore r σ.store ∗ repPeer r i σ.peerOrder)

@[irreducible] def ownRep (γ : EpNames) (i : Nat) (r : Loc) (σ : RState) : IProp GF :=
  ownRepDef γ i r σ

theorem ownRep_unseal : ownRep (GF := GF) = ownRepDef := by funext; with_unfolding_all rfl

/-- The executor's Tarjan stack, reached through `r.exec` (`New`'s
`r.exec = &Exec{r: r, stack: make([]*Instance, 0, 100)}`, never written after; `findSCC` and
`strongconnect` read and write `exec.stack` and its elements, append to it, always under the
instance lock): `exec.stack`'s points-to and its slice's elements and capacity (positive: `New` makes it 100, it only grows; HUB exec-E1). (`Index` of the
entries: reset by `findSCC`, `ownInst`.) -/
def execStackOwn (r : Loc) : IProp GF :=
  iprop(∃ (e : Loc) (s : GoSlice) (xs : List Loc), efld r go!"exec" ↦□ e ∗
    structFieldRef epaxos.Exec go!"stack" e ↦ s ∗ s ↦* xs ∗ ownSliceCap Loc s (DFrac.own 1) ∗
    ⌜0 < sint.Z s.cap⌝)

/-- The instance lock's invariant (fix E1): replica `i`'s protocol state in the heap and in the
ghost `Sys` (its fragment), idle (empty outboxes, no pending broadcast, no component being
executed), and the executor's Tarjan stack `r.exec.stack` (only the executor touches it, always
under the lock; `New` puts it here). -/
def instLockInv (γ : EpNames) (i : Nat) (r : Loc) : IProp GF :=
  iprop((∃ σ : RState, ownRep γ i r σ ∗ repFrag γ i σ ∗ repIdle γ i) ∗ execStackOwn r)

/-! ## The replica handle -/

/-- The protocol's read-only fields (set by `New`) that the rpc methods may read: the rpc codes
`epaxos.New` registered (9 .. 17) and `transconf`. (Not here: `exec`, `instancesToRecover`, the
nine `*Chan` fields and `batchWait`, which only `run()` and the executor read: `run`'s own
precondition, from `New`, T2-8. The channels' invariants are the framework's `tableOk`, read
through the rpc table.) -/
def epROFields (r : Loc) : IProp GF :=
  iprop(efld r go!"prepareRPC" ↦□ W8 9 ∗ efld r go!"prepareReplyRPC" ↦□ W8 10 ∗
    efld r go!"preAcceptRPC" ↦□ W8 11 ∗ efld r go!"preAcceptReplyRPC" ↦□ W8 12 ∗
    efld r go!"acceptRPC" ↦□ W8 13 ∗ efld r go!"acceptReplyRPC" ↦□ W8 14 ∗
    efld r go!"commitRPC" ↦□ W8 15 ∗ efld r go!"tryPreAcceptRPC" ↦□ W8 16 ∗
    efld r go!"tryPreAcceptReplyRPC" ↦□ W8 17 ∗ efld r go!"transconf" ↦□ false)

/-- Replica `i`'s handle (persistent): the framework's read-only part through the embedded
pointer (`fwRO`; `isReplicaFw` once `ConnectToPeers` returned is the run loop's, not needed by
the rpc methods), the protocol's read-only fields, the instance lock with `instLockInv`, the
protocol invariant, the package's initialization fact (the rpc methods' specs need it). -/
def isReplicaDef (γ : EpNames) (i : Nat) (r : Loc) : IProp GF :=
  iprop(∃ (rr : Loc) (L : List GoString) (p : FwPtrs),
    efld r go!"Replica" ↦□ rr ∗ fwRO γ rr i L p ∗ ⌜L.length = nR⌝ ∗ epROFields r ∗
    (∃ lp : Loc, efld r go!"lock" ↦□ lp ∗ sync.isMutex lp (instLockInv γ i r)) ∗
    inv protoN (epInv γ) ∗ pkgInit_epaxos)

@[irreducible] def isReplica (γ : EpNames) (i : Nat) (r : Loc) : IProp GF :=
  isReplicaDef γ i r

theorem isReplica_unseal : isReplica (GF := GF) = isReplicaDef := by funext; with_unfolding_all rfl

instance lockOwn_persistent (r : Loc) (R : IProp GF) :
    Persistent (iprop(∃ lp : Loc, efld r go!"lock" ↦□ lp ∗ sync.isMutex lp R)) := by
  infer_instance

instance isReplicaDef_persistent (γ : EpNames) (i : Nat) (r : Loc) :
    Persistent (isReplicaDef (GF := GF) γ i r) := by
  unfold isReplicaDef epROFields; infer_instance

instance isReplica_persistent (γ : EpNames) (i : Nat) (r : Loc) : Persistent (isReplica (GF := GF) γ i r) := by
  rw [isReplica_unseal]; infer_instance

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
