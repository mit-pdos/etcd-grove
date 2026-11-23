/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/Defs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The swift replica's internal predicates (the swift group's; not frozen). The design (who owns
which field, under which lock or invariant) is notes/prove-swift.md §1; this file states the
parts the proved functions use so far.

* `swift.fld r f`: field `f` of the `*swift.Replica` at `r`.
* `swift.ballotLInv r`: `ballotL`'s lock invariant (R6): a quarter of `ballot`, non-negative.
* `swift.readerBorrow m R`: the right to borrow a reader token bundle of the concurrent map `m`
  (`IsEmpty`, `Has`, `Get`, `IterCb` take one) for a call and give it back. `New` makes
  `cmapReaders` bundles; turning them into an unbounded borrowing right needs the thread bound
  (fewer than `2^30` threads hold one at a time: `ThreadBoundLe`), see notes/prove-swift.md.
* `swift.anyInv r`: `deliveredAny`'s invariant (fork change P2-A): the flag's value is free
  (BeTheLeader's both branches are safe), `deliver`/`handleSync` open it for their stores.
* `swift.rcvrRes r γc γm`: what the rpc methods (`BeTheLeader`, `Ping`) need, persistent.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.Defs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumSpecs
public import Dsverify.Proof.github_com.orcaman.concurrent_map.Specs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Pkg
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Inv
public import Perennial.Proof.sync.atomic.Base

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]

/-- Field `f` of the swift replica at `r`. -/
abbrev swift.fld (r : Loc) (f : GoString) : Loc := structFieldRef swift.Replica f r

/-- `ballotL`'s lock invariant (R6): a quarter of `ballot` (the run loop holds the rest while
it may write it), a non-negative ballot. -/
def swift.ballotLInv (r : Loc) : IProp netDistGF :=
  iprop(∃ b : w32, typedPointsto (swift.fld r go!"ballot") b (DFrac.own (1 : Qp).half.half) ∗
    ⌜0 ≤ sint.Z b⌝)

/-- The right to borrow a reader token bundle of `m` around a call (persistent). -/
def swift.readerBorrow (m : GoSlice) (R : GoString → GoInterface → IProp netDistGF) :
    IProp netDistGF :=
  iprop(□ |={⊤}=> github_com.orcaman.concurrent_map.reader m R ∗ (github_com.orcaman.concurrent_map.reader m R ={⊤}=∗ True))

instance swift.readerBorrow_persistent (m : GoSlice) (R : GoString → GoInterface → IProp netDistGF) :
    Persistent (swift.readerBorrow m R) := by
  unfold swift.readerBorrow; infer_instance

/-- The right to borrow a reader token bundle of the map `m` (ghost view `γ`, cmap's strong
specs) around a call (persistent). FRAMEWORK: established at `New` only with the thread bound
(notes/prove-swift.md §6). -/
def swift.readerBorrowV (m : GoSlice) (γ : GName) (R : GoString → GoInterface → IProp netDistGF) :
    IProp netDistGF :=
  iprop(□ |={⊤}=> github_com.orcaman.concurrent_map.readerV m γ R ∗
    (github_com.orcaman.concurrent_map.readerV m γ R ={⊤}=∗ True))

instance swift.readerBorrowV_persistent (m : GoSlice) (γ : GName)
    (R : GoString → GoInterface → IProp netDistGF) : Persistent (swift.readerBorrowV m γ R) := by
  unfold swift.readerBorrowV; infer_instance

/-- `deliveredAny`'s invariant namespace (fork change P2-A). -/
def swift.anyN : Namespace := ndot nroot "swiftpaxos.deliveredAny"

/-- `deliveredAny` (an `atomic.Bool`, fork change P2-A, notes/prove-swift.md §13): some value,
under an invariant (persistent). `BeTheLeader` loads it, `deliver` stores `true`, `handleSync`
stores `false`; its value is not related to `delivered` (no proof needs it). -/
def swift.anyInv (r : Loc) : IProp netDistGF :=
  iprop(isPkgInit (PROP := IProp netDistGF) pkg_id.sync.atomic ∗
    inv swift.anyN (∃ b : Bool, sync.atomic.ownBool (swift.fld r go!"deliveredAny") (DFrac.own 1) b))

instance swift.anyInv_persistent (r : Loc) : Persistent (swift.anyInv r) := by
  unfold swift.anyInv; infer_instance

/-- What `delivered`'s entries say: nothing the rpc methods need (its entries' facts are the
execution record's, notes/prove-swift.md §1.3). -/
abbrev swift.deliveredR : GoString → GoInterface → IProp netDistGF := fun _ _ => iprop(True)

/-- **`b` is one of this replica's own ballots** (D56 N1-c): non-negative, `b mod N` its `Id`
(the replica `r`'s embedded `Replica`, its `N` and `Id`). -/
def swift.ownBallot (r : Loc) (b : w32) : IProp netDistGF :=
  iprop(∃ (rr : Loc) (N : Nat) (me : w32), swift.fld r go!"Replica" ↦□ rr ∗
    replica.fld rr go!"N" ↦□ (W64 N) ∗ replica.fld rr go!"Id" ↦□ me ∗
    ⌜1 ≤ N ∧ N ≤ 7 ∧ 0 ≤ sint.Z b ∧ sint.Z b % (N : Int) = sint.Z me⌝)

/-- **The `recover` channel's values** (D56 N1-c): `-1` (`BallotAt(1)` without a quorum file,
the kit's configuration) or one of this replica's own ballots. -/
def swift.recoverOk (r : Loc) (b : w32) : IProp netDistGF :=
  iprop(⌜sint.Z b = -1⌝ ∨ swift.ownBallot r b)

instance swift.ownBallot_persistent (r : Loc) (b : w32) : Persistent (swift.ownBallot r b) := by
  unfold swift.ownBallot; infer_instance

instance swift.recoverOk_persistent (r : Loc) (b : w32) : Persistent (swift.recoverOk r b) := by
  unfold swift.recoverOk; infer_instance

/-- What the rpc methods (`BeTheLeader`, `Ping`) need (persistent): the embedded replica's `N`
and `Id`, the configuration's view, `delivered` and `deliveredAny`'s invariant (P2-A: no reader
bundle of `delivered` any more), the quorum
system (the map's ghost view `γdl` is the run loop's), the `recover` channel (its values
`swift.recoverOk`: -1 or this replica's own ballots, D56 N1-c), `ballotL`. -/
def swift.rcvrRes (r : Loc) (γc γm : GName) : IProp netDistGF :=
  iprop(∃ (rr : Loc) (N : Nat) (fr : Bool) (l : List GoString) (me : w32) (dm : GoSlice)
      (qs : Loc) (rc : Loc) (γrc : ChanNames) (γdl : GName),
    swift.fld r go!"Replica" ↦□ rr ∗ replica.fld rr go!"N" ↦□ (W64 N) ∗
    replica.fld rr go!"Id" ↦□ me ∗ sp.cfg γc γm N fr l ∗
    ⌜1 ≤ N ∧ N ≤ 7 ∧ 0 ≤ sint.Z me ∧ sint.Z me < N⌝ ∗
    swift.fld r go!"delivered" ↦□ dm ∗ github_com.orcaman.concurrent_map.isCMapV dm γdl swift.deliveredR ∗
    swift.anyInv r ∗
    swift.fld r go!"qs" ↦□ qs ∗ replica.quorum.isQS qs N ∗
    swift.fld r go!"recover" ↦□ rc ∗ isChanBag γrc rc (swift.recoverOk r) ∗
    sync.isMutex (swift.fld r go!"ballotL") (swift.ballotLInv r))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 1000000 in
instance swift.rcvrRes_persistent (r : Loc) (γc γm : GName) :
    Persistent (swift.rcvrRes r γc γm) := by
  unfold swift.rcvrRes; infer_instance

end defs

/-- `CommandId`'s countable instance (one for the whole package: the channels of `CommandId`s,
`deliverChan` and `recheckChan`, are typed with it in `New` and in the descriptors' proofs). -/
instance swift.CommandId_countable [GooseExts] : Pos.Countable swift.CommandId :=
  countableOfLeftInverse (fun c : swift.CommandId => (c.ClientId', c.SeqNum'))
    (fun p => ⟨p.1, p.2⟩) (fun _ => rfl)

end Perennial.github_com.imdea_software.swiftpaxos
