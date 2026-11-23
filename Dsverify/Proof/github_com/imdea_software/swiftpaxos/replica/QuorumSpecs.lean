/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/QuorumSpecs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`replica/quorum.go` (and `Leader`, `NextBallotOf` of `replica/replica.go`): the replica group's
internal specs (not frozen), over the pure model `QuorumPure.lean`.

* A quorum (`Quorum`, a `map[int32]struct{}`) holding the replicas `s` (`qOwn q dq s`);
* a quorum set as `NewQuorumSet(N / 2 + 1, N)` builds it, read only from then on (`qsIs qs N`):
  for every leader `l < N`, `qs[l]` maps `qid` to the `qid`-th fast quorum containing `l`
  (`lqs N l`), in `subsets`' enumeration order;
* the quorum system of the deployment (no quorum file: `config.plain`), `isQS sys N`
  (persistent): `qs` as above and no listed ballots.

Premises the callers supply (and why): `1 ≤ N ≤ 7` (the membership's size; `numAQ_pos` is
checked for these `N`); a non-negative ballot for `AQ`, `SameHigher` (a negative one makes Go's
`%` negative, `qs[l]` nil and the next `%` a division by zero: F1). `NextBallotOf` and
`SameHigher` return the int32 arithmetic's (wrapping) value; `nextBallot_val` gives its exact
value when the caller knows it fits.
-/
module

public import Dsverify.GeneratedProof.github_com.imdea_software.swiftpaxos.replica
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Perennial.Proof.errors.NewVar
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumPure
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Base

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace replica.quorum

/-- A replica id as an int32 key. -/
def w32n (j : Nat) : w32 := W32 (j : Int)

/-- The map `m` is the set of replicas `s`. -/
def qRepr (m : GMap w32 Unit) (s : List Nat) : Prop :=
  ∀ k, m !! k = if k ∈ s.map w32n then some () else none

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF]
variable [sem : go.Semantics]

/-- The `Quorum` `q` holds the replicas `s`. -/
def qOwn (q : Loc) (dq : DFrac) (s : List Nat) : IProp netDistGF :=
  iprop(∃ m : GMap w32 Unit, q ↦${dq} m ∗ ⌜qRepr m s⌝)

/-- The `QuorumsOfLeader` `p` lists the quorums `Q` (by `qid`, from 0); each quorum persistent. -/
def lqsOwn (p : Loc) (dq : DFrac) (Q : List (List Nat)) : IProp netDistGF :=
  iprop(∃ m : GMap w32 Loc, p ↦${dq} m ∗
    ⌜Q.length < 2 ^ 31 ∧ ∀ k : w32, (m !! k).isSome ↔ ∃ i < Q.length, k = w32n i⌝ ∗
    [∗list] i ↦ s ∈ Q, ∃ ql, ⌜m !! w32n i = some ql⌝ ∗ qOwn ql DFrac.discard s)

/-- The `QuorumSet` `qs` (persistent) gives leader `l < N` the quorums `L l`. -/
def qsOwn (qs : Loc) (N : Nat) (L : Nat → List (List Nat)) (dq : DFrac) : IProp netDistGF :=
  iprop(∃ m : GMap w32 Loc, qs ↦$□ m ∗
    ⌜∀ k : w32, (m !! k).isSome ↔ ∃ l < N, k = w32n l⌝ ∗
    [∗list] l ∈ List.range N, ∃ p, ⌜m !! w32n l = some p⌝ ∗ lqsOwn p dq (L l))

/-- The quorum set of `NewQuorumSet(N / 2 + 1, N)` (persistent). -/
def qsIs (qs : Loc) (N : Nat) : IProp netDistGF :=
  iprop(⌜1 ≤ N ∧ N ≤ 7⌝ ∗ qsOwn qs N (lqs N) DFrac.discard)

/-- The deployment's quorum system (no quorum file), persistent. -/
def isQS (sys : Loc) (N : Nat) : IProp netDistGF :=
  iprop(∃ qs : Loc, sys ↦□ (replica.QuorumSystem.mk qs slice.nil) ∗ qsIs qs N)

instance qOwn_persistent (q : Loc) (s : List Nat) :
    Persistent (qOwn q DFrac.discard s) := by unfold qOwn; infer_instance
instance lqsOwn_persistent (p : Loc) (Q : List (List Nat)) :
    Persistent (lqsOwn p DFrac.discard Q) := by unfold lqsOwn; infer_instance
instance qsOwn_persistent (qs : Loc) (N : Nat) (L : Nat → List (List Nat)) :
    Persistent (qsOwn qs N L DFrac.discard) := by unfold qsOwn; infer_instance
instance qsIs_persistent (qs : Loc) (N : Nat) : Persistent (qsIs qs N) := by
  unfold qsIs; infer_instance
instance isQS_persistent (sys : Loc) (N : Nat) : Persistent (isQS sys N) := by
  unfold isQS; infer_instance

/-- The `treat` callback does nothing (`NewQuorumSet`'s). -/
def treatOk (treat : GoFunc) : IProp netDistGF :=
  iprop(□ ∀ (l qid : w32) (q : Loc) (Φ : val → IProp netDistGF), Φ #() -∗
    WP (App (App (App (Val #treat) (Val #l)) (Val #qid)) (Val #q)) {{ Φ }})

instance treatOk_persistent (treat : GoFunc) : Persistent (treatOk treat) := by
  unfold treatOk; infer_instance

end defs

/-- What `subsets` adds to leader `l`'s list: the emitted sets that contain `l`. -/
def addL (L : Nat → List (List Nat)) (E : List (List Nat)) : Nat → List (List Nat) :=
  fun l => L l ++ E.filter (fun s => decide (l ∈ s))

/-- `ids` as `newQuorumSetAdvance` fills it. -/
def idsList (N : Nat) : List w32 := (List.range N).map w32n

end replica.quorum

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF]
variable [sem : go.Semantics] [replica.Assumptions] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]

open replica.quorum

/-- `Leader(ballot, N)`: `ballot % N` (Go's truncated remainder; for a non-negative ballot the
`Nat` remainder, `leader_val`). -/
abbrev replica.Leader.spec : Prop :=
  ∀ (b : w32) (n : w64),
  {{ (⌜0 < sint.Z n ∧ sint.Z n < 2 ^ 31⌝ : IProp netDistGF) }}
    (App (App (Val (@! replica.Leader)) (Val #b)) (Val #n))
  {{ RET #(BitVec.srem b (W32 (sint.Z n))); True }}

/-- `NextBallotOf(rid, old, N)`: `(old / N + 1) * N + rid` in int32 arithmetic (exact when it
fits: `nextBallot_val`). -/
abbrev replica.NextBallotOf.spec : Prop :=
  ∀ (rid old : w32) (n : w64),
  {{ (⌜0 < sint.Z n ∧ sint.Z n < 2 ^ 31⌝ : IProp netDistGF) }}
    (App (App (App (Val (@! replica.NextBallotOf)) (Val #rid)) (Val #old)) (Val #n))
  {{ RET #((BitVec.sdiv old (W32 (sint.Z n)) + 1) * W32 (sint.Z n) + rid); True }}

/-- `NewMajorityOf(N)`: `N / 2 + 1`. -/
abbrev replica.NewMajorityOf.spec : Prop :=
  ∀ (N : Nat),
  {{ (⌜N < 2 ^ 62⌝ : IProp netDistGF) }}
    (App (Val (@! replica.NewMajorityOf)) (Val #(W64 N)))
  {{ RET #(W64 (N / 2 + 1)); True }}

/-- `NewThreeQuartersOf(N)`: `3 N / 4 + 1`. -/
abbrev replica.NewThreeQuartersOf.spec : Prop :=
  ∀ (N : Nat),
  {{ (⌜N < 2 ^ 61⌝ : IProp netDistGF) }}
    (App (Val (@! replica.NewThreeQuartersOf)) (Val #(W64 N)))
  {{ RET #(W64 (3 * N / 4 + 1)); True }}

abbrev replica.Majority.Size.spec : Prop :=
  ∀ (m : w64),
  {{ (True : IProp netDistGF) }}
    (App (Val (m @!! replica.Majority.ty @!! go!"Size")) (Val #()))
  {{ RET #m; True }}

abbrev replica.Majority.Contains.spec : Prop :=
  ∀ (m : w64) (r : w32),
  {{ (True : IProp netDistGF) }}
    (App (Val (m @!! replica.Majority.ty @!! go!"Contains")) (Val #r))
  {{ RET #true; True }}

abbrev replica.ThreeQuarters.Size.spec : Prop :=
  ∀ (m : w64),
  {{ (True : IProp netDistGF) }}
    (App (Val (m @!! replica.ThreeQuarters.ty @!! go!"Size")) (Val #()))
  {{ RET #m; True }}

abbrev replica.ThreeQuarters.Contains.spec : Prop :=
  ∀ (m : w64) (r : w32),
  {{ (True : IProp netDistGF) }}
    (App (Val (m @!! replica.ThreeQuarters.ty @!! go!"Contains")) (Val #r))
  {{ RET #true; True }}

/-- `NewQuorum(size)`: an empty quorum. -/
abbrev replica.NewQuorum.spec : Prop :=
  ∀ (size : w64),
  {{ (True : IProp netDistGF) }}
    (App (Val (@! replica.NewQuorum)) (Val #size))
  {{ (q : Loc), RET #q; qOwn q (DFrac.own 1) [] }}

/-- `q.Size()`: the number of replicas. -/
abbrev replica.Quorum.Size.spec : Prop :=
  ∀ (q : Loc) (dq : DFrac) (s : List Nat),
  {{ qOwn q dq s ∗ ⌜s.Nodup ∧ ∀ x ∈ s, x < 2 ^ 31⌝ }}
    (App (Val (q @!! replica.Quorum.ty @!! go!"Size")) (Val #()))
  {{ RET #(W64 s.length); qOwn q dq s }}

/-- `q.Contains(r)`. -/
abbrev replica.Quorum.Contains.spec : Prop :=
  ∀ (q : Loc) (dq : DFrac) (s : List Nat) (r : w32),
  {{ qOwn q dq s }}
    (App (Val (q @!! replica.Quorum.ty @!! go!"Contains")) (Val #r))
  {{ RET #(decide (r ∈ s.map w32n)); qOwn q dq s }}

/-- `q.copy()`: a new quorum with the same replicas. -/
abbrev replica.Quorum.copy.spec : Prop :=
  ∀ (q : Loc) (dq : DFrac) (s : List Nat),
  {{ qOwn q dq s }}
    (App (Val (q @!! replica.Quorum.ty @!! go!"copy")) (Val #()))
  {{ (nq : Loc), RET #nq; qOwn q dq s ∗ qOwn nq (DFrac.own 1) s }}

/-- `NewQuorumsOfLeader()`: an empty list of quorums. -/
abbrev replica.NewQuorumsOfLeader.spec : Prop :=
  {{ (True : IProp netDistGF) }}
    (App (Val (@! replica.NewQuorumsOfLeader)) (Val #()))
  {{ (p : Loc), RET #p; lqsOwn p (DFrac.own 1) [] }}

/-- `subsets(ids, N, k, i, q, qs, treat)` (`N ≤ 7`, `q` the replicas chosen so far, below
`i`): every leader's list grows by the emitted sets containing it (`emitL N k i q`), `q` is
restored. -/
abbrev replica.subsets.spec : Prop :=
  ∀ (ids : GoSlice) (N : Nat) (k : w64) (i : Nat) (q : Loc) (cur : List Nat) (qs : Loc)
    (L : Nat → List (List Nat)) (treat : GoFunc),
  {{ ids ↦*□ idsList N ∗ qOwn q (DFrac.own 1) cur ∗ qsOwn qs N L (DFrac.own 1) ∗ treatOk treat ∗
      ⌜N ≤ 7 ∧ i ≤ N ∧ (∀ x ∈ cur, x < i) ∧ cur.Nodup ∧ -(i : Int) ≤ sint.Z k ∧ sint.Z k ≤ N ∧
        ∀ l, (L l).length + ((emitL N (sint.Z k) i cur).filter (fun s => decide (l ∈ s))).length
          < 2 ^ 31⌝ }}
    (App (App (App (App (App (App (App (Val (@! replica.subsets)) (Val #ids)) (Val #(W64 N)))
      (Val #k)) (Val #(W64 i))) (Val #q)) (Val #qs)) (Val #treat))
  {{ RET #(); qOwn q (DFrac.own 1) cur ∗ qsOwn qs N (addL L (emitL N (sint.Z k) i cur)) (DFrac.own 1) }}

/-- `newQuorumSetAdvance(N / 2 + 1, N, treat)` with a no-op `treat`. -/
abbrev replica.newQuorumSetAdvance.spec : Prop :=
  ∀ (N : Nat) (treat : GoFunc),
  {{ treatOk treat ∗ ⌜1 ≤ N ∧ N ≤ 7⌝ }}
    (App (App (App (Val (@! replica.newQuorumSetAdvance)) (Val #(W64 (N / 2 + 1)))) (Val #(W64 N)))
      (Val #treat))
  {{ (qs : Loc), RET #qs; qsIs qs N }}

/-- `NewQuorumSet(N / 2 + 1, N)`. -/
abbrev replica.NewQuorumSet.spec : Prop :=
  ∀ (N : Nat),
  {{ (⌜1 ≤ N ∧ N ≤ 7⌝ : IProp netDistGF) }}
    (App (App (Val (@! replica.NewQuorumSet)) (Val #(W64 (N / 2 + 1)))) (Val #(W64 N)))
  {{ (qs : Loc), RET #qs; qsIs qs N }}

/-- `qs.AQ(ballot)` for a non-negative ballot: its fast quorum (`aqOf`; persistent). -/
abbrev replica.QuorumSet.AQ.spec : Prop :=
  ∀ (qs : Loc) (N : Nat) (b : w32),
  {{ qsIs qs N ∗ ⌜0 ≤ sint.Z b⌝ }}
    (App (Val (qs @!! replica.QuorumSet.ty @!! go!"AQ")) (Val #b))
  {{ (q : Loc), RET #q; qOwn q DFrac.discard (aqOf N (sint.Z b).toNat) }}

/-- `NewQuorumsFromFile("", r)`: no quorum file. -/
abbrev replica.NewQuorumsFromFile.spec : Prop :=
  ∀ (r : Loc) (msg : GoString),
  {{ (errors.newVar replica.NO_QUORUM_FILE msg : IProp netDistGF) }}
    (App (App (Val (@! replica.NewQuorumsFromFile)) (Val #(go!""))) (Val #r))
  {{ (e : GoInterface), RET (PairV (PairV #slice.nil #slice.nil) #e);
      ⌜∃ x : Loc, e = interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x⌝ ∗
      globalAddr replica.NO_QUORUM_FILE ↦□ e }}

/-- `NewQuorumSystem(N / 2 + 1, r, "")` (`config.plain`'s `Quorum`): the quorum system of every
majority, no error. `r`'s `N` field (the only one read) is the configuration's `N`. -/
abbrev replica.NewQuorumSystem.spec : Prop :=
  ∀ (r : Loc) (dq : DFrac) (N : Nat) (msg : GoString),
  {{ (errors.newVar replica.NO_QUORUM_FILE msg : IProp netDistGF) ∗
      (structFieldRef replica.Replica go!"N" r) ↦{dq} (W64 (N : Int)) ∗ ⌜1 ≤ N ∧ N ≤ 7⌝ }}
    (App (App (App (Val (@! replica.NewQuorumSystem)) (Val #(W64 (N / 2 + 1)))) (Val #r))
      (Val #(go!"")))
  {{ (sys : Loc), RET (PairV #sys #interface.nil);
      (structFieldRef replica.Replica go!"N" r) ↦{dq} (W64 (N : Int)) ∗ isQS sys N }}

/-- `sys.BallotAt(i)`: no listed ballots, so `-1`. -/
abbrev replica.QuorumSystem.BallotAt.spec : Prop :=
  ∀ (sys : Loc) (N : Nat) (i : w64),
  {{ isQS sys N ∗ ⌜0 ≤ sint.Z i⌝ }}
    (App (Val (sys @!! go.GoType.PointerType replica.QuorumSystem.ty @!! go!"BallotAt")) (Val #i))
  {{ RET #(W32 (-1)); True }}

/-- `sys.NumAQ(l)` for a replica `l < N`: the number of its fast quorums. -/
abbrev replica.QuorumSystem.NumAQ.spec : Prop :=
  ∀ (sys : Loc) (N : Nat) (l : w32),
  {{ isQS sys N ∗ ⌜0 ≤ sint.Z l ∧ sint.Z l < N⌝ }}
    (App (Val (sys @!! go.GoType.PointerType replica.QuorumSystem.ty @!! go!"NumAQ")) (Val #l))
  {{ RET #(W64 (numAQ N (sint.Z l).toNat)); True }}

/-- `sys.AQ(ballot)` for a non-negative ballot. -/
abbrev replica.QuorumSystem.AQ.spec : Prop :=
  ∀ (sys : Loc) (N : Nat) (b : w32),
  {{ isQS sys N ∗ ⌜0 ≤ sint.Z b⌝ }}
    (App (Val (sys @!! go.GoType.PointerType replica.QuorumSystem.ty @!! go!"AQ")) (Val #b))
  {{ (q : Loc), RET #q; qOwn q DFrac.discard (aqOf N (sint.Z b).toNat) }}

/-- `sys.SameHigher(sameAs, higherThan)` for a non-negative `sameAs`: `sameAs + k L N` in
int32 arithmetic, `L` the number of fast quorums of `sameAs`'s leader, `k = higherThan / L`. -/
abbrev replica.QuorumSystem.SameHigher.spec : Prop :=
  ∀ (sys : Loc) (N : Nat) (sameAs higherThan : w32),
  {{ isQS sys N ∗ ⌜0 ≤ sint.Z sameAs⌝ }}
    (App (App (Val (sys @!! go.GoType.PointerType replica.QuorumSystem.ty @!! go!"SameHigher"))
      (Val #sameAs)) (Val #higherThan))
  {{ RET #(sameAs + BitVec.sdiv higherThan (W32 (numAQ N ((sint.Z sameAs).toNat % N))) *
        W32 (numAQ N ((sint.Z sameAs).toNat % N)) * W32 N); True }}

end specs

end Perennial.github_com.imdea_software.swiftpaxos

end
