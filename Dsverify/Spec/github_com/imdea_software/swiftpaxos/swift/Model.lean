/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/swift/Model.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
SwiftPaxos's protocol as a pure model (no Iris), the refinement target of the Go code
(`swift/recovery.go`, `swift/swift.go`, `swift/dpath.go`, `swift/key.go`, fork branch `verify`,
d9e184b, **plus F4's repair**, below), and its safety theorems, proved.

Files: `Model/Defs.lean` (the definitions: sequences, `lkDeps`, quorums, `recoverSync` piece by
piece, `PState`, `PInv`), `Model/Seq.lean`, `Model/Recover.lean`, `Model/Graph.lean`,
`Model/Safety.lean`, `Model/Protocol.lean` (the proof, in layers: lists and orders; what each rule
of the recovery keeps; the kept graph; one recovery keeps a safe command; from `PInv` to the
recovery's facts and the induction over ballots), `Model/Register.lean` (registering a command
keeps `PInv`).

Notation: `N` replicas (`Conf.n`), ballots `Nat`, `leaderOf N b = b mod N`, `AQ N b` the fast
quorum (a majority containing the leader: `AQ_majority`).

## The orders and the paths

Replica `r`'s sequence in ballot `b`, `loc r b`, is the ballot's `MSync` order (`base b`, empty for
ballot 0) followed by the proposals its run loop handled in `b` (`r.handled`). The leader's is the
ballot's order `ord b`; a command's dependencies are `lkDeps` of the sequence before it (S2: a put
after the last put and the gets since, a get after the last put). F2's fix: every hash log starts
empty in each ballot, a path hash commits to its path (start-marked), the leader numbers its
proposals in path order; so `path r b x = P` (`PInv.path_ok`): the leader's path is its commands
of `x`'s key in `b` up to `x` (`keyPrefix`), a follower's contains every command of the key it
handled in `b` before `x` (pending ones, and acknowledged ones, which are in the synced prefix,
the leader's path of the highest-numbered acknowledged command). Equal hashes are equal paths
(the hub-requested `checksum_path`), so the fast path's condition is path *equality*
(`fastChosen`).

## What is chosen

`x` is possibly chosen in `b` (`possiblyChosen`: a client may hold the leader's result
`resultIn (ordSeq N b) x`): `x ∈ ord b` and either a majority accepted it (`slowChosen`, the
leader counts) or every non-leader member of `AQ N b` pre-accepted it with the leader's
dependencies and the leader's path (`fastChosen`, N4's fix: the leader counted once), and
(D33) the leader executed `x` in `b` (`lexec`: a set closed under the leader's dependencies, each
in the base or pre-accepted by the leader). Only the leader's `MReply`, sent after `deliver`,
completes a client, and `deliver` needs the whole dependency closure delivered: a proposal the
leader handled but whose `proposeMsg` was dropped (P6) is never executed in `b`, nor is anything
depending on it (notes/recovery-h7-client.md). The leader's report may list such a proposal in
`START` (`repOk`'s seventh clause asks only that it lists every proposal).

## The recovery (`recoverSync`, rules 1 to 6, with 3b and F4's repair)

Rule 1 keeps the entries accepted or committed in `U` (the reports of the highest `cballot` `c`)
and the old leader's (class 0); rule 2 (R1), if the old leader did not report, the commands every
reporter of `R = U ∩ AQ N c` pre-accepted with equal dependencies, with `R[0]`'s; rule 3 the
closure; rule 3b (F3) puts a class-≠0 command after every conflicting kept command `R[0]` reported
before it (reports list the base, then `r.handled`'s order); rule 4 puts it after the conflicting
class-0 ones; rule 5 one order (`recOrder`); rule 6 the `lkAlong` dependencies.

**F4 (found here; notes/prove-model.md, issues/f4-recovery-closure-cycle.md)**: the code's rule 3
takes a dependency's entry of the highest phase among `U` (first by replica id on ties): another
reporter's entry (a `START` entry with its own `proposeDep`, or a pre-acceptance in another order)
can order a dependency of a fast-chosen get after the get: a cycle, broken by `recOrder` at the
smallest id, and the get re-executes with another result (N = 3 with two commands; N = 5 with
three; Go test `TestIssueF4_FastGetResultKept`). The repair (`recBest`): when rule 2 applies,
`R[0]`'s own entry first. The model has the repair; the fork must take it (a premise of the
refinement, marked).

## The safety argument (`Model/Safety.lean`, `Model/Protocol.lean`)

Let `M = recoverSync N reps` be the `MSync` of `b'`, `c` the highest `cballot`, `x` possibly
chosen in `b < b'`. A reporter of the majority is in `x`'s quorum, acted in `b`, so its
`cballot ≥ b` (`repOk`: nothing in a ballot between its `cballot` and `b'`): `b ≤ c < b'`.
* `c > b`: by induction `x ∈ base c` with the facts; every reporter of `U` reports the base in
  `COMMIT`: `x` is class 0.
* `c = b`: slow, an acceptor (or the leader) reported `x` accepted (class 0); fast, the leader
  reported (class 0), or `R` is not empty and every member pre-accepted `x` with the leader's
  dependencies: kept by rule 2 (or class 0).
**D33**: when the old leader reported, a class-0 entry may depend on its dropped proposal, which
the closure keeps with any reporter's entry (`OthEntry`), so the kept graph may have cycles.
Acyclicity is claimed only below the commands the old leader executed (`Ctx.Gd`, closed under
dependencies, `Ctx.Ac`): `recOrder` places such a command after what it reaches and before what
reaches it (`order_root`, from `recOrder_loc`); nothing is claimed of the rest of the kept
graph. A conflicting kept command after an executed `x` in the leader's order reaches `x`
(`chain_in`: the leader's chain while class 0, rule 4 at the first other command). Without the
old leader's report every class-0 command is `Gd`, and the argument below is unchanged.
The kept graph below `Gd` commands is acyclic: class-0 entries have the leader's dependencies (N2: an acceptor
accepted the dependencies first; a follower commits only what it accepted), all class 0; with
F4's repair every other entry is `R[0]`'s, its dependencies earlier in `R[0]`'s report; rules 3b
and 4 add edges to earlier `R[0]` positions or to class-0 commands. The potential (`Ctx.phi`:
the leader's index for class 0, after them `R[0]`'s position) decreases along every edge out of
an `Ac` command, so `recOrder` places an `Ac` command after what it reaches (`order_root`). For a safe `x` (`Ctx.Safe`):
(S2) every conflicting kept command reaches `x` or is reached from it (the leader's dependency
chains among class-0 commands; rules 3b and 4 otherwise); (S3) whatever `x` reaches was before
`x` in the leader's order (F2's fact: `R[0]` handled before `x` only commands of the leader's
path of `x`; a class-0 command after `x` conflicting with an earlier one would make it class 0);
(S4) a get's last put `p` (the leader's) is reached, and every other put it reaches is reached
from `p` (rule 3b on `R[0]`'s order, where `p` is the last put before `x`, as its dependencies
are the leader's). So in the `MSync` order (which keeps every conflicting pair's order of
`recOrder`'s, `syncOrder_lkAlong`) `x` is present, its last put is `p`, and a conflicting
command before it was before it in the leader's order: `ballot_safety`. Checked first by
`etc/modelcheck` (flags `fix4`, `start` for `START` entries, `b3` for another fast quorum, `cyc`
for acyclicity; oracle `l_*` is this statement): no failure, no cycle (notes/prove-model.md).

## The linearization (where each operation takes effect): **no fixed point exists** (L1)

`Inv.lean` linearizes with an append-only `G` and each command's atomic update committed when
it is appended (TaDa), so a command's place in `G` is fixed when it is first appended, at the
latest when a client may accept it. SwiftPaxos does not allow that (notes/prove-model.md, L1;
replay: `etc/modelcheck/lin.py`): N = 3, AQ = {0, 1}; the leader handles put p1, get x, put q,
put y; replica 1 handles x, (the leader's ack of x,) p1, (its ack,) q, y: y's path and
dependencies are the leader's, y is chosen on the fast path, its client may accept now. In one
future replica 2 accepts p1 and x (x slow-chosen, result V1: x after p1); in another the
recovery by {1, 2} orders x, p1, q, y (x not chosen, re-executed with result ''): x before p1.
Both histories are linearizable, but in both p1 and q must precede y in `G` (a later get reads
y's value) and x must precede y (it reads p1's value or nothing), so `G` must fix the order of
x and p1 when y is appended, before the future decides it. Hence the TaDa laws `accept_fast`,
`accept_slow`, `client_collect` (with `doneRes`, `slotRes`) cannot be established by any body of
`sp.inv` that the replicas' steps keep (hub request L1: a prophecy of the final order, or a
history-based statement at the end of the run, or a protocol change). What the model proves
instead, and what any of these needs: a possibly chosen command keeps its leader's result and
its real-time order in every later `MSync` (`ballot_safety`), so its leader results agree
(`result_agree`), and every replica executing a later `MSync` executes it with that result
(`sync_result`). `PState.G` stays as a field (the ghost list of `Inv.lean`), registered commands
only (`PInv.G_ok`).

**D7 (prophecy of each get's result) does not close L1 by itself** (notes/prophecy-client.md;
`etc/modelcheck/lin2.py`): an undecided *put* p1 on the path of a fast-chosen put y can end
before y (a replica accepted p1) or after it (the recovery does not know p1, it is proposed
again), and `G` must place p1 when y is appended; only later gets' results reveal which, and a
put has no result to prophesy. A node-wide prophecy of all observations, with `G` a prefix of
the observed history's linearization, would need a forward-simulation invariant about the
protocol's future that `PInv` does not give; C12 is therefore not applied.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Model.Protocol
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Model.Register
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Model.Steps

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

namespace sp

namespace PState

variable {S : PState} {N : Nat} {fr : Bool}

/-- **Ballot safety**, the client-level form (proved): a command possibly chosen in `b` is in
the `MSync` of every later ballot, with its leader's result, and every command of the `MSync`
before it that conflicts with it was before it in the leader's order (so after it in real time
only if not chosen when it was). The old form (the puts before a decided command kept) is false
of any recovery from a majority's reports (notes/recovery-fix.md, "Unresolved"). -/
theorem ballot_safety (hI : S.PInv N fr) {b b' : Nat} {x : CmdId} (hb : b < b')
    (hs : S.sync b' ≠ none) (hx : S.possiblyChosen N b x) :
    x ∈ S.base b' ∧ resultIn (S.seqOf (S.base b')) x = resultIn (S.ordSeq N b) x ∧
    ∀ y, S.conflicts y x → precedes (S.base b') y x → precedes (S.ord N b) y x :=
  let h := ballot_safety_proof hI b' b x hb hs hx; ⟨h.1, h.2.1, h.2.2.1⟩

/-- **Ballot safety, the last put** (S4 at the level of identities; L1): a possibly chosen get's
last put in its leader's order is its last put in every later `MSync`. -/
theorem ballot_safety_lastPut (hI : S.PInv N fr) {b b' : Nat} {x : CmdId} (hb : b < b')
    (hs : S.sync b' ≠ none) (hx : S.possiblyChosen N b x) {cx : Cmd} {p : Option CmdId}
    (hcx : S.cmds x = some cx) (hg : cx.isGet = true) (hp : S.LastPut (S.ord N b) x cx.key p) :
    S.LastPut (S.base b') x cx.key p :=
  (ballot_safety_proof hI b' b x hb hs hx).2.2.2 cx p hcx hg hp

/-- A ballot whose leader ordered something has its `MSync` (ballot 0 excepted). -/
theorem sync_of_ord (hI : S.PInv N fr) {b : Nat} {x : CmdId} (hx : x ∈ S.ord N b) (hb : 0 < b) :
    S.sync b ≠ none := by
  have hne : S.ord N b ≠ [] := fun h => by rw [h] at hx; simp at hx
  exact (((hI.loc_ok _ _).2.2 hne).2.2 hb).1

/-- **Result agreement**: the leaders' results of a command possibly chosen in two ballots are
equal (so every client accepting it gets the same result). -/
theorem result_agree (hI : S.PInv N fr) {b1 b2 : Nat} {x : CmdId} (h1 : S.possiblyChosen N b1 x)
    (h2 : S.possiblyChosen N b2 x) : resultIn (S.ordSeq N b1) x = resultIn (S.ordSeq N b2) x := by
  have key : ∀ b1 b2, b1 < b2 → S.possiblyChosen N b1 x → S.possiblyChosen N b2 x →
      resultIn (S.ordSeq N b1) x = resultIn (S.ordSeq N b2) x := by
    intro b1 b2 hlt h1 h2
    obtain ⟨g1, g2, -⟩ := ballot_safety hI hlt (sync_of_ord hI h2.1 (by omega)) h1
    rw [← g2]
    obtain ⟨T, hT⟩ := base_prefix_ord hI b2
    exact (resultIn_prefix_of hI _ _ ⟨T, hT⟩ (hI.loc_ok _ _).1 (hI.loc_ok _ _).2.1 x g1).symm
  rcases Nat.lt_trichotomy b1 b2 with h | rfl | h
  · exact key _ _ h h1 h2
  · rfl
  · exact (key _ _ h h2 h1).symm

/-- **Executions agree**: every replica that takes a later `MSync` executes a possibly chosen
command, in the `MSync`'s order, with its leader's result (the replicas' executions of the
command, `Command.Execute` along `syncOrder`, are the result its client got). -/
theorem sync_result (hI : S.PInv N fr) {b b' : Nat} {x : CmdId} (hb : b < b')
    (hs : S.sync b' ≠ none) (hx : S.possiblyChosen N b x) :
    x ∈ S.base b' ∧ resultIn (S.seqOf (S.base b')) x = resultIn (S.ordSeq N b) x :=
  let h := ballot_safety hI hb hs hx; ⟨h.1, h.2.1⟩

/-- **Real time**: a command after a possibly chosen `x` in the leader's order (in particular
one invoked after `x`'s client returned) never precedes `x` in a later `MSync`, if they
conflict. -/
theorem chosen_realtime (hI : S.PInv N fr) {b b' : Nat} {x y : CmdId} (hb : b < b')
    (hs : S.sync b' ≠ none) (hx : S.possiblyChosen N b x) (hy : S.conflicts y x)
    (hyx : ¬ precedes (S.ord N b) y x) : ¬ precedes (S.base b') y x :=
  fun h => hyx ((ballot_safety hI hb hs hx).2.2 y hy h)

end PState

end sp

end Perennial.github_com.imdea_software.swiftpaxos

end
