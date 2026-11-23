/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/swift/Model/Defs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
SwiftPaxos's protocol as a pure model: the definitions (sequences, dependencies, results,
quorums, the recovery `recoverSync` piece by piece as `recovery.go` computes it, the `MSync`
order, the protocol state `PState`, its invariant `PInv`). The design, the safety argument and the
theorems: `Spec/swift/Model.lean`.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Wire

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

namespace sp

/-- `f` applied `n` times. -/
def iter {α : Type} (f : α → α) : Nat → α → α
  | 0, a => a
  | n + 1, a => iter f n (f a)

/-! ## Sequences, dependencies, results -/

/-- A sequence of commands (oldest first). -/
abbrev Seq := List (CmdId × Cmd)

/-- The commands of `s` before `x` (all of `s` if `x` is not in it). -/
def before (s : Seq) (x : CmdId) : Seq := s.takeWhile (fun p => p.1 != x)

/-- `x`'s command in `s`. -/
def cmdIn (s : Seq) (x : CmdId) : Option Cmd := (s.find? (fun p => p.1 == x)).map Prod.snd

/-- `lightKeyInfo`'s conflicting commands for `c` after the sequence `s` (`getConflictCmds`):
for a get, the last put of its key; for a put, the last put and the gets since. -/
def lkDeps (s : Seq) (c : Cmd) : List CmdId :=
  let ks := (s.filter (fun p => p.2.key == c.key)).reverse
  let lastPut := (ks.find? (fun p => p.2.isPut)).toList.map Prod.fst
  let since := ((ks.takeWhile (fun p => !p.2.isPut)).map Prod.fst).reverse
  if c.isPut then lastPut ++ since else lastPut

/-- The dependencies of `x` in the sequence `s` (computed when `x` was appended). -/
def depsIn (s : Seq) (x : CmdId) : List CmdId :=
  match cmdIn s x with
  | some c => lkDeps (before s x) c
  | none => []

/-- The puts of `x`'s key before `x` in `s`, in order. -/
def putsBefore (s : Seq) (x : CmdId) : Seq :=
  match cmdIn s x with
  | some c => (before s x).filter (fun p => p.2.key == c.key && p.2.isPut)
  | none => []

/-- The result of `x` executed after the commands before it in `s` (`Command.Execute`): a get's
is the last put's value of its key (empty if none: `state.NIL()`), a put's is empty. -/
def resultIn (s : Seq) (x : CmdId) : List w8 :=
  match cmdIn s x with
  | some c => if c.isGet then (((putsBefore s x).getLast?).map (fun p => p.2.val)).getD [] else []
  | none => []

/-- The dependency closure of `x` in `s` (`x` included): the commands reachable through
`depsIn s` (at most `s.length` rounds). -/
def depClosure (s : Seq) (x : CmdId) : List CmdId :=
  let step := fun (acc : List CmdId) => acc ++ (acc.flatMap (depsIn s)).filter (fun y => y ∉ acc)
  iter (fun acc => (step acc).eraseDups) s.length [x]

/-! ## Quorums and ballots -/

/-- `replica.Leader`: ballot `b`'s leader. -/
def leaderOf (N b : Nat) : Nat := b % N

/-- The `k`-element sublists of `l`, in the lexicographic order of the chosen indices
(`replica.subsets`'s enumeration). -/
def combos : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | k + 1, a :: l => (combos k l).map (a :: ·) ++ combos (k + 1) l

/-- `qs.AQ(b)` (no quorum file): the fast quorum of ballot `b`, the
`(b / N) mod (number of them)`-th majority (`N / 2 + 1` replicas) containing `b`'s leader. -/
def AQ (N b : Nat) : List Nat :=
  let lqs := (combos (N / 2 + 1) (List.range N)).filter (fun q => leaderOf N b ∈ q)
  lqs.getD ((b / N) % lqs.length) []

/-- `Q` is a set of a majority of the replicas. -/
def isMajority (N : Nat) (Q : List Nat) : Prop :=
  Q.Nodup ∧ (∀ r ∈ Q, r < N) ∧ N < 2 * Q.length

/-! ## Recovery (`recovery.go`) -/

/-- A recovery report (`MNewLeaderAckN`): the reporter's `cballot` and its entries. -/
structure Report where
  cbal : Nat
  entries : List RepEntry
  deriving DecidableEq

instance Report.countable : Pos.Countable Report :=
  .ofInjective (fun r => Pos.Countable.encode (r.cbal, r.entries))
    (by rintro ⟨a, b⟩ ⟨a', b'⟩ h; have h := Pos.encode_inj h; simp_all)

/-- An `MSync`'s contents: every command it keeps, with its command and dependencies (all in
phase `COMMIT`), in the new leader's order. -/
abbrev SyncMsg := List (CmdId × Cmd × List CmdId)

/-- `recEntry`: a kept command's phase, command, dependencies and class (0: accepted or
committed, or the old leader's; 1: kept by R1; 2: a dependency of a kept command). -/
structure RecEntry where
  phase : Nat
  cmd : Cmd
  dep : List CmdId
  cls : Nat

/-- The kept commands, as an association list (`kept`). -/
abbrev Kept := List (CmdId × RecEntry)

def Kept.get (k : Kept) (x : CmdId) : Option RecEntry := (k.find? (·.1 == x)).map Prod.snd
def Kept.set (k : Kept) (x : CmdId) (e : RecEntry) : Kept :=
  if (k.find? (·.1 == x)).isSome then k.map (fun p => if p.1 == x then (x, e) else p)
  else k ++ [(x, e)]

/-- `sortedIds`: sorted by `cmdIdLess`. -/
def sortIds (l : List CmdId) : List CmdId := l.mergeSort (fun a b => !(CmdId.lt b a))

/-- `recReaches(kept, from, to)`: `to` is a dependency, through kept commands, of `from`. -/
def recReaches (k : Kept) (src dst : CmdId) : Bool :=
  let step := fun (seen : List CmdId) =>
    (seen ++ (seen.flatMap (fun y => ((k.get y).map RecEntry.dep).getD []))).eraseDups
  dst ∈ (iter step (k.length + 1) [src]).flatMap (fun y => ((k.get y).map RecEntry.dep).getD [])

/-- `recOrder(kept, ids)`: repeatedly the first of `ids` not placed whose kept dependencies are
placed, or else (a cycle) the first not placed. -/
def recOrder (k : Kept) (ids : List CmdId) : List CmdId :=
  iter (fun placed =>
    let rest := ids.filter (· ∉ placed)
    let ready := rest.find? (fun c => ((k.get c).map RecEntry.dep).getD [] |>.all
      (fun d => (k.get d).isNone || d ∈ placed))
    match ready, rest.head? with
    | some c, _ => placed ++ [c]
    | none, some c => placed ++ [c]
    | none, none => placed) ids.length []

/-- Dependencies equal as multisets (`Dep.Equals`). -/
def depEq (a b : List CmdId) : Bool := a.isPerm b

/-- `lightKeyInfo` along an order: each command's dependencies (`recoveredSync`'s step 6 and
`handleSync`'s rebuilding of the keys). -/
def lkAlong (cs : List (CmdId × Cmd)) : List (CmdId × Cmd × List CmdId) :=
  (cs.foldl (fun (acc : Seq × List (CmdId × Cmd × List CmdId)) p =>
    (acc.1 ++ [p], acc.2 ++ [(p.1, p.2, lkDeps acc.1 p.2)])) ([], [])).2

/-! ### `recoveredSync`, piece by piece (each a step of the Go function, in its order) -/

/-- The reports sorted by replica (`sort.Slice(acks, ... Replica <)`). -/
def recAcks (reps : List (Nat × Report)) : List (Nat × Report) :=
  reps.mergeSort (fun a b => a.1 ≤ b.1)

/-- The highest `cballot` of the reports (`maxCbal`; the code starts from -1, every `cballot` is
non-negative and a majority reports). -/
def recMaxC (acks : List (Nat × Report)) : Nat := (acks.map (·.2.cbal)).foldl max 0

/-- `U`: the reports of the highest `cballot`. -/
def recU (acks : List (Nat × Report)) : List (Nat × Report) :=
  acks.filter (·.2.cbal == recMaxC acks)

/-- Rule 1's test: an entry accepted or committed, or the old leader's pre-accepted one. -/
def okPhase (oldL : Nat) (a : Nat × Report) (e : RepEntry) : Bool :=
  e.phase.toNat == 2 || e.phase.toNat == 3 || (a.1 == oldL && e.phase.toNat == 1)

/-- Rule 1: the commands accepted or committed in `U`, and the old leader's own proposals
(class 0; a `COMMIT` entry replaces an earlier non-`COMMIT` one). -/
def rule1 (oldL : Nat) (U : List (Nat × Report)) : Kept :=
  U.foldl (fun k a => a.2.entries.foldl (fun k e =>
      if !okPhase oldL a e then k else
      match k.get e.id with
      | some old => if old.phase != 3 && e.phase.toNat == 3 then k.set e.id ⟨3, e.cmd, e.dep, 0⟩
          else k
      | none => k.set e.id ⟨e.phase.toNat, e.cmd, e.dep, 0⟩) k) []

/-- Rule 2 (R1): if the old leader did not report, a command `R[0]` pre-accepted that every
reporter of `R` pre-accepted with the same dependencies (class 1, `R[0]`'s dependencies). -/
def rule2 (k1 : Kept) (leaderInU : Bool) (R : List (Nat × Report)) : Kept :=
  if leaderInU then k1 else match R with
    | [] => k1
    | r0 :: rs => r0.2.entries.foldl (fun k e =>
        if e.phase.toNat != 1 || (k.get e.id).isSome then k
        else if rs.all (fun a => a.2.entries.any (fun e' =>
            e'.id == e.id && e'.phase.toNat == 1 && depEq e.dep e'.dep))
        then k.set e.id ⟨2, e.cmd, e.dep, 1⟩ else k) k1

/-- The highest-phase entry of `d` among the reports `l` (the first of them on ties). -/
def recPick (l : List (Nat × Report)) (d : CmdId) : Option RecEntry :=
  l.foldl (fun (b : Option RecEntry) a =>
    a.2.entries.foldl (fun b e => if e.id != d then b else match b with
      | none => some ⟨e.phase.toNat, e.cmd, e.dep, 2⟩
      | some b0 => if e.phase.toNat > b0.phase then some ⟨e.phase.toNat, e.cmd, e.dep, 2⟩
          else some b0) b) none

/-- Rule 3's `best(d)` with F4's repair (notes/prove-model.md, F4; **not yet in the fork**,
which takes the highest phase first): when rule 2 applies, `R[0]`'s own entry of `d`; else the
highest-phase entry in `U`, then in all the reports. -/
def recBest (leaderInU : Bool) (R U acks : List (Nat × Report)) (d : CmdId) :
    Option RecEntry :=
  match (if leaderInU then none else match R with
      | [] => none
      | r0 :: _ => r0.2.entries.find? (·.id == d)) with
  | some e => some ⟨e.phase.toNat, e.cmd, e.dep, 2⟩
  | none => match recPick U d with
    | some b => some b
    | none => recPick acks d

/-- Rule 3, one dependency `d` of `c`: kept (with `best`, pushed on the work list) and listed
if kept, dropped if no one reports it. -/
def closeDep (best : CmdId → Option RecEntry) (c : CmdId) (acc : Kept × List CmdId × List CmdId)
    (d : CmdId) : Kept × List CmdId × List CmdId :=
  if d == c then acc
  else if (acc.1.get d).isSome then (acc.1, acc.2.1, acc.2.2 ++ [d])
  else match best d with
    | none => acc
    | some bd => (acc.1.set d bd, acc.2.1 ++ [d], acc.2.2 ++ [d])

/-- One step of rule 3's work list: the first command's dependencies are kept (with `best`),
pushed on the list, and its dependency list keeps only the kept ones. -/
def closeStep (best : CmdId → Option RecEntry) (st : Kept × List CmdId) : Kept × List CmdId :=
  match st.2 with
  | [] => st
  | c :: work =>
    match st.1.get c with
    | none => (st.1, work)
    | some e =>
      let r := e.dep.foldl (closeDep best c) (st.1, work, [])
      (r.1.set c { e with dep := r.2.2 }, r.2.1)

/-- Rule 3: the closure, from the work list of the kept commands (sorted); `fuel` bounds the
code's loop (enough: `closure_done`). -/
def closure (best : CmdId → Option RecEntry) (fuel : Nat) (k2 : Kept) : Kept :=
  (iter (closeStep best) fuel (k2, sortIds (k2.map Prod.fst))).1

/-- `R[0]`'s position of a command in its report (the first, `pos`). -/
def recPos (r0 : Nat × Report) (c : CmdId) : Option Nat := r0.2.entries.findIdx? (·.id == c)

/-- Rule 3b, the pair `(c, w)`: `c` after `w` if `R[0]` reported `w` no later than `c`, they
conflict, and neither `w` is already a dependency of `c` nor `c` reachable from `w`. -/
def rule3bPair (r0 : Nat × Report) (c : CmdId) (pc : Nat) (k : Kept) (w : CmdId) : Kept :=
  match k.get w, k.get c, recPos r0 w with
  | some ew, some ec', some pw =>
    if w == c || decide (pw > pc) || !(Cmd.conflict ew.cmd ec'.cmd) then k
    else if ec'.dep.contains w || recReaches k w c then k
    else k.set c { ec' with dep := ec'.dep ++ [w] }
  | _, _, _ => k

/-- Rule 3b, the command `c` (kept by rule 2 or the closure, reported by `R[0]`) against every
kept `w`. -/
def rule3bCmd (r0 : Nat × Report) (ids : List CmdId) (k : Kept) (c : CmdId) : Kept :=
  match k.get c, recPos r0 c with
  | some ec, some pc => if ec.cls == 0 then k else ids.foldl (rule3bPair r0 c pc) k
  | _, _ => k

/-- Rule 3b (F3): a command kept by rule 2 or the closure comes after every conflicting kept
command `R[0]` handled before it (its report's order), unless one already reaches the other. -/
def rule3b (leaderInU : Bool) (R : List (Nat × Report)) (k3 : Kept) : Kept :=
  if leaderInU then k3 else match R with
    | [] => k3
    | r0 :: _ =>
      let ids := sortIds (k3.map Prod.fst)
      ids.foldl (rule3bCmd r0 ids) k3

/-- Rule 4, the pair `(c, a)`: `c` after the conflicting class-0 `a` if neither reaches the
other. -/
def rule4Pair (c : CmdId) (k : Kept) (a : CmdId) : Kept :=
  match k.get a, k.get c with
  | some ea, some ec' =>
    if ea.cls != 0 || !(Cmd.conflict ea.cmd ec'.cmd) then k
    else if !(recReaches k c a) && !(recReaches k a c) then
      k.set c { ec' with dep := ec'.dep ++ [a] }
    else k
  | _, _ => k

/-- Rule 4, the command `c` (if kept by rule 2 or the closure) against every kept `a`. -/
def rule4Cmd (ids : List CmdId) (k : Kept) (c : CmdId) : Kept :=
  match k.get c with
  | none => k
  | some ec => if ec.cls == 0 then k else ids.foldl (rule4Pair c) k

/-- Rule 4: a command kept by rule 2 or the closure after every conflicting class-0 one that
neither reaches it nor is reached from it. -/
def rule4 (ids : List CmdId) (k3 : Kept) : Kept :=
  ids.foldl (rule4Cmd ids) k3

/-- `recoveredSync`: the `MSync` the new leader of ballot `b'` computes from the reports
`reps` (replica id, report) of a majority (`recovery.go`, rules 1 to 6, with 3b and F4's
repair of rule 3). -/
def recoverSync (N : Nat) (reps : List (Nat × Report)) : SyncMsg :=
  let acks := recAcks reps
  let U := recU acks
  let oldL := leaderOf N (recMaxC acks)
  let aq := AQ N (recMaxC acks)
  let leaderInU := U.any (·.1 == oldL)
  let R := U.filter (fun a => a.1 ∈ aq)
  let k1 := rule1 oldL U
  let k2 := rule2 k1 leaderInU R
  let fuel := (reps.flatMap (·.2.entries)).length + k2.length + 1
  let k3 := closure (recBest leaderInU R U acks) fuel k2
  let k3b := rule3b leaderInU R k3
  let ids := sortIds (k3b.map Prod.fst)
  let k4 := rule4 ids k3b
  -- 5. one order; 6. the dependencies sent, `lightKeyInfo` along it
  let order := recOrder k4 ids
  lkAlong (order.filterMap (fun c => (k4.get c).map (fun e => (c, e.cmd))))

/-- `syncOrder`: the order in which a replica taking an `MSync` executes its commands (and
rebuilds its keys): `recOrder` of its dependencies over its sorted ids. -/
def syncOrder (M : SyncMsg) : List CmdId :=
  let k : Kept := M.map (fun p => (p.1, ⟨3, p.2.1, p.2.2, 0⟩))
  recOrder k (sortIds (M.map Prod.fst))

/-- The sequence of an `MSync`: its commands in `syncOrder`. -/
def syncSeq (M : SyncMsg) : Seq :=
  (syncOrder M).filterMap (fun x => (M.find? (·.1 == x)).map (fun p => (x, p.2.1)))

/-! ## The protocol state -/

/-- A replica's protocol state: its ballot, the ballot of the last `MSync` it took (`cballot`),
and whether it is in normal operation (not recovering). -/
structure RState where
  ballot : Nat
  cballot : Nat
  normal : Bool
  /-- the replica's own rows of the protocol state (MR4: its half of `nodeSt` is exactly its
  part of `PState`, `PInv.rows_ok`), as finite lists, newest first: its sequences by ballot -/
  locR : List (Nat × List CmdId)
  /-- its acceptances `(b, x)` -/
  accR : List (Nat × CmdId)
  /-- its pre-acceptances `((b, x), D)` -/
  preR : List ((Nat × CmdId) × List CmdId)
  /-- its paths `((b, x), P)` -/
  pathR : List ((Nat × CmdId) × List CmdId)
  /-- its commits `(b, x)` -/
  comR : List (Nat × CmdId)
  /-- its reports `(b', R)` -/
  repR : List (Nat × Report)
  deriving DecidableEq

instance RState.countable : Pos.Countable RState :=
  .ofInjective (fun s => Pos.Countable.encode
      (s.ballot, s.cballot, s.normal, s.locR, s.accR, s.preR, s.pathR, s.comR, s.repR))
    (by rintro ⟨a, b, c, d, e, f, g, h, i⟩ ⟨a', b', c', d', e', f', g', h', i'⟩ hh
        have hh := Pos.encode_inj hh; simp_all)

/-- The initial state: ballot 0, normal, nothing done. -/
def RState.init : RState := ⟨0, 0, true, [], [], [], [], [], []⟩

/-- The replica's sequence in ballot `b` (its newest row for `b`). -/
def RState.locAt (s : RState) (b : Nat) : List CmdId :=
  ((s.locR.find? (·.1 == b)).map Prod.snd).getD []

/-- Its pre-acceptance of `x` in `b`. -/
def RState.preAt (s : RState) (b : Nat) (x : CmdId) : Option (List CmdId) :=
  (s.preR.find? (·.1 == (b, x))).map Prod.snd

/-- Its path of `x` in `b`. -/
def RState.pathAt (s : RState) (b : Nat) (x : CmdId) : Option (List CmdId) :=
  (s.pathR.find? (·.1 == (b, x))).map Prod.snd

/-- Its report for `b`. -/
def RState.repAt (s : RState) (b : Nat) : Option Report :=
  (s.repR.find? (·.1 == b)).map Prod.snd

/-- The protocol state the ghost state records (`Inv.lean`): every function is the content of a
ghost map whose elements are persistent facts (but `rs`, each replica's own state). -/
structure PState where
  /-- the registered commands (each sent by its client: `cmdIs`) -/
  cmds : CmdId → Option Cmd
  /-- replica `r`'s sequence in ballot `b` (the `MSync`'s order, then the proposals it handled,
  in its run loop's order: `r.handled`) -/
  loc : Nat → Nat → List CmdId
  /-- ballot `b`'s `MSync` (`b > 0`), once its leader computed it -/
  sync : Nat → Option SyncMsg
  /-- each replica's state, by replica id -/
  rs : Nat → RState
  /-- `acc r b x`: replica `r` accepted `x` in `b`, with the leader's dependencies (phase
  `ACCEPT`, or `COMMIT` from an `MSync`) -/
  acc : Nat → Nat → CmdId → Prop
  /-- `pre r b x = some D`: `r` pre-accepted `x` in `b` with its dependencies `D` -/
  pre : Nat → Nat → CmdId → Option (List CmdId)
  /-- `path r b x = some P`: the dependency path `r` sent with its pre-acceptance of `x` in `b`
  (for `x`'s key; see the header) -/
  path : Nat → Nat → CmdId → Option (List CmdId)
  /-- `com r b x`: `r` committed (and so may execute) `x` in `b` -/
  com : Nat → Nat → CmdId → Prop
  /-- `rep r b = some R`: `r`'s recovery report for ballot `b` -/
  rep : Nat → Nat → Option Report
  /-- the linearization order's ghost list (`Inv.lean`'s `G`; see the header, "The
  linearization", on why no invariant of this model relates it to the orders) -/
  G : Seq

/-- `y` comes before `x` in `l` (`x` need not be in `l`: then `y ∈ l`). -/
def precedes (l : List CmdId) (y x : CmdId) : Prop := y ∈ l.takeWhile (· != x)

namespace PState
variable (S : PState)

/-- The commands of a list of ids, with their registered commands. -/
def seqOf (l : List CmdId) : Seq := l.filterMap (fun x => (S.cmds x).map (x, ·))

/-- Ballot `b`'s leader's order. -/
def ord (N b : Nat) : List CmdId := S.loc (leaderOf N b) b

/-- Ballot `b`'s leader's sequence. -/
def ordSeq (N b : Nat) : Seq := S.seqOf (S.ord N b)

/-- Ballot `b`'s base: its `MSync`'s order (`[]` for ballot 0 or before the `MSync`). -/
def base (b : Nat) : List CmdId := ((S.sync b).map syncOrder).getD []

/-- Two registered commands conflict. -/
def conflicts (y x : CmdId) : Prop :=
  ∃ cy cx, S.cmds y = some cy ∧ S.cmds x = some cx ∧ Cmd.conflict cy cx = true

/-- The ids of `x`'s key among the commands replica `r` handled in `b` (after the base) up to
`x`, `x` last: what its hash log appended in `b` up to `x` (F2's fix: the hash logs start empty
in every ballot). -/
def keyPrefix (r b : Nat) (x : CmdId) : List CmdId :=
  match S.cmds x with
  | some c => ((((S.seqOf ((S.loc r b).drop (S.base b).length)).takeWhile (·.1 != x)).filter
      (·.2.key == c.key)).map Prod.fst) ++ [x]
  | none => [x]

/-- The old relation of two paths with equal hashes (one a suffix of the other), what
`Inv.lean`'s `checksum_path` gives for its chained hashes from the zero hash. Since F2's fix the
code's path hashes are start-marked and equal hashes are equal paths (hub request: `pathHashes`
as the code computes them); `possiblyChosen` uses equality. -/
def pathRel (P Q : List CmdId) : Prop := P <:+ Q ∨ Q <:+ P

/-- The fast path's condition (with N4's fix, the client counts the leader once): the leader
sent its path `PL` for `x`, and every other member of `AQ N b` pre-accepted `x` with the
leader's dependencies and the same path (equal path hashes, the hub-requested
`checksum_path`). -/
def fastChosen (N b : Nat) (x : CmdId) : Prop :=
  ∃ PL, S.path (leaderOf N b) b x = some PL ∧ ∀ r ∈ AQ N b, r ≠ leaderOf N b →
    ∃ D, S.pre r b x = some D ∧ D.Perm (depsIn (S.ordSeq N b) x) ∧ S.path r b x = some PL

/-- The slow path's condition: a majority of acceptors (the leader among them: its proposals
are its acceptances). -/
def slowChosen (N b : Nat) (x : CmdId) : Prop :=
  ∃ Q, isMajority N Q ∧ ∀ r ∈ Q, r = leaderOf N b ∨ S.acc r b x

/-- D33: `b`'s leader executed (`deliver`ed) `x` in `b`, hence its whole dependency closure:
some set `E ∋ x`, closed under the leader's pre-acceptance dependencies, each of whose commands
is in `b`'s base (`handleSync` executed it) or pre-accepted by the leader (its `handlePropose`
ran; the leader's dependencies are its pre-acceptance's, `pre_ok`). A proposal the leader
handled but whose `proposeMsg` was dropped (P6) is never pre-accepted, hence never executed in
`b`, and neither is anything depending on it. -/
def lexec (N b : Nat) (x : CmdId) : Prop :=
  ∃ E : List CmdId, x ∈ E ∧ ∀ y ∈ E, y ∈ S.base b ∨
    ∃ D, S.pre (leaderOf N b) b y = some D ∧ ∀ d ∈ D, d ∈ E

/-- `x` is possibly chosen in `b` (a client may hold its result, the leader's
`resultIn (S.ordSeq N b) x`): a quorum's condition, and (D33) the leader executed it (only
the leader's `MReply`, sent after its execution, completes a client). -/
def possiblyChosen (N b : Nat) (x : CmdId) : Prop :=
  x ∈ S.ord N b ∧ (S.slowChosen N b x ∨ S.fastChosen N b x) ∧ S.lexec N b x

/-- An entry of a report is truthful about its reporter `r`'s state in its `cballot` `c`:
a registered command `r` has (the base or a proposal it handled), in one of the four phases; accepted or committed (phase
`ACCEPT` or `COMMIT`) with the leader's dependencies; pre-accepted (phase `PRE_ACCEPT`) with its
own dependencies, or the leader's proposal with its dependencies; in phase `START` (a proposal
whose descriptor had not run `handlePropose`), with some of its own dependencies (`proposeDep`,
or none). -/
def entryOk (N r c : Nat) (e : RepEntry) : Prop :=
  S.cmds e.id = some e.cmd ∧ e.id ∈ S.loc r c ∧ e.phase.toNat ≤ 3 ∧
  (e.phase.toNat ≥ 2 → (S.acc r c e.id ∨ S.com r c e.id) ∧ e.id ∈ S.ord N c ∧
    e.dep.Perm (depsIn (S.ordSeq N c) e.id)) ∧
  (e.phase.toNat = 1 →
    (r = leaderOf N c ∧ e.id ∈ S.ord N c ∧ e.dep.Perm (depsIn (S.ordSeq N c) e.id)) ∨
    S.pre r c e.id = some e.dep) ∧
  (e.phase.toNat = 0 → ∀ d ∈ e.dep, d ∈ depsIn (S.seqOf (S.loc r c)) e.id)

/-- The facts of a recovery report `R` of `r` for ballot `b'` (`fillNewLeaderAckN`), with
`c = R.cbal`: `r` had moved to `b'` (and so accepts nothing more below it), took no part in a
ballot between `c` and `b'`, reports every command of the `MSync` of `c` in `COMMIT` with the
`MSync`'s dependencies (N3's fix), every command it accepted, committed or pre-accepted in `c`
(and, as `c`'s leader, every proposal, in any phase: D33, a proposal dropped before
`handlePropose` is reported `START`), its entries in its handling order (F3's fix: the
`MSync`'s commands first, in some order, then `r.handled`), and every entry is truthful. -/
def repOk (N r b' : Nat) (R : Report) : Prop :=
  let c := R.cbal
  (S.rs r).ballot ≥ b' ∧ c < b' ∧
  (0 < c → ∃ M, S.sync c = some M ∧ ∀ p ∈ M, ∃ e ∈ R.entries, e.id = p.1 ∧
    e.phase.toNat = 3 ∧ e.dep.Perm p.2.2) ∧
  (∀ c' x, c < c' → c' < b' → ¬ S.acc r c' x ∧ S.pre r c' x = none ∧ ¬ S.com r c' x ∧
    S.loc r c' = []) ∧
  (∀ x, S.acc r c x ∨ S.com r c x →
    ∃ e ∈ R.entries, e.id = x ∧ (e.phase.toNat ≥ 2 ∨ (r = leaderOf N c ∧ e.phase.toNat ≥ 1))) ∧
  (∀ x D, S.pre r c x = some D → ∃ e ∈ R.entries, e.id = x ∧
    (e.phase.toNat ≥ 2 ∨ (e.phase.toNat = 1 ∧ e.dep = D))) ∧
  (r = leaderOf N c → ∀ x ∈ S.ord N c, ∃ e ∈ R.entries, e.id = x) ∧
  (∃ B, B.Perm (S.base c) ∧ R.entries.map (·.id) = B ++ (S.loc r c).drop (S.base c).length) ∧
  (∀ e ∈ R.entries, S.entryOk N r c e)

/-- **The protocol invariant** for `N` replicas (`fr`: fast reads on). -/
structure PInv (N : Nat) (fr : Bool) : Prop where
  /-- a replica's sequence: registered, no duplicates; from ballot 1 on, it starts with the
  ballot's `MSync` order -/
  loc_ok : ∀ r b, (S.loc r b).Nodup ∧ (∀ x ∈ S.loc r b, S.cmds x ≠ none) ∧
    (S.loc r b ≠ [] → r < N ∧ (S.rs r).ballot ≥ b ∧
      (b > 0 → S.sync b ≠ none ∧ S.base b <+: S.loc r b))
  /-- replicas' states: `cballot ≤ ballot`; in normal operation, `cballot = ballot` -/
  rs_ok : ∀ r, (S.rs r).cballot ≤ (S.rs r).ballot ∧
    ((S.rs r).normal → (S.rs r).cballot = (S.rs r).ballot)
  /-- an acceptance: of a command the replica handled and the leader ordered, in a ballot the
  replica reached; N2: a follower's dependencies accepted or committed first (the leader does not
  check them: SWB-9, notes/prove-swift.md §14) -/
  acc_ok : ∀ r b x, S.acc r b x → r < N ∧ x ∈ S.loc r b ∧ x ∈ S.ord N b ∧
    (S.rs r).ballot ≥ b ∧
    (r ≠ leaderOf N b → ∀ d ∈ depsIn (S.ordSeq N b) x, S.acc r b d ∨ S.com r b d)
  /-- a pre-acceptance: by a fast-quorum member, with its own dependencies in its sequence -/
  pre_ok : ∀ r b x D, S.pre r b x = some D → r ∈ AQ N b ∧ (S.rs r).ballot ≥ b ∧
    x ∈ S.loc r b ∧ D = depsIn (S.seqOf (S.loc r b)) x ∧ S.path r b x ≠ none
  /-- dependency paths (`HashLog`, reset by every `MSync`, F2): a path ends with its command;
  the leader's is its commands of the key in `b` up to `x`; a follower's has every command of
  the key it handled in `b` up to `x` (each pending, or removed by the leader's acknowledgement
  of a command whose number is at most that of the synced prefix's last one, which the leader
  numbered in its path order: so it is in that prefix) -/
  path_ok : ∀ r b x P, S.path r b x = some P → x ∈ S.loc r b ∧ x ∉ S.base b ∧ P.getLast? = some x ∧
    (r = leaderOf N b → P = S.keyPrefix r b x) ∧ (∀ y ∈ S.keyPrefix r b x, y ∈ P)
  /-- a commit: by the leader, of a command the replica accepted (a follower commits on the
  leader's acknowledgement, which it accepted first), or of the ballot's `MSync` -/
  com_ok : ∀ r b x, S.com r b x → r < N ∧ (S.rs r).ballot ≥ b ∧ x ∈ S.loc r b ∧
    (r = leaderOf N b ∨ S.acc r b x ∨ x ∈ S.base b)
  /-- reports are truthful -/
  rep_ok : ∀ r b R, S.rep r b = some R → S.repOk N r b R
  /-- `MSync`s are the recovery of a majority's reports, by the ballot's leader, which took it
  first -/
  sync_ok : ∀ b M, S.sync b = some M → b > 0 ∧ (S.rs (leaderOf N b)).ballot ≥ b ∧
    S.base b <+: S.ord N b ∧
    ∃ reps : List (Nat × Report), isMajority N (reps.map Prod.fst) ∧
      (∀ p ∈ reps, S.rep p.1 b = some p.2) ∧ M = recoverSync N reps
  /-- MR4: each replica's state carries exactly its rows -/
  rows_ok : ∀ r b, S.loc r b = (S.rs r).locAt b ∧ (∀ x, S.acc r b x ↔ (b, x) ∈ (S.rs r).accR) ∧
    (∀ x, S.pre r b x = (S.rs r).preAt b x) ∧ (∀ x, S.path r b x = (S.rs r).pathAt b x) ∧
    (∀ x, S.com r b x ↔ (b, x) ∈ (S.rs r).comR) ∧ S.rep r b = (S.rs r).repAt b
  /-- `G`: registered commands, no duplicates -/
  G_ok : (S.G.map Prod.fst).Nodup ∧ (∀ p ∈ S.G, S.cmds p.1 = some p.2)

end PState

end sp

end Perennial.github_com.imdea_software.swiftpaxos

end
