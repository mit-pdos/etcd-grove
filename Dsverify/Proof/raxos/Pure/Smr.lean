/-
The replicated state machine as pure functions (the lab's `Pure/Smr.lean`, notes/dsv-quepaxa.md; an
epoch summary is a batch of one command, executed as a read).

A replica executes the decided slots `1, 2, …` in order (`updateStateMachine`); a slot decided
`ids` executes the client batches with those ids, from the replica's store, each batch id once
over the whole log (Q2's fix, `executeClientBatches`'s `executedBatches`), on the resident
key-value store (`kvStore.go`, `residentExecute`: a command is a type byte, an 8-byte key and a
value). The batch with an id is fixed for good (the batch registry: the client registers each
request before it sends it; `"nil"` is the empty batch every proxy stores at its start).

Every replica's execution of slots `1..c` is `execLog B (D.take c)` for the registry `B` and the
decided log `D` (agreement: one `ids` per slot), so replicas agree on the store and on each
batch's results.

Changed against the lab: the client's operations are the kit's `In`/`Out` (`model.go`), and the
store's specification is linkv's pending-writes store `kvB` (a put is a write, a get a read; the
kit's porcupine model is `pSeq kvB`'s state sets, as paxos's `woB`), in place of the lab's
`Harness.Model` `kv`: `execCmd_step` says executing an input's command on the store is `kvB`'s step.
-/
module

public import Perennial.Std.ByteString
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.PendModel

@[expose] public section

namespace Perennial.raxos.pure

/-- A client batch as the replicas see it: its id, its sender, its commands (one per
`ClientBatch_SingleMessage`). -/
structure Batch where
  id : GoString
  sender : Int
  cmds : List GoString
deriving DecidableEq, Inhabited

/-- The empty batch `"nil"` (`NewProxy`, `proposeToIndex`): sender -1, no commands. -/
def nilBatch : Batch := ⟨go!"nil", -1, []⟩

/-- The key length (kit.toml `KeyLen`, `raxos.New`'s `keyLen`). -/
def keyLen : Nat := 8

/-- The resident store's state: the Go map from keys to values. -/
abbrev Store := GoString → Option GoString

/-- `residentExecute` on one command `cmd` (at least `1 + keyLen` bytes: the type, the key,
the value): a write (`"0"`) stores the value and answers `"0"+key+"ok"`; a read answers
`"1"+key+value`, or `"1"+key+"nil"` for a key not stored. -/
def execCmd (st : Store) (cmd : GoString) : Store × GoString :=
  let key := (cmd.drop 1).take keyLen
  let val := cmd.drop (1 + keyLen)
  if cmd.take 1 = go!"0" then
    (fun k => if k = key then some val else st k, go!"0" ++ key ++ go!"ok")
  else
    (st, go!"1" ++ key ++ (st key).getD go!"nil")

/-- A command the store can execute (`residentExecute` slices it: no panic). -/
def cmdOk (cmd : GoString) : Prop := 1 + keyLen ≤ cmd.length

/-- A batch's commands executed in order: the store after, and the results. -/
def execBatch (st : Store) : List GoString → Store × List GoString
  | [] => (st, [])
  | c :: cs =>
    let (st1, r) := execCmd st c
    let (st2, rs) := execBatch st1 cs
    (st2, r :: rs)

/-- A command's write, if it is one: its key and value. -/
def cmdPut (cmd : GoString) : Option (GoString × GoString) :=
  if cmd.take 1 = go!"0" then some ((cmd.drop 1).take keyLen, cmd.drop (1 + keyLen)) else none

/-- The execution state of a prefix of the log: the store, the ids executed (in order), each
executed batch's results (by id), and the writes executed (in order). -/
structure ExecSt where
  store : Store
  done : List GoString
  results : GoString → Option (List GoString)
  puts : List (GoString × GoString)

def ExecSt.init : ExecSt := ⟨fun _ => none, [], fun _ => none, []⟩

/-- One slot's ids executed (`executeClientBatches`): each id not executed before is executed
on the store (its batch from the registry `B`); an id executed before is skipped. -/
def execIds (B : GoString → Option Batch) (es : ExecSt) : List GoString → ExecSt
  | [] => es
  | x :: xs =>
    if x ∈ es.done then execIds B es xs
    else
      let cmds := (B x).map Batch.cmds |>.getD []
      let (st', rs) := execBatch es.store cmds
      execIds B ⟨st', es.done ++ [x], fun y => if y = x then some rs else es.results y,
        es.puts ++ cmds.filterMap cmdPut⟩ xs

/-- The decided slots `1..c` (their ids, in order) executed from the start. -/
def execLog (B : GoString → Option Batch) (L : List (List GoString)) : ExecSt :=
  L.foldl (execIds B) ExecSt.init

/-- The store of the puts `l`, newest first (the lab's `Harness.Models` `kvAbs`: a key's value is
its newest put's). -/
def kvAbs : List (GoString × GoString) → Store
  | [] => fun _ => none
  | (k, v) :: l => fun k' => if k' = k then some v else kvAbs l k'

theorem kvAbs_put (l : List (GoString × GoString)) (k v : GoString) :
    kvAbs ((k, v) :: l) = fun k' => if k' = k then some v else kvAbs l k' := rfl

/-! ## The client's operations and the store's specification -/

/-- A key-value input as the kit's `In` (`model.go`): a put of `v` at `k`, or a get of `k`. -/
structure KIn where
  put : Bool
  k : GoString
  v : GoString
deriving DecidableEq, Inhabited

/-- A key-value answer as the kit's `Out` with a known outcome: a get's `found`/`v`, a put's
`⟨false, []⟩`. -/
structure KOut where
  found : Bool
  v : GoString
deriving DecidableEq, Inhabited

/-- **The store's specification**: linkv's pending-writes store of the map (a put is a write; a get
reads the key's value). -/
def kvB : EtcdGrove.linkv.PendSpec Store KIn KOut where
  init := fun _ => none
  step i st :=
    if i.put then (fun k => if k = i.k then some i.v else st k, ⟨false, []⟩)
    else (st, match st i.k with | some v => ⟨true, v⟩ | none => ⟨false, []⟩)
  isWrite i := i.put

/-- The command of an input (`kit.go`'s `command`): `"0"+key+value` for a put, `"1"+key` for a
get. -/
def cmdOf (i : KIn) : GoString :=
  if i.put then go!"0" ++ i.k ++ i.v else go!"1" ++ i.k

/-- The store's answer to an input's command, from the specification's answer (what `kit.go`'s
`result` reads back): a put is done; a get finds the value, or `"nil"` for nothing. -/
def ansOf (i : KIn) (o : KOut) : GoString :=
  if i.put then go!"0" ++ i.k ++ go!"ok"
  else if o.found then go!"1" ++ i.k ++ o.v else go!"1" ++ i.k ++ go!"nil"

/-- The inputs the kit makes (`Gen`): a key of `keyLen` (8) bytes; a put's value nonempty and not
`"nil"`. -/
def inputOk (i : KIn) : Prop :=
  i.k.length = keyLen ∧ (i.put → i.v ≠ [] ∧ i.v ≠ go!"nil")

/-- **Executing an input's command is the specification's step**, with the answer `ansOf` of the
step's answer. -/
theorem execCmd_step (st : Store) (i : KIn) (h : inputOk i) :
    cmdOk (cmdOf i) ∧
      execCmd st (cmdOf i) = ((kvB.step i st).1, ansOf i (kvB.step i st).2) := by
  obtain ⟨put, k, v⟩ := i
  obtain ⟨hk, -⟩ := h
  simp only at hk
  cases put with
  | false =>
    refine ⟨by simp [cmdOk, cmdOf, hk]; omega, ?_⟩
    have h2 : ((go!"1" ++ k).drop 1).take keyLen = k := by simp [← hk]
    have h0 : ((go!"1" ++ k).take 1 = go!"0") = False := by simp
    simp only [cmdOf, execCmd, h2, h0, ite_false, kvB, ansOf, Bool.false_eq_true]
    cases st k <;> rfl
  | true =>
    refine ⟨by simp [cmdOk, cmdOf, hk]; omega, ?_⟩
    have h1 : (go!"0" ++ k ++ v).take 1 = go!"0" := rfl
    have h2 : ((go!"0" ++ k ++ v).drop 1).take keyLen = k := by simp [← hk]
    have h3 : (go!"0" ++ k ++ v).drop (1 + keyLen) = v := by
      rw [← hk, List.append_assoc, List.drop_append, List.drop_append]; simp
    simp only [cmdOf, execCmd, h1, h2, h3, ite_true, kvB, ansOf]

end Perennial.raxos.pure
