/-
Ported from dsverify-lab examples/epaxos/proof/Epaxos/Interface/State.lean (notes/dsv-epaxos.md).
Changed: the treemap is the real gods v1.18.1 (the lab's was a cut-down model), whose specs are
**hypotheses** here (the class `StateTreemap`, `Interface/Treemap.lean`: the coordinator's rule; a
gods model is being built on dsv-tpmodels); `isTreeMap` is that class's abstract predicate.

The `state` package (`state/state.go`) and the gods treemap, as the replicas use them:

* **The store.** `isState st S` (exclusive, sealed): `st` is a `*state.State` (read-only fields:
  its `mutex`, with invariant `True`, and its `Store`) whose treemap maps each key of `S` to a
  read-only `state.Value` slice holding `S`'s bytes. The pure image is the finite map
  `S : GMap w64 (List w8)` (a `state.Key` as its bits). Ownership is exclusive: the store belongs
  to whoever executes (the protocol layer's executor, under its instance lock); the mutex adds
  nothing. Values are read-only: `GET` returns the stored slice itself (`Execute` aliases it), and
  `PUT` stores the command's own `V` slice.
* **Commands in the heap.** `cmdOk c wc`: the `state.Command` value `c` has the image `wc`
  (`WCmd`: op byte, key, value bytes; its `V` slice read-only); `ownCmds sl cs dq`: a
  `[]state.Command` slice whose elements have the images `cs`.
* **The pure functions**: `execCmd S wc` (`Execute`'s new store and result: `PUT` stores and
  returns `NIL()`, `GET` returns the key's value or `NIL()`, `SCAN` returns the values of the
  keys of its range present in the store (`rangeKeys`), in key order, concatenated (a fresh
  slice), anything else returns `NIL()`), `conflict` (`Conflict` for non-`SCAN` commands: same key and one a
  `PUT`), `conflictBatch` (`ConflictBatch`).
* **Specs** (`def <Func>.spec : Prop`, grouped here): `InitState`, `NIL`, `NOOP`,
  `Command.Execute`, `Conflict`, `ConflictBatch`; the treemap's `NewWith` (with
  `KeyComparator`), `Put`, `Get` over `isTreeMap m M` (keys `state.Key`s, values `state.Value`s:
  the only way `state` uses it; `Select` and the iterator serve `SCAN` only, inside `Execute`:
  the state package's own proofs).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.Wire
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.Treemap

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std github_com.imdea_software.swiftpaxos_epaxos.kvs

/-! ## Pure -/

/-- `Command.Execute`'s new store and result on store `S`. -/
def execCmd (S : GMap w64 (List w8)) (c : WCmd) : GMap w64 (List w8) × List w8 :=
  if c.op = opPUT then (S.insert c.key c.val, [])
  else if c.op = opGET then (S, (S.lookup c.key).getD [])
  else if c.op = opSCAN then (S, ((rangeKeys c).filterMap S.lookup).flatten)
  else (S, [])

/-- `Conflict(gamma, delta)` for commands that are not `SCAN`s: the same key, and one of them a
`PUT`. -/
def conflict (g d : WCmd) : Bool := (g.key == d.key).and ((g.op == opPUT).or (d.op == opPUT))

/-- `ConflictBatch(b1, b2)`: some pair conflicts. -/
def conflictBatch (b1 b2 : List WCmd) : Bool := b1.any fun g => b2.any fun d => conflict g d

/-- `NOOP()`: one `NONE` command on key 0 with the empty value. -/
def noopCmds : List WCmd := [⟨opNONE, W64 0, []⟩]

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : StateTreemap GF]

/-! ## Heap representations -/

/-- The `state.Command` value `c` has the image `wc`; its value slice is read-only. -/
def cmdOk (c : state.Command) (wc : WCmd) : IProp GF :=
  iprop(⌜c.Op' = wc.op ∧ c.K' = wc.key⌝ ∗ c.V' ↦*□ wc.val)

instance cmdOk_persistent (c : state.Command) (wc : WCmd) : Persistent (cmdOk (GF := GF) c wc) := by
  unfold cmdOk; infer_instance

/-- A `[]state.Command` slice whose commands have the images `cs` (the slice with fraction
`dq`). -/
def ownCmds (sl : GoSlice) (cs : List WCmd) (dq : DFrac) : IProp GF :=
  iprop(∃ vs : List state.Command, sl ↦*{dq} vs ∗ ⌜vs.length = cs.length⌝ ∗
    [∗list] j ↦ c ∈ vs, ∃ wc, ⌜cs[j]? = some wc⌝ ∗ cmdOk c wc)

/-- The store `st` holds `S` (exclusive, sealed): see the file header. -/
def isStateDef (st : Loc) (S : GMap w64 (List w8)) : IProp GF :=
  iprop(∃ (mu store : Loc) (M : GMap w64 GoSlice),
    st ↦□ state.State.mk mu store ∗ sync.isMutex mu iprop(True) ∗ TH.isTreeMap store M ∗
    ⌜∀ k, (M.lookup k).isSome = (S.lookup k).isSome⌝ ∗
    [∗map] k ↦ sl ∈ M, sl ↦*□ ((S.lookup k).getD []))

@[irreducible] def isState (st : Loc) (S : GMap w64 (List w8)) : IProp GF :=
  isStateDef st S

theorem isState_unseal : @isState = @isStateDef := by funext; with_unfolding_all rfl

/-! ## Specs: the state package -/

/-- `InitState()`: an empty store. -/
def state.InitState.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.state }}
    (App (Val (@! state.InitState)) (Val #()))
  {{ (st : Loc), RET #st; isState st ∅ }}

/-- `NIL()`: a fresh empty value. -/
def state.NIL.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.state }}
    (App (Val (@! state.NIL)) (Val #()))
  {{ (sl : GoSlice), RET #sl; sl ↦* ([] : List w8) }}

/-- `NOOP()`: a fresh slice of one `NONE` command. -/
def state.NOOP.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.state }}
    (App (Val (@! state.NOOP)) (Val #()))
  {{ (sl : GoSlice), RET #sl; ownCmds sl noopCmds (DFrac.own 1) }}

/-- `c.Execute(st)`: the store becomes `(execCmd S wc).1` and the result (read-only: for a `GET`
of a present key it is the stored slice) holds `(execCmd S wc).2`. A `SCAN`'s value has 8 bytes
(at least: `binary.LittleEndian.Uint64` reads the first 8; S3: shorter scans are out of scope),
and its result fits a Go `int` (`concat` sums the values' lengths in an `int`; stored values may
alias, so the store alone does not bound the sum: HUB-REQUEST state-1). -/
def state.Command.Execute.spec : Prop :=
  ∀ (c : Loc) (dq : DFrac) (cv : state.Command) (wc : WCmd) (st : Loc)
    (S : GMap w64 (List w8)),
  (wc.op = opSCAN → 8 ≤ wc.val.length) →
  (wc.op = opSCAN → (execCmd S wc).2.length < 2 ^ 63) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.state ∗
      c ↦{dq} cv ∗ cmdOk cv wc ∗ isState st S }}
    (App (Val (c @!! go.GoType.PointerType state.Command.ty @!! go!"Execute")) (Val #st))
  {{ (ret : GoSlice), RET #ret; c ↦{dq} cv ∗ isState st (execCmd S wc).1 ∗
      ret ↦*□ (execCmd S wc).2 }}

/-- `Conflict(gamma, delta)` for commands that are not `SCAN`s. (No caller is reached in this
configuration: `findPreAcceptConflicts` serves the dead TryPreAccept path, D2, and the executor's
`transconf` loop is off; the range case is not specified for that reason, review T2-4.) -/
def state.Conflict.spec : Prop :=
  ∀ (g d : Loc) (dqg dqd : DFrac) (gv dv : state.Command) (wg wd : WCmd),
  wg.op ≠ opSCAN → wd.op ≠ opSCAN →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.state ∗
      g ↦{dqg} gv ∗ d ↦{dqd} dv ∗ cmdOk gv wg ∗ cmdOk dv wd }}
    (App (App (Val (@! state.Conflict)) (Val #g)) (Val #d))
  {{ RET #(conflict wg wd); g ↦{dqg} gv ∗ d ↦{dqd} dv }}

/-- `ConflictBatch(b1, b2)` for batches with no `SCAN` (no caller reached: see `Conflict.spec`). -/
def state.ConflictBatch.spec : Prop :=
  ∀ (s1 s2 : GoSlice) (dq1 dq2 : DFrac) (b1 b2 : List WCmd),
  (∀ c ∈ b1, c.op ≠ opSCAN) → (∀ c ∈ b2, c.op ≠ opSCAN) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.state ∗
      ownCmds s1 b1 dq1 ∗ ownCmds s2 b2 dq2 }}
    (App (App (Val (@! state.ConflictBatch)) (Val #s1)) (Val #s2))
  {{ RET #(conflictBatch b1 b2); ownCmds s1 b1 dq1 ∗ ownCmds s2 b2 dq2 }}

/-- `c.String()`: some string (through `Key.String`, `Value.String`: the local `formatInt16` and
`hexEncodeToString`; a `SCAN`'s branch reads its value with `binary.LittleEndian.Uint64`, 8 bytes
(S3), and formats it with the local `formatUint10`, FMT-SPRINT); the command unchanged
(HUB-REQUEST epaxos-3). -/
def state.Command.String.spec : Prop :=
  ∀ (c : Loc) (dq : DFrac) (cv : state.Command) (wc : WCmd),
  (wc.op = opSCAN → 8 ≤ wc.val.length) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.state ∗
      c ↦{dq} cv ∗ cmdOk cv wc }}
    (App (Val (c @!! go.GoType.PointerType state.Command.ty @!! go!"String")) (Val #()))
  {{ (s : GoString), RET #s; c ↦{dq} cv }}

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
