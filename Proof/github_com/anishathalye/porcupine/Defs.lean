/-
Lean-first (no Rocq counterpart).

# Porcupine: the specs' vocabulary (2026-10-14)

## A model

A `porcupine.Model` is a struct of closures. Its specification (`ModelSpec`) is a sequential
model `M` (`Theory.SeqModel`) over abstract states `σ`, whose operations are the
`(input, output)` pairs of interface values, with what a Go state value represents
(`rep k v s`, not necessarily persistent: the model's closures may write to a state value, as
etcd's robustness model sorts its states in place in `Equal`,
`issues/etcd-robustness-model-equal-mutates.md`; each closure is given the `rep`s it reads and
gives them back, of the same abstract states) and what an operation's input and output own
(`ioOk i o`, persistent: the model's `Step` may read memory they point to, e.g. etcd's requests
and responses). The checker keeps a state value in several places (its stack, its cache): it
shares each one in a non-atomic invariant (`Shared.lean`), not the model.

`rep k v s` is indexed by the number `k` of steps that made `v` from `Init`'s value (`Init`
gives index `0`, a step from index `k` gives `k + 1`), and `Step` need only work from an index
below `2^60`: the checker steps a value only along its stack of linearized operations, distinct
operations of a history of fewer than `2^60` (`HistOk`). A model whose values grow with each step
(a Go slice per pending operation, as `examples/linkv`'s) can bound their sizes by the index; a
model whose values do not ignores it.

A new state value's `rep` is separate from the old's (`S.rep v s ∗ stepPost …` in `Step`'s
postcondition): what one owns, the other does not (memory they share must be read-only in both,
or in neither), so no freshness premise is needed.

`isModel S m` is what a caller of the `Check*` functions gives (etcd's robustness model has this
shape: `Init`, `StepContext`, `Equal`; no `Partition`, no `Hash`):

- `Partition` is `nil` (porcupine then checks the whole history as one partition);
- `Init` returns a value representing `M.init`;
- `StepContext` is not `nil` and steps as `M` does, or answers `false` once its context is
  done (etcd's robustness model returns `(false, nil)` whenever `ctx.Err() != nil`, checked
  before and after the step); or it is `nil`, and `Step` is not `nil` and steps as `M` does;
- `Equal` is not `nil`, and returns `true` only on values of the same abstract state (it may
  return `false` on equal states: the cache then only misses);
- `Hash` is `nil` or returns anything (the cache is sound for any hash).

`isModelFilled S m` is the model after `fillDefault`: `StepContext` as above (steps as `M` does,
or answers `false` on a done context), and `Equal`, `Hash` as above. A wrong `false` only makes
`checkSingle` answer `false` with its context done, which its spec allows.

## A history

`histOf ops` is the abstract history of a Go slice of `Operation`s (inputs and outputs, call
and return timestamps read signed, as `int64`). `HistOk S ops` is the caller's premise on it:
every operation's call is at most its return, and there are fewer than `2^60` (so that the
entry ids, `2·n` entries and the bitset's size fit). `entryOf`, `EntriesFor` relate a Go slice of
`entry`s to the abstract entries of `Theory` (what `makeEntries` returns).
-/
module

public import Proof.github_com.anishathalye.porcupine.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.anishathalye.porcupine

open Theory

/-- An operation's content: its input and output. -/
abbrev OpV [FfiSyntax] := GoInterface × GoInterface

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

/-- A porcupine model's specification (see the file header). -/
structure ModelSpec (GF : BundledGFunctors) (σ : Type) where
  M : SeqModel σ OpV
  rep : Nat → GoInterface → σ → IProp GF
  ioOk : GoInterface → GoInterface → IProp GF
  ioOk_pers : ∀ i o, Persistent (ioOk i o)

variable {σ : Type}

instance ModelSpec.ioOk_persistent (S : ModelSpec GF σ) (i o : GoInterface) :
    Persistent (S.ioOk i o) := S.ioOk_pers i o

/-- What a step from a value of index `k` returns besides its verdict: a value of the new state,
of index `k + 1`, if the model allows the operation. -/
def stepPost (S : ModelSpec GF σ) (k : Nat) (s : σ) (io : OpV) (v' : GoInterface) : IProp GF :=
  match S.M.step s io with
  | some s' => S.rep (k + 1) v' s'
  | none => iprop(True)

/-- `Init()` returns a value of the model's initial state. -/
def initSpec (S : ModelSpec GF σ) (f : GoFunc) : IProp GF :=
  iprop({{ True }}
    (App (Val #f) (Val #()))
  {{ (v : GoInterface), RET #v; S.rep 0 v S.M.init }})

/-- `Step(state, input, output)`, on a value of index below `2^60`, steps as the model does, and
gives the state value back. -/
def stepSpec (S : ModelSpec GF σ) (f : GoFunc) : IProp GF :=
  iprop(∀ (k : Nat) (v : GoInterface) (s : σ) (i o : GoInterface),
    {{ ⌜k < 2 ^ 60⌝ ∗ S.rep k v s ∗ S.ioOk i o }}
      (App (App (App (Val #f) (Val #v)) (Val #i)) (Val #o))
    {{ (ok : Bool) (v' : GoInterface), RET (PairV #ok #v');
        S.rep k v s ∗ ⌜ok = (S.M.step s (i, o)).isSome⌝ ∗ stepPost S k s (i, o) v' }})

/-- `Equal(a, b)` returns `true` only on values of one state, and gives both values back (of
the same states: it may write to them, as etcd's robustness model sorts its states). -/
def equalSpec (S : ModelSpec GF σ) (f : GoFunc) : IProp GF :=
  iprop(∀ (k j : Nat) (v w : GoInterface) (s t : σ),
    {{ S.rep k v s ∗ S.rep j w t }}
      (App (App (Val #f) (Val #v)) (Val #w))
    {{ (b : Bool), RET #b; S.rep k v s ∗ S.rep j w t ∗ ⌜b = true → s = t⌝ }})

/-- `Hash(state)` returns some hash, and gives the state value back. -/
def hashSpec (S : ModelSpec GF σ) (f : GoFunc) : IProp GF :=
  iprop(∀ (k : Nat) (v : GoInterface) (s : σ),
    {{ S.rep k v s }}
      (App (Val #f) (Val #v))
    {{ (x : w64), RET #x; S.rep k v s }})

/-- `Equal` and `Hash`, as the checker uses them. -/
def isEqHash (S : ModelSpec GF σ) (m : Model) : IProp GF :=
  iprop(⌜m.Equal' ≠ func.nil⌝ ∗ equalSpec S m.Equal' ∗ (⌜m.Hash' = func.nil⌝ ∨ hashSpec S m.Hash'))

instance initSpec_persistent (S : ModelSpec GF σ) (f : GoFunc) :
    Persistent (initSpec S f) := by unfold initSpec; infer_instance
instance stepSpec_persistent (S : ModelSpec GF σ) (f : GoFunc) :
    Persistent (stepSpec S f) := by unfold stepSpec; infer_instance
instance equalSpec_persistent (S : ModelSpec GF σ) (f : GoFunc) :
    Persistent (equalSpec S f) := by unfold equalSpec; infer_instance
instance hashSpec_persistent (S : ModelSpec GF σ) (f : GoFunc) :
    Persistent (hashSpec S f) := by unfold hashSpec; infer_instance
instance isEqHash_persistent (S : ModelSpec GF σ) (m : Model) :
    Persistent (isEqHash S m) := by unfold isEqHash; infer_instance

/-- `Partition(history)` returns the one partition `[history]` (`noPartition`, what
`fillDefault` stores for a `nil` `Partition`). -/
def noPartitionSpec (f : GoFunc) : IProp GF :=
  iprop(∀ (sl : GoSlice) (ops : List Operation) (dq : DFrac),
    {{ sl ↦*{dq} ops }}
      (App (Val #f) (Val #sl))
    {{ (r : GoSlice), RET #r; r ↦* [sl] ∗ sl ↦*{dq} ops }})

instance noPartitionSpec_persistent (f : GoFunc) :
    Persistent (noPartitionSpec (GF := GF) f) := by unfold noPartitionSpec; infer_instance

/-- What every operation of a history owns, for the model's `Step`. -/
def histIoOk (S : ModelSpec GF σ) (h : List (Theory.Op OpV)) : IProp GF :=
  iprop([∗list] o ∈ h, S.ioOk o.val.1 o.val.2)

/-- What every operation of a slice of `Operation`s owns, for the model's `Step`. -/
def opsIoOk (S : ModelSpec GF σ) (ops : List Operation) : IProp GF :=
  iprop([∗list] o ∈ ops, S.ioOk o.Input' o.Output')

instance histIoOk_persistent (S : ModelSpec GF σ) (h : List (Theory.Op OpV)) :
    Persistent (histIoOk S h) := by unfold histIoOk; infer_instance
instance opsIoOk_persistent (S : ModelSpec GF σ) (ops : List Operation) :
    Persistent (opsIoOk S ops) := by unfold opsIoOk; infer_instance

/-- `checkSingle`'s second result, the longest partial linearization through each
operation: a slice of `n` pointers, each `nil` or to a read-only slice of ids (shared between
operations). Only memory safety is claimed of it (`LinearizationInfo` is for the visualizer). -/
def longestOwn (longest : GoSlice) (n : Nat) : IProp GF :=
  iprop(∃ ps : List Loc, longest ↦* ps ∗ ⌜ps.length = n⌝ ∗
    [∗list] p ∈ ps, ⌜p = null⌝ ∨
      ∃ (sl : GoSlice) (xs : List w64), p ↦□ sl ∗ sl ↦*{DFrac.discard} xs)

end defs

/-! The model's specs that mention its context (`stepCtxSpec`), stated at
`HeapGS HasLC.hasLC GF` as Perennial's `context.isContext` is. -/
section defs_hasLC
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]
variable {σ : Type}

/-- `StepContext(ctx, state, input, output)`, on a context `ctx` (`isContext c cs`) and a value
of index below `2^60`, steps as the model does, or refuses the operation once the context is done (`□ cs.PDone`, what
`isContext`'s `Err()` gives for a non-`nil` error): etcd's robustness model returns
`(false, nil)` whenever `ctx.Err() != nil`. It gives the state value back in both cases. -/
def stepCtxSpec (S : ModelSpec GF σ) (f : GoFunc) : IProp GF :=
  iprop(∀ (c : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (k : Nat) (v : GoInterface)
      (s : σ) (i o : GoInterface),
    {{ context.isContext c cs ∗ ⌜k < 2 ^ 60⌝ ∗ S.rep k v s ∗ S.ioOk i o }}
      (App (App (App (App (Val #f) (Val #(GoInterface.ok c))) (Val #v)) (Val #i)) (Val #o))
    {{ (ok : Bool) (v' : GoInterface), RET (PairV #ok #v');
        S.rep k v s ∗
        ((⌜ok = (S.M.step s (i, o)).isSome⌝ ∗ stepPost S k s (i, o) v') ∨
          (⌜ok = false⌝ ∗ □ cs.PDone)) }})

instance stepCtxSpec_persistent (S : ModelSpec GF σ) (f : GoFunc) :
    Persistent (stepCtxSpec S f) := by unfold stepCtxSpec; infer_instance

/-- A caller's model (see the file header). -/
def isModel (S : ModelSpec GF σ) (m : Model) : IProp GF :=
  iprop(⌜m.Partition' = func.nil⌝ ∗ initSpec S m.Init' ∗
    ((⌜m.StepContext' ≠ func.nil⌝ ∗ stepCtxSpec S m.StepContext') ∨
      (⌜m.StepContext' = func.nil ∧ m.Step' ≠ func.nil⌝ ∗ stepSpec S m.Step')) ∗
    isEqHash S m)

/-- A model with `Step` and no `StepContext`, from its parts (which are stated over any
`HasLC`). -/
theorem isModel_of_step (S : ModelSpec GF σ) (m : Model) :
    ⌜m.Partition' = func.nil⌝ ∗ initSpec S m.Init' ∗
      ⌜m.StepContext' = func.nil ∧ m.Step' ≠ func.nil⌝ ∗ stepSpec S m.Step' ∗ isEqHash S m ⊢
      isModel S m := by
  iintro ⟨%Hp, #Hi, %Hsc, #Hs, #Heh⟩
  unfold isModel
  iframe Hi Heh
  isplitr
  · ipureintro; exact Hp
  iright
  iframe Hs
  ipureintro; exact Hsc

/-- The model after `fillDefault` (see the file header). -/
def isModelFilled (S : ModelSpec GF σ) (m : Model) : IProp GF :=
  iprop(initSpec S m.Init' ∗ stepCtxSpec S m.StepContext' ∗ isEqHash S m)

instance isModel_persistent (S : ModelSpec GF σ) (m : Model) :
    Persistent (isModel S m) := by unfold isModel; infer_instance
instance isModelFilled_persistent (S : ModelSpec GF σ) (m : Model) :
    Persistent (isModelFilled S m) := by unfold isModelFilled; infer_instance

end defs_hasLC

/-! ## Histories and entries -/

section hist
variable [ext : FfiSyntax]

/-- An `Operation`'s abstract operation. -/
def opOf (o : Operation) : Theory.Op OpV :=
  ⟨(o.Input', o.Output'), sint.Z o.Call', sint.Z o.Return'⟩

/-- A slice of `Operation`s as a history. -/
def histOf (ops : List Operation) : List (Theory.Op OpV) := ops.map opOf

/-- The caller's premise on a history (see the file header). -/
def HistOk (ops : List Operation) : Prop :=
  (ops.length : Int) < 2 ^ 60 ∧ ∀ o ∈ ops, sint.Z o.Call' ≤ sint.Z o.Return'

/-- An `entry`'s abstract entry: its kind (`entryKind` is `Bool`, `returnEntry` is `true`) and
id. -/
def entryOf (e : entry) : Theory.Entry :=
  ⟨e.kind', (sint.Z e.id').toNat⟩

/-- `es` are the entries of history `h`: the abstract entries satisfy `EntriesOk`, each id is
a non-negative `int`, and each entry carries its operation's input (a call) or output (a
return) and time. -/
def EntriesFor (h : List (Theory.Op OpV)) (es : List entry) : Prop :=
  es.length = 2 * h.length ∧ EntriesOk h (es.map entryOf) ∧
    ∀ e ∈ es, 0 ≤ sint.Z e.id' ∧ ∃ o, h[(sint.Z e.id').toNat]? = some o ∧
      (if e.kind' then e.value' = o.val.2 ∧ sint.Z e.time' = o.ret
       else e.value' = o.val.1 ∧ sint.Z e.time' = o.call)

end hist

end github_com.anishathalye.porcupine

end Perennial
