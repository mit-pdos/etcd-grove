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
`checkSingle` answer `false` with its context done, which its spec allows; a `true` is never
wrong, so an answer `true` stays sound.

## A history

`histOf ops` is the abstract history of a Go slice of `Operation`s (inputs and outputs, call
and return timestamps read signed, as `int64`). `HistOk ops` is v1.3.1's premise on it: every
operation's call is at most its return, and there are fewer than `2^60`. PR #46 adds `ClientsOk`:
the client ids are non-negative and small enough for the allocations they size
(`ClientIdsOk`, `AllocOk`, `maxAllocBytes`), and along each client's listed order the returns do
not decrease (`MonoReturns`). The checker decides linearizability respecting the client order
(`Theory.LinearizableCO` at `clientOrder`); under sequential clients (`ClientsSeq`) that is
linearizability (`linCO_iff_lin`).

The PR never calls the model's `Hash` (its cache hashes the bitset only), so `isModel`'s and
`isModelFilled`'s `Hash` clause is not needed; it is kept to share v1.3.1's `isModel`.

The allocations that grow with the number of operations only (`longest`, the bitset, `seq`) are
smaller than the caller's slice of `Operation`s, or are grown by `append` (the entries, the
per-client slices, the stack, the cache), which asks for more than `maxAlloc` only from a live
slice of more than about 0.8·2^48 bytes: Go runs out of memory first, so no premise bounds them.

## A partition

`makeEntries` splits a partition by client: an `operationHistory`, one slice of
`clientOperation`s per client (`ohistOwn`, `CoFresh`), abstractly the chains `chainsOf ops nc`
(`Chains.lean`).
-/
module

public import PorcupineDag.Proof.github_com.anishathalye.porcupine.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.anishathalye.porcupine

open Theory

/-- An operation's content: its input and output. -/
abbrev OpV [GooseExts] := GoInterface × GoInterface

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
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

/-! ## Histories, clients and chains -/

section hist
variable [GooseExts]

/-- An `Operation`'s abstract operation. -/
def opOf (o : Operation) : Theory.Op OpV :=
  ⟨(o.Input', o.Output'), sint.Z o.Call', sint.Z o.Return'⟩

/-- A slice of `Operation`s as a history. -/
def histOf (ops : List Operation) : List (Theory.Op OpV) := ops.map opOf

/-- The caller's premise on a history (v1.3.1's): fewer than `2^60` operations, each called no
later than it returns. -/
def HistOk (ops : List Operation) : Prop :=
  (ops.length : Int) < 2 ^ 60 ∧ ∀ o ∈ ops, sint.Z o.Call' ≤ sint.Z o.Return'

/-- gc's largest allocation, in bytes: `maxAlloc` on 64-bit platforms other than ios/arm64 and
wasm (2^48); a larger `make` panics (`makeslice: len out of range`). Perennial does not model the
limit: the premises that mention it keep the specs true of Go; the proofs use them only to keep
`n·numClients` and `maxClientId + 1` within `int`. -/
@[word_unfold] def maxAllocBytes : Int := 2 ^ 48

/-- The allocations sized by `nc` clients over `n` operations fit (`newChains`, `makeEntries`):
the largest is `8·nc·max n 6` bytes (`firstUnks`, `8·n·nc`; the clients, `48·nc`). -/
@[word_unfold] def AllocOk (nc n : Nat) : Prop := (nc : Int) * ((max n 6 : Nat) : Int) * 8 ≤ maxAllocBytes

/-- The client ids index the chains: non-negative, and small enough that the allocations they
size fit. -/
def ClientIdsOk (ops : List Operation) : Prop :=
  ∀ o ∈ ops, 0 ≤ sint.Z o.ClientId' ∧ AllocOk (sint.nat o.ClientId' + 1) ops.length

/-- Along each client's listed order, the returns do not decrease. -/
def MonoReturns (ops : List Operation) : Prop :=
  ∀ (i j : Nat) (oi oj : Operation), i < j → ops[i]? = some oi → ops[j]? = some oj →
    oi.ClientId' = oj.ClientId' → sint.Z oi.Return' ≤ sint.Z oj.Return'

/-- PR #46's premise on a history (`notes/porcupine-dag-plan.md`, spec plan, "Premises"). -/
def ClientsOk (ops : List Operation) : Prop := ClientIdsOk ops ∧ MonoReturns ops

/-- The client order: `i` listed before `j`, with the same client id. -/
def clientOrder (ops : List Operation) (i j : Nat) : Prop :=
  i < j ∧ ∃ oi oj : Operation, ops[i]? = some oi ∧ ops[j]? = some oj ∧ oi.ClientId' = oj.ClientId'

/-- Sequential clients: of two operations of one client, the one listed first returns strictly
before the other is called. Under it the client order is real time's (`linCO_iff_lin`). -/
def ClientsSeq (ops : List Operation) : Prop :=
  ∀ (i j : Nat) (oi oj : Operation), i < j → ops[i]? = some oi → ops[j]? = some oj →
    oi.ClientId' = oj.ClientId' → sint.Z oi.Return' < sint.Z oj.Call'

/-- `Consistency.Check` on linearizability (`RealTime`, then `GeneralLikely`): `HardBefore` if
`a` returns before `b` is called, `HardAfter` if `a` is called after `b` returns, else
`SoftBefore`/`SoftAfter`/`DontKnow` as `a`'s call is before, after or at `b`'s. -/
def linOrder (a b : Operation) : w64 :=
  if sint.Z a.Return' < sint.Z b.Call' then W64 (-2)
  else if sint.Z b.Return' < sint.Z a.Call' then W64 2
  else if sint.Z a.Call' < sint.Z b.Call' then W64 (-1)
  else if sint.Z b.Call' < sint.Z a.Call' then W64 1
  else W64 0

/-- A partition's well-formedness (`HistOk` in pure terms). -/
def HistWf (h : List (Theory.Op OpV)) : Prop := (h.length : Int) < 2 ^ 60 ∧ Theory.CallLeRet h

/-- The chains `makeEntries` builds: client `c`'s ids, in order, for the clients below `nc`. -/
def chainsOf (ops : List Operation) (nc : Nat) : List (List Nat) :=
  (List.range nc).map fun (c : Nat) =>
    (List.range ops.length).filter fun (i : Nat) =>
      decide (((ops[i]?).map (fun o => sint.Z o.ClientId')) = some (c : Int))

/-- A client's slice of `clientOperation`s holding the chain `ch` of `h`, as `makeEntries` builds
it: each with its id (`id`, `globalId`), its operation's input, output and times, and not yet
`visited` (its other fields, `firstUnk` and the operation's other fields, any). -/
def CoFresh (h : List (Theory.Op OpV)) (ch : List Nat) (cos : List clientOperation) : Prop :=
  cos.length = ch.length ∧ ∀ (k : Nat) (co : clientOperation), cos[k]? = some co →
    ∃ (y : Nat) (o : Theory.Op OpV), ch[k]? = some y ∧ h[y]? = some o ∧
    sint.Z co.id' = y ∧ sint.Z co.globalId' = y ∧ co.Op'.Input' = o.val.1 ∧
    co.Op'.Output' = o.val.2 ∧ sint.Z co.Op'.Call' = o.call ∧ sint.Z co.Op'.Return' = o.ret ∧
    co.visited' = false

end hist

section ohist
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

/-- An `operationHistory` (one slice of `clientOperation`s per client) holding the chains `cs`
of `h`. -/
def ohistOwn (ohsl : GoSlice) (h : List (Theory.Op OpV)) (cs : List (List Nat)) : IProp GF :=
  iprop(∃ sls : List GoSlice, ohsl ↦* sls ∗ ⌜sls.length = cs.length⌝ ∗
    [∗list] c ↦ sl ∈ sls, ∃ cos : List clientOperation, sl ↦* cos ∗ ⌜CoFresh h (chain cs c) cos⌝)

end ohist

/-! ## Laws -/

/-- What the `Check*` specs' result (`Ok` and the property, `Illegal` and not, or `Unknown` with
a timeout) gives a caller that knows the property (`L`): `Ok`, or `Unknown` with a timeout. -/
theorem checkResult_complete {r : GoString} {L : Prop} {dur : w64}
    (hr : (r = go!"Ok" ∧ L) ∨ (r = go!"Illegal" ∧ ¬ L) ∨ (r = go!"Unknown" ∧ 0 < sint.Z dur))
    (hL : L) : r = go!"Ok" ∨ (r = go!"Unknown" ∧ 0 < sint.Z dur) := by
  rcases hr with ⟨h1, -⟩ | ⟨-, h2⟩ | h3
  · exact Or.inl h1
  · exact absurd hL h2
  · exact Or.inr h3

section laws
variable [GooseExts] {σ : Type}

/-- Under sequential clients, the client order is real time's: linearizable respecting it is
linearizable. -/
theorem linCO_iff_lin {M : SeqModel σ OpV} {ops : List Operation} (hseq : ClientsSeq ops) :
    LinearizableCO M (histOf ops) (clientOrder ops) ↔ Linearizable M (histOf ops) := by
  refine ⟨linearizable_of_co, good_mono fun a b hab => ?_⟩
  rcases hab with hp | ⟨hlt, oa, ob, ha, hb, hc⟩
  · exact hp
  · refine ⟨opOf oa, opOf ob, ?_, ?_, hseq a b oa ob hlt ha hb hc⟩
    · simp [histOf, ha]
    · simp [histOf, hb]

/-- Linearizable respecting the client order, from a linearization (respecting real time) that
keeps each client's operations in the order listed. -/
theorem linearizableCO_intro {M : SeqModel σ OpV} {h : List (Theory.Op OpV)}
    {co : Nat → Nat → Prop} {π : List Nat}
    (hπ : Completes M h (Prec h) (fun _ => False) M.init π)
    (hco : π.Pairwise fun a b => ¬ co b a) : LinearizableCO M h co := by
  obtain ⟨hnd, hmem, hrun, hpw⟩ := hπ
  refine ⟨π, hnd, hmem, hrun, ?_⟩
  refine List.Pairwise.imp₂ (fun a b h1 h2 hor => ?_) hpw hco
  rcases hor with h | h
  · exact h1 h
  · exact h2 h

end laws

end github_com.anishathalye.porcupine

end Perennial
