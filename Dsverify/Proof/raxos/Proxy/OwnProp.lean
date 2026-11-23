/-
Package `proxy`'s definition of the main loop's exclusive state (the body of `proxyOwnDef` is
`∃ γq, ownQ γ k pr γq`).

What `NewProxy` must establish (besides the fields it already had to: the log, the executed
prefix, the proposal frontier, `toBeProposed`, the decided slots to piggyback):
* `storeHasDef γs "nil"` (`NewProxy` adds the genesis batch `"nil"` to the store);
* the capacities of `lastDecidedIndexes`, `lastDecidedProposers`, `lastDecidedDecisions`
  (`make([]T, 0)`: `ownSliceCap`);
* `ownProp`: the `proposeRequestIndex` channel (a bag, elements `reqIdxP γq`), a fresh ghost map
  `γq` (empty: no pending slot), `instanceTimeouts` (`make(..., 1000000)`: all `nil`),
  `lastTimeProposed`, and the constant `batchTime`;
* `epochOwn`: the `epochTimes` slice (stage 2).
-/
module

public import Dsverify.Proof.raxos.Proxy.StateDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

instance ProposeRequestIndex.countable [GooseExts] : Pos.Countable ProposeRequestIndex :=
  .ofInjective (fun v => Pos.Countable.encode v.index')
    (by rintro ⟨⟩ ⟨⟩ h; have h := Pos.encode_inj h; simp_all)

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]

/-- An element of `proposeRequestIndex` (a timer's request to propose slot `index`): the pending
slot's exclusive ghost element (its init token is in `ownProp`). -/
def reqIdxP (γq : GName) (v : ProposeRequestIndex) : IProp GF :=
  ghostMapElem γq (sint.Z v.index') (DFrac.own 1) ()

/-- The main loop's proposal state, at proposal frontier `lp` (`lastProposedIndex`) and log
length `n`: the pending slots `Pm` (issued, a timer running or its request in the channel) with
their init tokens; every issued slot is in the log or pending; `instanceTimeouts` (only issued
slots have a timer); `lastTimeProposed`; constants. -/
def ownProp (γ : QNames) (k : Nat) (pr : Loc) (γq : GName) (lp : Int) (n : Nat) : IProp GF :=
  iprop(∃ (Pm : GMap Int Unit) (its : GoSlice) (ts : List Loc) (tlp : time.Time) (bt : w64),
    (∃ hs : raxos.replica.src.Assumptions, haveI := hs;
      chanField ProposeRequestIndex.ty pr go!"proposeRequestIndex" (reqIdxP γq)) ∗
    ghostMapAuth γq 1 Pm ∗ ([∗map] i ↦ _u ∈ Pm, initTok γ k i) ∗
    ⌜(∀ i, (Pm !! i).isSome → 1 ≤ i ∧ i ≤ lp) ∧
      (∀ i, 1 ≤ i → i ≤ lp → i < n ∨ (Pm !! i).isSome)⌝ ∗
    pr.[Proxy, go!"instanceTimeouts"] ↦ its ∗ its ↦* ts ∗
    ⌜ts.length = 1000000 ∧ ∀ (i : Nat) (t : Loc), ts[i]? = some t → t ≠ null → (i : Int) ≤ lp⌝ ∗
    pr.[Proxy, go!"lastTimeProposed"] ↦ tlp ∗ pr.[Proxy, go!"batchTime"] ↦□ bt)

/-- The decided slots to piggyback on the next proposal (`lastDecided*`), with the slices'
capacities. -/
def decState (γ : QNames) (pr : Loc) : IProp GF :=
  iprop(∃ (ls ps ds : GoSlice), pr.[Proxy, go!"lastDecidedIndexes"] ↦ ls ∗
    pr.[Proxy, go!"lastDecidedProposers"] ↦ ps ∗ pr.[Proxy, go!"lastDecidedDecisions"] ↦ ds ∗
    decidedSlotsP γ ls ps ds ∗ ownSliceCap w64 ls (DFrac.own 1) ∗
    ownSliceCap w32 ps (DFrac.own 1) ∗ ownSliceCap GoSlice ds (DFrac.own 1))

/-- The epochs' times (`epochTimes`, leader mode 2's measurements: any values). -/
def epochOwn (pr : Loc) : IProp GF :=
  iprop(∃ (et : GoSlice) (ets : List EpochTime), pr.[Proxy, go!"epochTimes"] ↦ et ∗ et ↦* ets ∗
    ownSliceCap EpochTime et (DFrac.own 1))

/-- The main loop's state for the ghost name `γq` of its pending slots: the replicated log and
the executed prefix (`logP`, `smrP`), the proposal frontier (`lastProposedIndex`, the init
frontier one past it), the ids to propose (in the store, registered), the decided slots to
piggyback, `ownProp`. -/
def ownQ (γ : QNames) (c : QConf) (k : Nat) (pr : Loc) (γq : GName) : IProp GF :=
  iprop(∃ (γs : GName) (cb bm ebm : Loc) (rl : GoSlice) (slots : List Slot)
      (L : List (Option (List GoString))) (ci lp : w64) (D : List (List GoString))
      (Bm : GMap GoString Batch) (tb : GoSlice) (tbs : List GoString),
    pr.[Proxy, go!"clientBatchStore"] ↦□ cb ∗ isStoreDef γ γs cb ∗ storeHasDef γs go!"nil" ∗
    pr.[Proxy, go!"benchmark"] ↦□ bm ∗ pr.[Proxy, go!"executedBatches"] ↦□ ebm ∗
    pr.[Proxy, go!"replicatedLog"] ↦ rl ∗ rl ↦* slots ∗ ownSliceCap Slot rl (DFrac.own 1) ∗
    logP γ γs c slots L ∗ smrP γ pr bm ebm L ci D Bm ∗
    pr.[Proxy, go!"lastProposedIndex"] ↦ lp ∗ initFront γ k (sint.Z lp + 1) ∗
    ⌜0 ≤ sint.Z lp ∧ sint.Z lp ≤ 600⌝ ∗
    pr.[Proxy, go!"toBeProposed"] ↦ tb ∗ tb ↦* tbs ∗ ownSliceCap GoString tb (DFrac.own 1) ∗
    ([∗list] x ∈ tbs, idP γ γs x) ∗
    decState γ pr ∗ epochOwn pr ∗
    ownProp γ k pr γq (sint.Z lp) slots.length)

end defs

end Perennial.raxos
