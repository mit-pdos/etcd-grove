/-
Lean-first (no Rocq counterpart).

# The store's porcupine model (2026-10-19)

`examples/kvwitness/check.go`'s `Model()` is the store's sequential specification as a porcupine model,
and `Check` runs the lintest driver (`examples/lintest`) on it, with the store's operations as
the library (`apply`) and random traffic (`Gen`) as the inputs. This file holds what their specs
are stated over.

## The model (`kvS`)

The states are the store's (`KVMap`, `Base.lean`: every key's value). An input is a boxed `Input`
struct (`boxIn x`: its kind, key, value and replica); an output a boxed string (`boxS`). The
operation `(i, o)` is allowed in state `s` iff `i` is `boxIn x` and `o` is `boxS (inOut x s)`:
`""` for a `Put` or an `Append`, the key's value for a `Get`; the next state is `inStep x s` (a
`Put` sets the key, a `Get` leaves the store, any other kind appends, as `Check`'s `apply` runs
it: `inStep_kvNext`). `kvM` reads the input back with `inOf`, which is exact: a boxed `Input`
determines its fields (`boxIn_inj`: each field getter of the struct's value is a deterministic
pure step, so two equal values have equal fields).

A state value (`kvRep v s`) is a boxed `map[string]string`, read-only for good (`↦$□`: the model
never changes a state once made; `Step` copies before it writes), whose every key has the value
`s` gives it (a key it lacks: `[]`, as Go's lookup). Persistent, so `Step` may return its input
state (a `Get`).

## The driver's side

`kvInOk i` (the driver's `inOk`): `i` is a boxed `Input` with a key and a value shorter than
`2^61`, which `Gen` returns (one byte each) and `apply` asserts. The library's state and mask
are `Check`'s proof's (`Check.lean`): a copy of the store's state, kept in step with the client's
half of the store (`rkvVal γr`, `Defs.lean`) by an invariant.
-/
module

public import RaftWitness.Proof.github_com.mit_pdos.etcd_grove.examples.kvwitness.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvwitness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

/-- The test's input struct. -/
abbrev KVInput [GooseExts] := github_com.mit_pdos.etcd_grove.examples.kvwitness.Input

section model
variable [GooseExts] [go_gctx : GoGlobalContext]

/-- The type `map[string]string`. -/
abbrev kvMapTy : go.GoType := go.GoType.MapType go.string go.string

/-- The boxed `Input` `x` (`any(x)`). -/
abbrev boxIn (x : KVInput) : GoInterface :=
  interface.mkOk github_com.mit_pdos.etcd_grove.examples.kvwitness.Input.ty #x

/-- The boxed string `s`. -/
abbrev boxS (s : GoString) : GoInterface := interface.mkOk go.string #s

/-- The boxed map at `l`. -/
abbrev boxM (l : Loc) : GoInterface := interface.mkOk kvMapTy #l

/-- The store after the input `x`: a `Get` leaves it, a `Put` sets the key, any other kind
appends to it. -/
def inStep (x : KVInput) (s : KVMap) : KVMap :=
  if x.Kind' = opGetB then s
  else if x.Kind' = opPutB then kvUpd s x.Key' x.Val'
  else kvUpd s x.Key' (s x.Key' ++ x.Val')

/-- The output of the input `x` in the state `s`: a `Get`'s key's value, `""` otherwise. -/
def inOut (x : KVInput) (s : KVMap) : GoString := if x.Kind' = opGetB then s x.Key' else []

open Classical in
/-- The `Input` boxed in `i`, if it is one. -/
def inOf (i : GoInterface) : Option KVInput :=
  if h : ∃ x, i = boxIn x then some h.choose else none

/-- The store's sequential model (see the file header). -/
def kvM : SeqModel KVMap OpV where
  init := kvEmpty
  step s io :=
    match inOf io.1 with
    | some x => if io.2 = boxS (inOut x s) then some (inStep x s) else none
    | none => none

end model

section inj
variable [GooseExts] [go_gctx : GoGlobalContext] [lctx : GoLocalContext]
variable [GoSemanticsFunctions] [go.CoreSemantics]
variable [ta : github_com.mit_pdos.etcd_grove.examples.kvwitness.Input.TypeAssumptions]

theorem boxS_inj (a b : GoString) : boxS a = boxS b ↔ a = b := by
  constructor
  · intro h
    simp only [boxS, interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at h
    exact go.intoVal_inj h
  · rintro rfl; rfl

/-- A deterministic pure step's result is a function of its argument. -/
theorem pureDet_result {instr : GoInstruction} {a b : val} {ea eb : Expr}
    (Ha : go.IsGoStepPureDetTagged Tag.under instr a ea)
    (Hb : go.IsGoStepPureDetTagged Tag.under instr b eb) (h : a = b) : ea = eb := by
  subst h
  have h1 := Ha.isGoStep_det_internal.isGoStep_pure_det
  have h2 := Hb.isGoStep_det_internal.isGoStep_pure_det
  have := h1.symm.trans h2
  exact ((congrFun this ea).mp rfl).symm

/-- A boxed `Input` determines its fields (see the file header). -/
theorem boxIn_inj (x y : KVInput) : boxIn x = boxIn y ↔ x = y := by
  constructor
  · intro h
    simp only [boxIn, interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at h
    have hk := pureDet_result (ta.get_Kind x) (ta.get_Kind y) h
    have hK := pureDet_result (ta.get_Key x) (ta.get_Key y) h
    have hv := pureDet_result (ta.get_Val x) (ta.get_Val y) h
    have hr := pureDet_result (ta.get_Replica x) (ta.get_Replica y) h
    simp only [Expr.Val.injEq] at hk hK hv hr
    cases x; cases y
    simp only [KVInput, github_com.mit_pdos.etcd_grove.examples.kvwitness.Input.mk.injEq]
    exact ⟨go.intoVal_inj hk, go.intoVal_inj hK, go.intoVal_inj hv, go.intoVal_inj hr⟩
  · rintro rfl; rfl

theorem inOf_boxIn (x : KVInput) : inOf (boxIn x) = some x := by
  have h : ∃ y, boxIn x = boxIn y := ⟨x, rfl⟩
  unfold inOf
  rw [dif_pos h]
  congr 1
  exact ((boxIn_inj _ _).mp h.choose_spec).symm

/-- The model on a boxed input and a boxed output. -/
theorem kvM_step_box (s : KVMap) (x : KVInput) (o : GoString) :
    kvM.step s (boxIn x, boxS o) = if o = inOut x s then some (inStep x s) else none := by
  show (match inOf (boxIn x) with
    | some x => if boxS o = boxS (inOut x s) then some (inStep x s) else none
    | none => none) = _
  rw [inOf_boxIn]
  simp only [boxS_inj]

end inj

/-- `Check`'s `apply` on the input `x`: the operation it runs is `kvNext` of its kind (a `Get`,
a `Put`, or else an `Append`), and its answer is `inOut`. -/
theorem inStep_kvNext [GooseExts] (x : KVInput) (s : KVMap) :
    inStep x s = kvNext (if x.Kind' = opGetB then opGetB else if x.Kind' = opPutB then opPutB
      else opAppendB) x.Key' x.Val' s := by
  have h1 : opGetB ≠ opPutB := by decide
  have h2 : opGetB ≠ opAppendB := by decide
  have h3 : opAppendB ≠ opPutB := by decide
  unfold inStep kvNext
  by_cases hg : x.Kind' = opGetB
  · rw [if_pos hg, if_pos hg, if_neg h1, if_neg h2]
  · rw [if_neg hg, if_neg hg]
    by_cases hp : x.Kind' = opPutB
    · rw [if_pos hp, if_pos hp, if_pos rfl]
    · rw [if_neg hp, if_neg hp, if_neg h3, if_pos rfl]

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]

/-- A state value (see the file header; persistent). -/
def kvRep (v : GoInterface) (s : KVMap) : IProp GF :=
  iprop(∃ (l : Loc) (m : GMap GoString GoString), ⌜v = boxM l⌝ ∗ l ↦$□ m ∗
    ⌜∀ k, (m !! k).getD [] = s k⌝)

instance kvRep_persistent (v : GoInterface) (s : KVMap) : Persistent (kvRep (GF := GF) v s) := by
  unfold kvRep; infer_instance

/-- The store's porcupine model specification (see the file header). -/
def kvS : ModelSpec GF KVMap where
  M := kvM
  rep _ := kvRep
  ioOk i o := iprop(⌜(∃ x, i = boxIn x) ∧ ∃ str, o = boxS str⌝)
  ioOk_pers _ _ := by infer_instance

/-- The test's inputs: boxed `Input`s (the driver's `inOk`), whose key and value are shorter than
`2^61` (what the store's operations take: `encode`'s capacity, `25` plus both lengths, is then an
`int`). -/
abbrev kvInOk (i : GoInterface) : IProp GF :=
  iprop(⌜∃ x, i = boxIn x ∧ (x.Key'.length : Int) < 2 ^ 61 ∧ (x.Val'.length : Int) < 2 ^ 61⌝)

end defs

end kvwitness
end EtcdGrove
end Perennial
