/-
Lean-first (no Rocq counterpart).

# lintest/counter: the counter's model and its lock invariant (2026-10-14)

`examples/lintest/counter/counter.go` is an instance of the lintest driver: a counter under a
mutex, its porcupine model and `Check`, which runs the driver on them.

## The model (`counterS`)

States are `w64` (Go's `int64`, wrapping). An operation `(i, o)` of interface values is
allowed in state `s` iff its output is the boxed `int64` of the next state
`counterNext s i`, which is `s + 1` if the input is not `nil` (`isInc i`, `input != nil`) and
`s` otherwise. A state value is the boxed `int64` of the state (`rep`); an operation's output
is a boxed `int64` (`ioOk`), which `Step`'s `output.(int64)` needs. The input needs nothing:
`Step` and `Apply` only compare it with `nil`, which is why they take any interface value,
even an ill-formed one (`lintest.Run`'s `applySpec` quantifies over all of them).

## The counter (`isCounter γ c`)

The mutex `c.mu` guards `c.n`, with half of a ghost variable `γ` holding the same value
(`counterR`); the other half is the library's abstract state (`counterState γ s`), which the
driver's invariant holds. `Apply`'s linearization point is right after it takes the lock.
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.lintest.counter
public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.mit_pdos.etcd_grove.examples.lintest.counter

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.counter.Assumptions]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest.counter :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest.counter :=
  build_get_is_pkg_init_wf

end init

end github_com.mit_pdos.etcd_grove.examples.lintest.counter

namespace EtcdGrove
namespace lintest
namespace counter

open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory
section model
variable [ext : FfiSyntax] [go_gctx : GoGlobalContext]

/-- `input != nil`: does `i` increment? -/
def isInc (i : GoInterface) : Bool :=
  match i with
  | interface.nil => false
  | interface.ok _ => true

/-- The boxed `int64` `x` (`any(x)`). -/
abbrev boxI (x : w64) : GoInterface := interface.mkOk go.int64 #x

/-- The state after input `i` in state `s`. -/
def counterNext (s : w64) (i : GoInterface) : w64 := if isInc i then s + W64 1 else s

/-- The counter's sequential model (see the file header). -/
def counterM : SeqModel w64 OpV where
  init := W64 0
  step s io := if io.2 = boxI (counterNext s io.1) then some (counterNext s io.1) else none

theorem counterM_step (s : w64) (i o : GoInterface) :
    counterM.step s (i, o) =
      if o = boxI (counterNext s i) then some (counterNext s i) else none := rfl

theorem boxI_inj (x y : w64) : boxI x = boxI y ↔ x = y := by
  constructor
  · intro h
    simp only [boxI, interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at h
    exact GoGlobalContext.intoVal_inj_w64 h
  · rintro rfl; rfl

/-- The model on an output `boxI x`. -/
theorem counterM_step_box (s x : w64) (i : GoInterface) :
    counterM.step s (i, boxI x) =
      if x = counterNext s i then some (counterNext s i) else none := by
  rw [counterM_step]
  simp only [boxI_inj]

end model

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- The address of `c.mu`. -/
abbrev muAddr (c : Loc) : Loc :=
  structFieldRef github_com.mit_pdos.etcd_grove.examples.lintest.counter.Counter go!"mu" c

/-- The address of `c.n`. -/
abbrev nAddr (c : Loc) : Loc :=
  structFieldRef github_com.mit_pdos.etcd_grove.examples.lintest.counter.Counter go!"n" c

end addrs

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.counter.Assumptions]

/-- The counter's porcupine model specification (see the file header). -/
def counterS : ModelSpec GF w64 where
  M := counterM
  rep v s := iprop(⌜v = boxI s⌝)
  rep_pers _ _ := by infer_instance
  ioOk _ o := iprop(⌜∃ x : w64, o = boxI x⌝)
  ioOk_pers _ _ := by infer_instance

/-- What `Step` returns of a next state: `stepPost` of the output `boxI x`. -/
theorem stepPost_counter (s x : w64) (i : GoInterface) :
    ⊢ stepPost (counterS (GF := GF)) s (i, boxI x) (boxI (counterNext s i)) := by
  unfold stepPost
  simp only [counterS]
  rw [counterM_step_box]
  by_cases h : x = counterNext s i
  · simp only [h, ite_true]
    ipureintro; trivial
  · simp only [h, ite_false]
    itrivial

/-- The lock invariant of `c.mu` (see the file header). -/
abbrev counterR (γ : GName) (c : Loc) : IProp GF :=
  iprop(∃ n : w64, nAddr c ↦ n ∗ ghostVar γ (1 : Qp).half n)

/-- The library's abstract state: the counter's value is `s`. -/
abbrev counterState (γ : GName) (s : w64) : IProp GF := ghostVar γ (1 : Qp).half s

/-- The counter `c` (persistent; see the file header). -/
def isCounter (γ : GName) (c : Loc) : IProp GF :=
  iprop(sync.isMutex (muAddr c) (counterR γ c))

instance isCounter_persistent (γ : GName) (c : Loc) : Persistent (isCounter (GF := GF) γ c) := by
  unfold isCounter; infer_instance

end defs

end counter
end lintest
end EtcdGrove

end Perennial
