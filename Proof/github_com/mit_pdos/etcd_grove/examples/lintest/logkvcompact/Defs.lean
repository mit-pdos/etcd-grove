/-
Lean-first (no Rocq counterpart).

# lintest/logkvcompact: the register's model, its abstract state and the server's lock invariant (2026-10-28)

`examples/lintest/logkvcompact/logkvcompact.go` is a register whose writes go through a log: `Put` appends
its value to the log under the mutex and waits until the apply goroutine (`applyLoop`) has
applied it; `Get` reads the applied state. `Check` runs the lintest driver on it.

## The model (`regS`)

States are `GoString`s, initially `""`. The inputs are boxed `Op` structs (`boxOp`): a write
`Op{Put: true, Val: v}` takes any state to `v` (whatever its output: porcupine's `Step` does
not look at a write's output); a read `Op{Put: false, ...}` leaves the state `s` and must output
the boxed `s` (`boxS`). The inputs are boxed `Op`s (`regInOk`, the driver's `inOk`), and a read's output is a boxed `string` (`ioOk`): what `Step`'s
`input.(Op)` and, on a read only, `output.(string)` need.

## The API (`isServer γ s`, `regState γ v`)

The register's abstract state is `regState γ v`: half of a ghost variable `γ`. A server
`s` serving it is `isServer γ s` (persistent; the name of the log's requests, `γr`, is hidden in
it). `Put` and `Get` are logically atomic over
`regState` with no invariant of their own (mask `∅`): the same specs a register under a mutex
would have. Nothing in them mentions the log.

## The lock invariant (`logkvcompactR γ s`)

The mutex guards the log `s.log`, its offset `s.start`, the applied count `s.applied` and the
state `s.state`. The writes ever made are a list of requests `rs` (`Req`: the value, the name of the writer's saved postcondition
and the name of its ticket), recorded in a monotone ghost list `γr` (a writer keeps a
persistent witness of its request's index); the log holds the values of those from `start` on
(`start ≤ applied`: the apply goroutine compacts only what it applied). `start + len(log)`, the
number of writes, does not wrap around: the lock invariant keeps one time receipt per write
(`⧗ |rs|`), so `|rs| < receiptBound GF ≤ 2^64` (`isServer`). The state is the other half of `γ`. The first
`applied` requests are done (`doneSlot`): the writer's postcondition `P` waits there until the
writer takes it, leaving its ticket. The others are pending (`pendSlot`): each holds its
writer's atomic update (`regAu`), a fancy update that takes the register to its value and gives
back the postcondition `P`. `applyLoop` fires it when it applies the entry (the linearization
point of `Put`, in the apply goroutine), and moves the slot from pending to done; the writer,
woken once `applied` passes its index, collects `P`: the saved proposition (`savedPropOwn`,
discarded) says it is its own (`▷ (P ≡ P')`), the ticket (`token`) that it was not taken yet.
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact
public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.Defs
public import Perennial.Proof.sync.CondDefs
public import Perennial.Ghost.SavedProp
public import Perennial.Ghost.MonoList
public import Perennial.Ghost.Token

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact.Assumptions]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact :=
  build_get_is_pkg_init_wf

end init

end github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact

namespace EtcdGrove
namespace lintest
namespace logkvcompact

open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

/-- The Go struct `Op`. -/
abbrev LOp [GooseExts] := github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact.Op

section model
variable [GooseExts] [go_gctx : GoGlobalContext]

/-- The boxed `string` `x` (`any(x)`). -/
abbrev boxS (x : GoString) : GoInterface := interface.mkOk go.string #x

/-- The boxed `Op` `o` (`any(o)`). -/
abbrev boxOp (o : LOp) : GoInterface :=
  interface.mkOk github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact.Op.ty #o

open Classical in
/-- The value an input writes, if it is a write. -/
def putVal (i : GoInterface) : Option GoString :=
  if h : ∃ v, i = boxOp ⟨true, v⟩ then some h.choose else none

open Classical in
/-- The register's step: a write takes any state to its value, whatever its output; a read
leaves the state, and its output must be the state. -/
def regStep (s : GoString) (io : OpV) : Option GoString :=
  match putVal io.1 with
  | some v => some v
  | none => if io.2 = boxS s then some s else none

/-- The register's sequential model (see the file header). -/
def regM : SeqModel GoString OpV where
  init := go!""
  step := regStep

end model

section inj
variable [GooseExts] [go_gctx : GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions] [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact.Assumptions]

theorem boxS_inj (x y : GoString) : boxS x = boxS y ↔ x = y := by
  constructor
  · intro h
    simp only [boxS, interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at h
    exact go.intoVal_inj h
  · rintro rfl; rfl

/-- An `Op` value determines its fields (its fields' loads are deterministic). -/
instance op_intoValInj : go.IntoValInj LOp where
  intoVal_inj x y h := by
    have hp : ∀ z : LOp, is_go_step_pure (StructFieldGet
        github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact.Op.underlying go!"Put")
        #z = Eq (Val #(z.Put')) := fun z =>
      (github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact.Op.TypeAssumptions.get_Put
        z).isGoStep_det_internal.isGoStep_pure_det
    have hv : ∀ z : LOp, is_go_step_pure (StructFieldGet
        github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact.Op.underlying go!"Val")
        #z = Eq (Val #(z.Val')) := fun z =>
      (github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact.Op.TypeAssumptions.get_Val
        z).isGoStep_det_internal.isGoStep_pure_det
    have e1 := hp x
    rw [h, hp y] at e1
    have e2 := hv x
    rw [h, hv y] at e2
    have f1 : Val #(x.Put') = Val #(y.Put') := by
      have := congrFun e1 (Val #(x.Put')); simp only [eq_iff_iff, iff_true] at this; exact this.symm
    have f2 : Val #(x.Val') = Val #(y.Val') := by
      have := congrFun e2 (Val #(x.Val')); simp only [eq_iff_iff, iff_true] at this; exact this.symm
    injection f1 with f1
    injection f2 with f2
    cases x; cases y
    simp only [github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact.Op.mk.injEq]
    exact ⟨GoGlobalContext.intoVal_inj_bool f1, go.intoVal_inj f2⟩

theorem boxOp_inj (a b : LOp) : boxOp a = boxOp b ↔ a = b := by
  constructor
  · intro h
    simp only [boxOp, interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at h
    exact go.intoVal_inj h
  · rintro rfl; rfl

theorem putVal_boxOp (b : Bool) (v : GoString) :
    putVal (boxOp ⟨b, v⟩) = if b then some v else none := by
  unfold putVal
  split
  · rename_i h
    have hc := h.choose_spec
    rw [boxOp_inj] at hc
    simp only [github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact.Op.mk.injEq] at hc
    obtain ⟨rfl, hv⟩ := hc
    simp only [ite_true]
    exact congrArg some hv.symm
  · rename_i h
    cases b
    · rfl
    · exact absurd ⟨v, rfl⟩ h

/-- The model on a write. -/
theorem regStep_put (s v : GoString) (o : GoInterface) :
    regStep s (boxOp ⟨true, v⟩, o) = some v := by
  unfold regStep
  rw [putVal_boxOp]
  rfl

/-- The model on a read with output `boxS x`. -/
theorem regStep_get (s v x : GoString) :
    regStep s (boxOp ⟨false, v⟩, boxS x) = if x = s then some s else none := by
  unfold regStep
  rw [putVal_boxOp]
  simp only [Bool.false_eq_true, ite_false, boxS_inj]

end inj

section addrs
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- The address of `s.mu`. -/
abbrev muAddr (s : Loc) : Loc :=
  structFieldRef github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact.Server go!"mu" s
/-- The address of `s.cond`. -/
abbrev condAddr (s : Loc) : Loc :=
  structFieldRef github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact.Server go!"cond" s
/-- The address of `s.log`. -/
abbrev logAddr (s : Loc) : Loc :=
  structFieldRef github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact.Server go!"log" s
/-- The address of `s.start`. -/
abbrev startAddr (s : Loc) : Loc :=
  structFieldRef github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact.Server go!"start" s
/-- The address of `s.applied`. -/
abbrev appliedAddr (s : Loc) : Loc :=
  structFieldRef github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact.Server go!"applied" s
/-- The address of `s.state`. -/
abbrev stateAddr (s : Loc) : Loc :=
  structFieldRef github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact.Server go!"state" s

/-- The `Locker` the condition variable was made with: `&s.mu`. -/
abbrev muLocker (s : Loc) : GoInterfaceOk :=
  interface.mk (go.GoType.PointerType sync.Mutex.ty) #(muAddr s)

end addrs

/-- A request in the log: the value written, the name of the writer's saved postcondition and
the name of its ticket. -/
abbrev Req [GooseExts] := GoString × GName × GName

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact.Assumptions]

/-- The register's porcupine model specification (see the file header). -/
def regS : ModelSpec GF GoString where
  M := regM
  rep _ v s := iprop(⌜v = boxS s⌝)
  ioOk i o := iprop(⌜∃ b v, i = boxOp ⟨b, v⟩ ∧ (b = false → ∃ x, o = boxS x)⌝)
  ioOk_pers _ _ := by infer_instance

/-- The register's inputs: boxed `Op`s (the driver's `inOk`). -/
abbrev regInOk (i : GoInterface) : IProp GF := iprop(⌜∃ b v, i = boxOp ⟨b, v⟩⌝)

/-- **The register's abstract state is `v`.** -/
def regState (γ : GName) (v : GoString) : IProp GF := ghostVar γ (1 : Qp).half v

instance regState_timeless (γ : GName) (v : GoString) : Timeless (regState (GF := GF) γ v) := by
  unfold regState; infer_instance

/-- A writer's atomic update, as the lock invariant keeps it: it takes the register from any
state to `v`, giving `P`. -/
def regAu (γ : GName) (v : GoString) (P : IProp GF) : IProp GF :=
  iprop(|={⊤, ∅}=> ∃ x, regState γ x ∗ (regState γ v -∗ |={∅, ⊤}=> P))

/-- A pending request: its writer's atomic update, with the postcondition it saved. -/
def pendSlot (γ : GName) (r : Req) : IProp GF :=
  iprop(∃ P : IProp GF, savedPropOwn r.2.1 DFrac.discard P ∗ regAu γ r.1 P)

/-- A done request: its writer's postcondition, until the writer takes it with its ticket. -/
def doneSlot (r : Req) : IProp GF :=
  iprop(∃ P : IProp GF, savedPropOwn r.2.1 DFrac.discard P ∗ (P ∨ token r.2.2))

/-- The lock invariant of `s.mu` (see the file header). -/
def logkvcompactR (γ γr : GName) (s : Loc) : IProp GF :=
  iprop(∃ (sl : GoSlice) (rs : List Req) (b a : w64) (st : GoString),
    logAddr s ↦ sl ∗ sl ↦* (rs.drop (uint.nat b)).map Prod.fst ∗
    ownSliceCap GoString sl (DFrac.own 1) ∗
    startAddr s ↦ b ∗ appliedAddr s ↦ a ∗ stateAddr s ↦ st ∗
    ghostVar γ (1 : Qp).half st ∗ monoListAuthOwn γr 1 rs ∗ ⧗ rs.length ∗
    ⌜uint.nat b ≤ uint.nat a ∧ uint.nat a ≤ rs.length ∧ rs.length < 2 ^ 64⌝ ∗
    ([∗list] r ∈ rs.take (uint.nat a), doneSlot r) ∗
    ([∗list] r ∈ rs.drop (uint.nat a), pendSlot γ r))

/-- **The server `s` serves the register `γ`** (persistent): its condition variable (fixed
after `New`) over its mutex, and the mutex with its lock invariant; and the executions are
shorter than `2^64` steps (`receiptBound GF ≤ 2^64`), so the count of writes does not wrap. -/
def isServer (γ : GName) (s : Loc) : IProp GF :=
  iprop(∃ (γr : GName) (c : Loc), ⌜receiptBound GF ≤ 2 ^ 64⌝ ∗ condAddr s ↦□ c ∗ sync.isCond c (muLocker s) ∗
    sync.isMutex (muAddr s) (logkvcompactR γ γr s))

instance isServer_persistent (γ : GName) (s : Loc) : Persistent (isServer (GF := GF) γ s) := by
  unfold isServer; infer_instance

end defs

end logkvcompact
end lintest
end EtcdGrove

end Perennial
