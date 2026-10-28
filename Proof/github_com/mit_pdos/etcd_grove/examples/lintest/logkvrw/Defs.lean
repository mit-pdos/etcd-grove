/-
Lean-first (no Rocq counterpart).

# lintest/logkvrw: the register's model, its abstract state and the server's lock invariant (2026-10-28)

`examples/lintest/logkvrw/logkvrw.go` is a register whose writes go through a log: `Put` appends
its value to the log under the write lock of a read-write mutex and waits until the apply
goroutine (`applyLoop`) has applied it; `Get` reads the applied state under the read lock.
`Check` runs the lintest driver on it.

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
would have. Nothing in them mentions the log. `Get` takes the calling goroutine's thread token
(`threadTok`) and gives it back: the read lock needs one of the `RWMutex`'s bounded reader
tokens, which the server's thread pool lends for it (`Perennial/Proof/sync/RWMutexThreads.lean`).

## The read-write lock (`rdR`, `wInv`)

Perennial's guarded `RWMutex` protects a fractional `P q` (`rdR γ γb s q`): `RLock` gives
`P rfrac`, `Lock` gives `P 1`. A reader needs only `s.state` and the lock's half of `γ` (to
agree with the register's state at its linearization point), so `rdR` holds those, fractionally,
and the half `γb` at `false` ("the writer's part is in `wInv`"). The rest of the base's lock
invariant (the log, `applied`, the requests and their slots: `wrR`) is not fractional (the
slots hold atomic updates and postconditions), so it is in an invariant (`wInv`) which a writer
empties when it locks (flipping `γb` to `true`, with `rdR 1`'s half) and fills back before it
unlocks. While it holds the write lock, a writer holds the base's whole lock invariant,
`logkvrwR`, with the write lock `wLocked` (the lock's token and `γb`'s half at `true`):
`WLock.lean` gives `Lock`/`Unlock` and the condition variable's `Locker` in these terms, so the
writers' proofs are the base's.

## The lock invariant (`logkvrwR γ s`), as the writers hold it

The write lock guards the log `s.log`, the applied count `s.applied` and the state `s.state`. The
log is a list of requests `rs` (`Req`: the value, the name of the writer's saved postcondition
and the name of its ticket), recorded in a monotone ghost list `γr` (a writer keeps a
persistent witness of its request's index). The state is the other half of `γ`. The first
`applied` requests are done (`doneSlot`): the writer's postcondition `P` waits there until the
writer takes it, leaving its ticket. The others are pending (`pendSlot`): each holds its
writer's atomic update (`regAu`), a fancy update that takes the register to its value and gives
back the postcondition `P`. `applyLoop` fires it when it applies the entry (the linearization
point of `Put`, in the apply goroutine), and moves the slot from pending to done; the writer,
woken once `applied` passes its index, collects `P`: the saved proposition (`savedPropOwn`,
discarded) says it is its own (`▷ (P ≡ P')`), the ticket (`token`) that it was not taken yet.
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw
public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.Defs
public import Perennial.Proof.sync.CondDefs
public import Perennial.Proof.sync.RWMutexThreads
public import Perennial.Ghost.SavedProp
public import Perennial.Ghost.MonoList
public import Perennial.Ghost.Token

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw.Assumptions]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw :=
  build_get_is_pkg_init_wf

end init

end github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw

namespace EtcdGrove
namespace lintest
namespace logkvrw

open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

/-- The Go struct `Op`. -/
abbrev LOp [GooseExts] := github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw.Op

section model
variable [GooseExts] [go_gctx : GoGlobalContext]

/-- The boxed `string` `x` (`any(x)`). -/
abbrev boxS (x : GoString) : GoInterface := interface.mkOk go.string #x

/-- The boxed `Op` `o` (`any(o)`). -/
abbrev boxOp (o : LOp) : GoInterface :=
  interface.mkOk github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw.Op.ty #o

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw.Assumptions]

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
        github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw.Op.underlying go!"Put")
        #z = Eq (Val #(z.Put')) := fun z =>
      (github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw.Op.TypeAssumptions.get_Put
        z).isGoStep_det_internal.isGoStep_pure_det
    have hv : ∀ z : LOp, is_go_step_pure (StructFieldGet
        github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw.Op.underlying go!"Val")
        #z = Eq (Val #(z.Val')) := fun z =>
      (github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw.Op.TypeAssumptions.get_Val
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
    simp only [github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw.Op.mk.injEq]
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
    simp only [github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw.Op.mk.injEq] at hc
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
  structFieldRef github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw.Server go!"mu" s
/-- The address of `s.cond`. -/
abbrev condAddr (s : Loc) : Loc :=
  structFieldRef github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw.Server go!"cond" s
/-- The address of `s.log`. -/
abbrev logAddr (s : Loc) : Loc :=
  structFieldRef github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw.Server go!"log" s
/-- The address of `s.applied`. -/
abbrev appliedAddr (s : Loc) : Loc :=
  structFieldRef github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw.Server go!"applied" s
/-- The address of `s.state`. -/
abbrev stateAddr (s : Loc) : Loc :=
  structFieldRef github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw.Server go!"state" s

/-- The `Locker` the condition variable was made with: `&s.mu` (a `*RWMutex`, whose
`Lock`/`Unlock` are the write lock's). -/
abbrev muLocker (s : Loc) : GoInterfaceOk :=
  interface.mk (go.GoType.PointerType sync.RWMutex.ty) #(muAddr s)

end addrs

/-- A request in the log: the value written, the name of the writer's saved postcondition and
the name of its ticket. -/
abbrev Req [GooseExts] := GoString × GName × GName

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw.Assumptions]

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
def logkvrwR (γ γr : GName) (s : Loc) : IProp GF :=
  iprop(∃ (sl : GoSlice) (rs : List Req) (a : w64) (st : GoString),
    logAddr s ↦ sl ∗ sl ↦* rs.map Prod.fst ∗ ownSliceCap GoString sl (DFrac.own 1) ∗
    appliedAddr s ↦ a ∗ stateAddr s ↦ st ∗
    ghostVar γ (1 : Qp).half st ∗ monoListAuthOwn γr 1 rs ∗
    ⌜uint.nat a ≤ rs.length⌝ ∗
    ([∗list] r ∈ rs.take (uint.nat a), doneSlot r) ∗
    ([∗list] r ∈ rs.drop (uint.nat a), pendSlot γ r))

/-- The writer's part of the lock invariant: the log, `applied` and the requests' slots (the
base's `logkvrwR` without the state, see the file header). -/
def wrR (γ γr : GName) (s : Loc) : IProp GF :=
  iprop(∃ (sl : GoSlice) (rs : List Req) (a : w64),
    logAddr s ↦ sl ∗ sl ↦* rs.map Prod.fst ∗ ownSliceCap GoString sl (DFrac.own 1) ∗
    appliedAddr s ↦ a ∗ monoListAuthOwn γr 1 rs ∗
    ⌜uint.nat a ≤ rs.length⌝ ∗
    ([∗list] r ∈ rs.take (uint.nat a), doneSlot r) ∗
    ([∗list] r ∈ rs.drop (uint.nat a), pendSlot γ r))

/-- The lock invariant splits into the writer's part and the state. -/
theorem logkvrwR_split (γ γr : GName) (s : Loc) :
    logkvrwR γ γr s ⊢
      wrR γ γr s ∗ ∃ st : GoString, stateAddr s ↦ st ∗ ghostVar γ (1 : Qp).half st := by
  iintro H
  iunfold logkvrwR at H
  icases H with ⟨%sl, %rs, %a, %st, Hlog, Hsl, Hcap, Happ, Hst, Hg, Hrs, %Ha, Hdone, Hpend⟩
  isplitl [Hlog Hsl Hcap Happ Hrs Hdone Hpend]
  · iunfold wrR
    iexists sl, rs, a
    iframe
    ipureintro; exact Ha
  · iexists st
    iframe

/-- ... and back. -/
theorem logkvrwR_join (γ γr : GName) (s : Loc) (st : GoString) :
    wrR γ γr s ∗ stateAddr s ↦ st ∗ ghostVar γ (1 : Qp).half st ⊢ logkvrwR γ γr s := by
  iintro ⟨H, Hst, Hg⟩
  iunfold wrR at H
  icases H with ⟨%sl, %rs, %a, Hlog, Hsl, Hcap, Happ, Hrs, %Ha, Hdone, Hpend⟩
  iunfold logkvrwR
  iexists sl, rs, a, st
  iframe
  ipureintro; exact Ha

/-- What the `RWMutex` guards, at fraction `q` (see the file header): the state, the lock's
half of `γ` at it, and `γb`'s half at `false`. -/
def rdR (γ γb : GName) (s : Loc) (q : Qp) : IProp GF :=
  iprop(∃ st : GoString, stateAddr s ↦{DFrac.own q} st ∗ ghostVar γ q.half st ∗
    ghostVar γb q.half false)

instance rdR_timeless (γ γb : GName) (s : Loc) (q : Qp) : Timeless (rdR (GF := GF) γ γb s q) := by
  unfold rdR; infer_instance

instance rdR_fractional (γ γb : GName) (s : Loc) : Fractional (rdR (GF := GF) γ γb s) where
  fractional q1 q2 := by
    have hpt : ∀ v : GoString, (stateAddr s ↦{DFrac.own (q1 + q2)} v : IProp GF) ⊣⊢
        stateAddr s ↦{DFrac.own q1} v ∗ stateAddr s ↦{DFrac.own q2} v :=
      fun v => (typedPointsto_dfractional (GF := GF) _ v).dfractional (DFrac.own q1) (DFrac.own q2)
    have hgv := fun (v : GoString) =>
      (ghostVar_half_fractional (GF := GF) γ v).fractional q1 q2
    have hgb := (ghostVar_half_fractional (GF := GF) γb false).fractional q1 q2
    refine ⟨?_, ?_⟩
    · iintro H
      unfold rdR
      icases H with ⟨%st, Hst, Hg, Hb⟩
      icases (hpt st).1 $$ Hst with ⟨Hst1, Hst2⟩
      icases (hgv st).1 $$ Hg with ⟨Hg1, Hg2⟩
      icases hgb.1 $$ Hb with ⟨Hb1, Hb2⟩
      isplitl [Hst1 Hg1 Hb1]
      · iexists st; iframe
      · iexists st; iframe
    · iintro ⟨H1, H2⟩
      unfold rdR
      icases H1 with ⟨%st, Hst1, Hg1, Hb1⟩
      icases H2 with ⟨%st2, Hst2, Hg2, Hb2⟩
      icombine Hg1 Hg2 gives % ⟨_, Heq⟩
      subst Heq
      iexists st
      isplitl [Hst1 Hst2]
      · iapply (hpt st).2; iframe
      isplitl [Hg1 Hg2]
      · iapply (hgv st).2; iframe
      iapply hgb.2; iframe

/-- The writer's part, unless a writer holds it (`γb` at `true`; see the file header). -/
def wInv (γ γr γb : GName) (s : Loc) : IProp GF :=
  iprop(ghostVar γb (1 : Qp).half true ∨ (ghostVar γb (1 : Qp).half false ∗ wrR γ γr s))

/-- The namespace of the server's invariants. -/
abbrev logkvrwN : Namespace := nroot.@"logkvrw"
/-- `wInv`'s namespace. -/
abbrev wN : Namespace := logkvrwN.@"w"
/-- The namespace of the reader tokens' thread pool. -/
abbrev poolN : Namespace := logkvrwN.@"pool"

/-- The write lock of `s.mu`, as the writers use it (persistent): the `RWMutex`'s guard and the
writer's part's invariant. -/
def wLock (γ γr γb : GName) (s : Loc) : IProp GF :=
  iprop(sync.isRWMutexGuard (muAddr s) (rdR γ γb s) ∗ inv wN (wInv γ γr γb s))

instance wLock_persistent (γ γr γb : GName) (s : Loc) : Persistent (wLock (GF := GF) γ γr γb s) := by
  unfold wLock; infer_instance

/-- The write lock held: the `RWMutex`'s token and `γb` at `true`. -/
def wLocked (γ γb : GName) (s : Loc) : IProp GF :=
  iprop(sync.ownRWMutexWLocked (muAddr s) (rdR γ γb s) ∗ ghostVar γb (1 : Qp).half true)

/-- **The server `s` serves the register `γ`** (persistent): its condition variable (fixed
after `New`) over its `RWMutex`'s write lock, the write lock (`wLock`), and the thread pool of
the `RWMutex`'s reader tokens. -/
def isServer (γ : GName) (s : Loc) : IProp GF :=
  iprop(∃ (γr γb γp : GName) (c : Loc), condAddr s ↦□ c ∗ sync.isCond c (muLocker s) ∗
    wLock γ γr γb s ∗
    threadPool.isThreadPool poolN γp (sync.ownRWMutex (muAddr s) (rdR γ γb s)))

instance isServer_persistent (γ : GName) (s : Loc) : Persistent (isServer (GF := GF) γ s) := by
  unfold isServer; infer_instance

end defs

end logkvrw
end lintest
end EtcdGrove

end Perennial
