/-
Lean-first (no Rocq counterpart).

# The store's porcupine model (2026-10-29)

`examples/kv`'s (`Proof/github_com/mit_pdos/etcd_grove/examples/kv/ModelDefs.lean`, whose header
explains the construction), for `examples/kvreconf/check.go`'s `Model()`: its `Input` has no
replica, and its kinds are `Put` (sets the key, answers `""`) and `Get`/`Read` (leave the store,
answer the key's value): any kind other than `opPut` is a read, as `Step` runs it.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

/-- The test's input struct. -/
abbrev KVInput [GooseExts] := github_com.mit_pdos.etcd_grove.examples.kvreconf.Input

section model
variable [GooseExts] [go_gctx : GoGlobalContext]

/-- The type `map[string]string`. -/
abbrev kvMapTy : go.GoType := go.GoType.MapType go.string go.string

/-- The boxed `Input` `x` (`any(x)`). -/
abbrev boxIn (x : KVInput) : GoInterface :=
  interface.mkOk github_com.mit_pdos.etcd_grove.examples.kvreconf.Input.ty #x

/-- The boxed string `s`. -/
abbrev boxS (s : GoString) : GoInterface := interface.mkOk go.string #s

/-- The boxed map at `l`. -/
abbrev boxM (l : Loc) : GoInterface := interface.mkOk kvMapTy #l

/-- The store after the input `x`: a `Put` sets the key, any other kind (a `Get`, a `Read`)
leaves it. -/
def inStep (x : KVInput) (s : KVMap) : KVMap :=
  if x.Kind' = opPutB then kvUpd s x.Key' x.Val' else s

/-- The output of the input `x` in the state `s`: `""` for a `Put`, the key's value otherwise. -/
def inOut (x : KVInput) (s : KVMap) : GoString := if x.Kind' = opPutB then [] else s x.Key'

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
variable [ta : github_com.mit_pdos.etcd_grove.examples.kvreconf.Input.TypeAssumptions]

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
    simp only [Expr.Val.injEq] at hk hK hv
    cases x; cases y
    simp only [KVInput, github_com.mit_pdos.etcd_grove.examples.kvreconf.Input.mk.injEq]
    exact ⟨go.intoVal_inj hk, go.intoVal_inj hK, go.intoVal_inj hv⟩
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

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]

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

end kvreconf
end EtcdGrove
end Perennial
