/-
Lean-first (no Rocq counterpart).

# linkv: the instance's vocabulary for `lintest` (2026-10-19)

What the `lintest` driver's specs (`Proof/.../examples/lintest/Defs.lean`: `genSpec`,
`applySpec`) are instantiated with for `examples/linkv`:

- `boxIn x`: the Go input `x : Input` as the driver passes it, `any(x)`;
- `genKeys`, `genVals`: the keys and values `Gen` picks from (its local slices);
- `GenInput x`: `x` is an input `Gen` may return: its key one of `genKeys` and, for a put, its
  value one of `genVals`;
- `linkvInOk i`: the driver's `inOk`: `i` is a boxed `Input` that `Gen` may return. `Gen`
  returns only such inputs (`Gen.spec`); `Apply` may assume one (its `input.(Input)` cannot
  panic, and the key is one of three short, non-empty strings).

And the model's (`Model.spec`): `boxOut y`, `boxSt sl` (a boxed `Output`, a boxed `state`);
`decOp`, the model's decoder of porcupine's operations (`ModelLemmas.lean`'s `decIO` of a boxed
`Input` and `Output`, `decOp_box`; any other pair is no operation); `cfgOwn c g` (the Go
configuration `c`'s two slices hold `g`, read-only: configurations share slices, `step` returns
`c.kv` in a new configuration); `stRep v S` (a Go state value: a boxed `state`, its slice and
configurations read-only, whose contents `gs` represent `S`, `GOk gs S`); and `linkvS`, the
model's `ModelSpec`: `kvM decOp`, `stRep`, and `ioOk i o` (a boxed `Input` and a boxed `Output`,
what `Step`'s type assertions need).

`Input_intoVal_inj`/`Output_intoVal_inj`: a struct's `intoVal` is injective, from the
translation's field projections (`get_Put`, ...: a deterministic pure step from `#x` to `#x.f`),
which Perennial does not state for structs (`GoGlobalContext` states it of the basic types).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv.ModelLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv

open Iris Iris.BI Iris.ProgramLogic github_com.mit_pdos.etcd_grove.examples.linkv

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv.Assumptions]

/-- The input `x`, boxed (`any(x)`). -/
abbrev boxIn (x : Input) : GoInterface := interface.mkOk Input.ty #x

/-- The keys `Gen` picks from. -/
abbrev genKeys : List GoString := [go!"k0", go!"k1", go!"k2"]

/-- The values `Gen` picks from. -/
abbrev genVals : List GoString := [go!"a", go!"b", go!"c", go!"d"]

/-- An input `Gen` may return. -/
def GenInput (x : Input) : Prop := x.Key' ∈ genKeys ∧ (x.Put' = true → x.Val' ∈ genVals)

/-- The driver's `inOk` (see the file header). -/
abbrev linkvInOk (i : GoInterface) : IProp GF := iprop(⌜∃ x : Input, i = boxIn x ∧ GenInput x⌝)

/-- The output `y`, boxed (`any(y)`). -/
abbrev boxOut (y : Output) : GoInterface := interface.mkOk Output.ty #y

/-- The state slice `sl`, boxed (`any(state(sl))`). -/
abbrev boxSt (sl : GoSlice) : GoInterface := interface.mkOk state.ty #sl

open Classical in
/-- The model's decoder of porcupine's operations (see the file header). -/
def decOp (io : github_com.anishathalye.porcupine.OpV) :
    Option (KVIn GoString GoString × KVOut GoString) :=
  if h : ∃ p : Input × Output, io = (boxIn p.1, boxOut p.2) then decIO h.choose.1 h.choose.2
  else none

include sem package_sem in
theorem Input_intoVal_inj : Function.Injective (intoVal (V := Input)) := by
  intro x y h
  have hP := (Input.TypeAssumptions.get_Put x).isGoStep_det_internal.isGoStep_pure_det
  have hK := (Input.TypeAssumptions.get_Key x).isGoStep_det_internal.isGoStep_pure_det
  have hV := (Input.TypeAssumptions.get_Val x).isGoStep_det_internal.isGoStep_pure_det
  have hP' := (Input.TypeAssumptions.get_Put y).isGoStep_det_internal.isGoStep_pure_det
  have hK' := (Input.TypeAssumptions.get_Key y).isGoStep_det_internal.isGoStep_pure_det
  have hV' := (Input.TypeAssumptions.get_Val y).isGoStep_det_internal.isGoStep_pure_det
  have h : (#x : val) = #y := h
  rw [h, hP'] at hP; rw [h, hK'] at hK; rw [h, hV'] at hV
  have e1 := cast (congrFun hP (#y.Put')) rfl
  have e2 := cast (congrFun hK (#y.Key')) rfl
  have e3 := cast (congrFun hV (#y.Val')) rfl
  have := go.intoVal_inj (Expr.Val.inj e1)
  have := go.intoVal_inj (Expr.Val.inj e2)
  have := go.intoVal_inj (Expr.Val.inj e3)
  cases x; cases y; simp_all

include sem package_sem in
theorem Output_intoVal_inj : Function.Injective (intoVal (V := Output)) := by
  intro x y h
  have hP := (Output.TypeAssumptions.get_Err x).isGoStep_det_internal.isGoStep_pure_det
  have hK := (Output.TypeAssumptions.get_Found x).isGoStep_det_internal.isGoStep_pure_det
  have hV := (Output.TypeAssumptions.get_Val x).isGoStep_det_internal.isGoStep_pure_det
  have hP' := (Output.TypeAssumptions.get_Err y).isGoStep_det_internal.isGoStep_pure_det
  have hK' := (Output.TypeAssumptions.get_Found y).isGoStep_det_internal.isGoStep_pure_det
  have hV' := (Output.TypeAssumptions.get_Val y).isGoStep_det_internal.isGoStep_pure_det
  have h : (#x : val) = #y := h
  rw [h, hP'] at hP; rw [h, hK'] at hK; rw [h, hV'] at hV
  have e1 := cast (congrFun hP (#y.Err')) rfl
  have e2 := cast (congrFun hK (#y.Found')) rfl
  have e3 := cast (congrFun hV (#y.Val')) rfl
  have := go.intoVal_inj (Expr.Val.inj e1)
  have := GoGlobalContext.intoVal_inj_bool (Expr.Val.inj e2)
  have := go.intoVal_inj (Expr.Val.inj e3)
  cases x; cases y; simp_all

include sem package_sem in
/-- The decoder of a boxed input and output. -/
theorem decOp_box (x : Input) (y : Output) : decOp (boxIn x, boxOut y) = decIO x y := by
  have h : ∃ p : Input × Output, (boxIn x, boxOut y) = (boxIn p.1, boxOut p.2) := ⟨(x, y), rfl⟩
  unfold decOp
  rw [dif_pos h]
  have hs : (boxIn x, boxOut y) = (boxIn h.choose.1, boxOut h.choose.2) := h.choose_spec
  have h1 := (GoInterfaceOk.mk.inj (GoInterface.ok.inj (congrArg Prod.fst hs))).2
  have h2 := (GoInterfaceOk.mk.inj (GoInterface.ok.inj (congrArg Prod.snd hs))).2
  have e : h.choose = (x, y) :=
    Prod.ext (Input_intoVal_inj (sem := sem) (package_sem := package_sem) h1).symm
      (Output_intoVal_inj (sem := sem) (package_sem := package_sem) h2).symm
  rw [e]

/-- A Go configuration holds `g` (see the file header). -/
def cfgOwn (c : kvConfig) (g : GCfg) : IProp GF := iprop(c.kv' ↦*□ g.kv ∗ c.pend' ↦*□ g.pend)

instance cfgOwn_persistent (c : kvConfig) (g : GCfg) : Persistent (cfgOwn (GF := GF) c g) := by
  unfold cfgOwn; infer_instance

/-- A Go state value represents `S` (see the file header). -/
def stRep (v : GoInterface) (S : KVSet GoString GoString) : IProp GF :=
  iprop(∃ (sl : GoSlice) (cs : List kvConfig) (gs : List GCfg),
    ⌜v = boxSt sl ∧ GOk gs S⌝ ∗ sl ↦*□ cs ∗ [∗list] c;g ∈ cs;gs, cfgOwn c g)

instance stRep_persistent (v : GoInterface) (S : KVSet GoString GoString) :
    Persistent (stRep (GF := GF) v S) := by
  unfold stRep; infer_instance

/-- **The model's specification** (see the file header). -/
def linkvS : github_com.anishathalye.porcupine.ModelSpec GF (KVSet GoString GoString) where
  M := kvM decOp
  rep := stRep
  ioOk i o := iprop(⌜∃ x y, i = boxIn x ∧ o = boxOut y⌝)
  ioOk_pers _ _ := by infer_instance

end defs

end linkv
end EtcdGrove
end Perennial
