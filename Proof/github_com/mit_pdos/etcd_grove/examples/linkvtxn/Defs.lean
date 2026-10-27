/-
Lean-first (no Rocq counterpart).

# linkvtxn: the model's vocabulary (linkv-txn stage E)

What `Model.spec` is stated in (as `linkv/Defs.lean` for `examples/linkv`):

- `boxIn x`, `boxOut y`, `boxSt sl`: a Go `Input`, `Output`, `state` boxed (`any(x)`);
- `decIO x y`: the model's operation of an input and its output (`Abs.lean`'s `decIn` and
  `decOut`); `decOp`, the model's decoder of porcupine's operations (`decIO` of a boxed `Input`
  and `Output`, `decOp_box`; any other pair is no operation);
- `storeOwn s g`, `cfgOwn c g`: the Go store `s`'s entries hold `g`'s, the configuration `c`'s
  store and pending inputs hold `g`'s, read-only (configurations share slices: `step` returns
  `c.st` in a new configuration);
- `stRepB n v S`: a Go state value (a boxed `state`, its slice and configurations read-only) whose
  configurations `gs` represent `S` (`GOk gs S`), each `Bounded n`;
- `linkvtxnS`, the model's `ModelSpec`: `pM TS decOp`, `rep k` = `stRepB (k + 1)` (a value made by
  `k` steps), and `ioOk i o` (a boxed `Input` that `Gen` may return, `ValidIn`, and a boxed
  `Output`: what `Step`'s type assertions and the model's decoder need).

`Input_intoVal_inj`/`Output_intoVal_inj`: a struct's `intoVal` is injective, from the
translation's field projections (`get_Kind`, ...: a deterministic pure step from `#x` to `#x.f`),
which Perennial does not state for structs (`GoGlobalContext` states it of the basic types).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Steps
public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI Iris.ProgramLogic github_com.mit_pdos.etcd_grove.examples.linkvtxn

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

/-- The input `x`, boxed (`any(x)`). -/
abbrev boxIn (x : Input) : GoInterface := interface.mkOk Input.ty #x

/-- The output `y`, boxed (`any(y)`). -/
abbrev boxOut (y : Output) : GoInterface := interface.mkOk Output.ty #y

/-- The state slice `sl`, boxed (`any(state(sl))`). -/
abbrev boxSt (sl : GoSlice) : GoInterface := interface.mkOk state.ty #sl

/-- The model's operation of an input and its output. -/
def decIO (x : Input) (y : Output) : Option (MI × linkv.Ans MO) :=
  (decIn x).map fun i => (i, decOut x.Kind' y)

open Classical in
/-- The model's decoder of porcupine's operations (see the file header). -/
def decOp (io : github_com.anishathalye.porcupine.OpV) : Option (MI × linkv.Ans MO) :=
  if h : ∃ p : Input × Output, io = (boxIn p.1, boxOut p.2) then decIO h.choose.1 h.choose.2
  else none

/-- Two values with a field's deterministic projection have equal projections. -/
theorem proj_eq {t : Tag} {f : GoInstruction} {a b : val} {ea eb : Expr}
    (ha : go.IsGoStepPureDetTagged t f a ea) (hb : go.IsGoStepPureDetTagged t f b eb)
    (h : a = b) : ea = eb := by
  have h1 := ha.isGoStep_det_internal.isGoStep_pure_det
  have h2 := hb.isGoStep_det_internal.isGoStep_pure_det
  subst h
  rw [h2] at h1
  exact cast (congrFun h1 eb) rfl

include sem package_sem in
theorem VR_intoVal_inj : Function.Injective (intoVal (V := VR)) := by
  intro x y h
  have h : (#x : val) = #y := h
  have e1 := go.intoVal_inj (Expr.Val.inj
    (proj_eq (VR.TypeAssumptions.get_Val x) (VR.TypeAssumptions.get_Val y) h))
  have e2 := go.intoVal_inj (Expr.Val.inj
    (proj_eq (VR.TypeAssumptions.get_Mod x) (VR.TypeAssumptions.get_Mod y) h))
  have e3 := go.intoVal_inj (Expr.Val.inj
    (proj_eq (VR.TypeAssumptions.get_Ver x) (VR.TypeAssumptions.get_Ver y) h))
  cases x; cases y; simp_all

include sem package_sem in
theorem Cmp_intoVal_inj : Function.Injective (intoVal (V := Cmp)) := by
  intro x y h
  have h : (#x : val) = #y := h
  have e1 := go.intoVal_inj (Expr.Val.inj
    (proj_eq (Cmp.TypeAssumptions.get_Kind x) (Cmp.TypeAssumptions.get_Kind y) h))
  have e2 := go.intoVal_inj (Expr.Val.inj
    (proj_eq (Cmp.TypeAssumptions.get_Key x) (Cmp.TypeAssumptions.get_Key y) h))
  have e3 := go.intoVal_inj (Expr.Val.inj
    (proj_eq (Cmp.TypeAssumptions.get_Val x) (Cmp.TypeAssumptions.get_Val y) h))
  have e4 := go.intoVal_inj (Expr.Val.inj
    (proj_eq (Cmp.TypeAssumptions.get_Num x) (Cmp.TypeAssumptions.get_Num y) h))
  cases x; cases y; simp_all

include sem package_sem in
theorem TOp_intoVal_inj : Function.Injective (intoVal (V := TOp)) := by
  intro x y h
  have h : (#x : val) = #y := h
  have e1 := go.intoVal_inj (Expr.Val.inj
    (proj_eq (TOp.TypeAssumptions.get_Kind x) (TOp.TypeAssumptions.get_Kind y) h))
  have e2 := go.intoVal_inj (Expr.Val.inj
    (proj_eq (TOp.TypeAssumptions.get_Key x) (TOp.TypeAssumptions.get_Key y) h))
  have e3 := go.intoVal_inj (Expr.Val.inj
    (proj_eq (TOp.TypeAssumptions.get_Val x) (TOp.TypeAssumptions.get_Val y) h))
  cases x; cases y; simp_all

include sem package_sem in
theorem TRes_intoVal_inj : Function.Injective (intoVal (V := TRes)) := by
  intro x y h
  have h : (#x : val) = #y := h
  have e1 := go.intoVal_inj (Expr.Val.inj
    (proj_eq (TRes.TypeAssumptions.get_Kind x) (TRes.TypeAssumptions.get_Kind y) h))
  have e2 := GoGlobalContext.intoVal_inj_bool (Expr.Val.inj
    (proj_eq (TRes.TypeAssumptions.get_Found x) (TRes.TypeAssumptions.get_Found y) h))
  have e3 := VR_intoVal_inj (sem := sem) (package_sem := package_sem) (Expr.Val.inj
    (proj_eq (TRes.TypeAssumptions.get_R x) (TRes.TypeAssumptions.get_R y) h))
  have e4 := go.intoVal_inj (Expr.Val.inj
    (proj_eq (TRes.TypeAssumptions.get_N x) (TRes.TypeAssumptions.get_N y) h))
  cases x; cases y; simp_all

include sem package_sem in
theorem KV_intoVal_inj : Function.Injective (intoVal (V := KV)) := by
  intro x y h
  have h : (#x : val) = #y := h
  have e1 := go.intoVal_inj (Expr.Val.inj
    (proj_eq (KV.TypeAssumptions.get_Key x) (KV.TypeAssumptions.get_Key y) h))
  have e2 := VR_intoVal_inj (sem := sem) (package_sem := package_sem) (Expr.Val.inj
    (proj_eq (KV.TypeAssumptions.get_R x) (KV.TypeAssumptions.get_R y) h))
  cases x; cases y; simp_all

include sem package_sem in
theorem Input_intoVal_inj : Function.Injective (intoVal (V := Input)) := by
  intro x y h
  have h : (#x : val) = #y := h
  have e1 := go.intoVal_inj (Expr.Val.inj
    (proj_eq (Input.TypeAssumptions.get_Kind x) (Input.TypeAssumptions.get_Kind y) h))
  have e2 := go.intoVal_inj (Expr.Val.inj
    (proj_eq (Input.TypeAssumptions.get_Key x) (Input.TypeAssumptions.get_Key y) h))
  have e3 := go.intoVal_inj (Expr.Val.inj
    (proj_eq (Input.TypeAssumptions.get_Val x) (Input.TypeAssumptions.get_Val y) h))
  have e4 := go.intoVal_inj (Expr.Val.inj
    (proj_eq (Input.TypeAssumptions.get_NCmps x) (Input.TypeAssumptions.get_NCmps y) h))
  have e5 := Cmp_intoVal_inj (sem := sem) (package_sem := package_sem) (Expr.Val.inj
    (proj_eq (Input.TypeAssumptions.get_Cmp0 x) (Input.TypeAssumptions.get_Cmp0 y) h))
  have e6 := go.intoVal_inj (Expr.Val.inj
    (proj_eq (Input.TypeAssumptions.get_NThen x) (Input.TypeAssumptions.get_NThen y) h))
  have e7 := TOp_intoVal_inj (sem := sem) (package_sem := package_sem) (Expr.Val.inj
    (proj_eq (Input.TypeAssumptions.get_Then0 x) (Input.TypeAssumptions.get_Then0 y) h))
  have e8 := TOp_intoVal_inj (sem := sem) (package_sem := package_sem) (Expr.Val.inj
    (proj_eq (Input.TypeAssumptions.get_Then1 x) (Input.TypeAssumptions.get_Then1 y) h))
  have e9 := TOp_intoVal_inj (sem := sem) (package_sem := package_sem) (Expr.Val.inj
    (proj_eq (Input.TypeAssumptions.get_Then2 x) (Input.TypeAssumptions.get_Then2 y) h))
  have e10 := go.intoVal_inj (Expr.Val.inj
    (proj_eq (Input.TypeAssumptions.get_NElse x) (Input.TypeAssumptions.get_NElse y) h))
  have e11 := TOp_intoVal_inj (sem := sem) (package_sem := package_sem) (Expr.Val.inj
    (proj_eq (Input.TypeAssumptions.get_Else0 x) (Input.TypeAssumptions.get_Else0 y) h))
  cases x; cases y; simp_all

include sem package_sem in
theorem Output_intoVal_inj : Function.Injective (intoVal (V := Output)) := by
  intro x y h
  have h : (#x : val) = #y := h
  have e1 := GoGlobalContext.intoVal_inj_bool (Expr.Val.inj
    (proj_eq (Output.TypeAssumptions.get_Err x) (Output.TypeAssumptions.get_Err y) h))
  have e2 := go.intoVal_inj (Expr.Val.inj
    (proj_eq (Output.TypeAssumptions.get_Rev x) (Output.TypeAssumptions.get_Rev y) h))
  have e3 := GoGlobalContext.intoVal_inj_bool (Expr.Val.inj
    (proj_eq (Output.TypeAssumptions.get_Found x) (Output.TypeAssumptions.get_Found y) h))
  have e4 := VR_intoVal_inj (sem := sem) (package_sem := package_sem) (Expr.Val.inj
    (proj_eq (Output.TypeAssumptions.get_R x) (Output.TypeAssumptions.get_R y) h))
  have e5 := go.intoVal_inj (Expr.Val.inj
    (proj_eq (Output.TypeAssumptions.get_N x) (Output.TypeAssumptions.get_N y) h))
  have e6 := GoGlobalContext.intoVal_inj_bool (Expr.Val.inj
    (proj_eq (Output.TypeAssumptions.get_Ok x) (Output.TypeAssumptions.get_Ok y) h))
  have e7 := go.intoVal_inj (Expr.Val.inj
    (proj_eq (Output.TypeAssumptions.get_NRes x) (Output.TypeAssumptions.get_NRes y) h))
  have e8 := TRes_intoVal_inj (sem := sem) (package_sem := package_sem) (Expr.Val.inj
    (proj_eq (Output.TypeAssumptions.get_Res0 x) (Output.TypeAssumptions.get_Res0 y) h))
  have e9 := TRes_intoVal_inj (sem := sem) (package_sem := package_sem) (Expr.Val.inj
    (proj_eq (Output.TypeAssumptions.get_Res1 x) (Output.TypeAssumptions.get_Res1 y) h))
  have e10 := TRes_intoVal_inj (sem := sem) (package_sem := package_sem) (Expr.Val.inj
    (proj_eq (Output.TypeAssumptions.get_Res2 x) (Output.TypeAssumptions.get_Res2 y) h))
  have e11 := go.intoVal_inj (Expr.Val.inj
    (proj_eq (Output.TypeAssumptions.get_NKVs x) (Output.TypeAssumptions.get_NKVs y) h))
  have e12 := KV_intoVal_inj (sem := sem) (package_sem := package_sem) (Expr.Val.inj
    (proj_eq (Output.TypeAssumptions.get_KV0 x) (Output.TypeAssumptions.get_KV0 y) h))
  have e13 := KV_intoVal_inj (sem := sem) (package_sem := package_sem) (Expr.Val.inj
    (proj_eq (Output.TypeAssumptions.get_KV1 x) (Output.TypeAssumptions.get_KV1 y) h))
  have e14 := KV_intoVal_inj (sem := sem) (package_sem := package_sem) (Expr.Val.inj
    (proj_eq (Output.TypeAssumptions.get_KV2 x) (Output.TypeAssumptions.get_KV2 y) h))
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

/-- A Go store holds `g` (see the file header). -/
def storeOwn (s : store) (g : GSt) : IProp GF := iprop(s.kvs' ↦*□ g.kvs ∗ ⌜s.rev' = g.rev⌝)

instance storeOwn_persistent (s : store) (g : GSt) : Persistent (storeOwn (GF := GF) s g) := by
  unfold storeOwn; infer_instance

/-- A Go configuration holds `g` (see the file header). -/
def cfgOwn (c : mcfg) (g : GCfg) : IProp GF := iprop(storeOwn c.st' g.st ∗ c.pend' ↦*□ g.pend)

instance cfgOwn_persistent (c : mcfg) (g : GCfg) : Persistent (cfgOwn (GF := GF) c g) := by
  unfold cfgOwn; infer_instance

/-- A Go state value represents `S`, its configurations `Bounded n` (see the file header). -/
def stRepB (n : Nat) (v : GoInterface) (S : linkv.PSet MS MI) : IProp GF :=
  iprop(∃ (sl : GoSlice) (cs : List mcfg) (gs : List GCfg),
    ⌜v = boxSt sl ∧ GOk gs S ∧ ∀ g ∈ gs, Bounded n g⌝ ∗ sl ↦*□ cs ∗
      [∗list] c;g ∈ cs;gs, cfgOwn c g)

instance stRepB_persistent (n : Nat) (v : GoInterface) (S : linkv.PSet MS MI) :
    Persistent (stRepB (GF := GF) n v S) := by
  unfold stRepB; infer_instance

/-- **The model's specification** (see the file header). -/
def linkvtxnS : github_com.anishathalye.porcupine.ModelSpec GF (linkv.PSet MS MI) where
  M := linkv.pM TS decOp
  rep k := stRepB (k + 1)
  ioOk i o := iprop(⌜∃ x y, i = boxIn x ∧ o = boxOut y ∧ ValidIn x⌝)
  ioOk_pers _ _ := by infer_instance

end defs

end linkvtxn
end EtcdGrove
end Perennial
