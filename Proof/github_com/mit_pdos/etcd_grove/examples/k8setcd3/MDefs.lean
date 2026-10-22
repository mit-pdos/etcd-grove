/-
Lean-first (no Rocq counterpart).

# The driver's model: its Go values (stage 6a)

As linkvtxn's `Defs.lean`:

- `storeOwn s g`, `cfgOwn c g`: the Go store `s`'s items hold `g`'s, the configuration `c`'s
  store and pending inputs hold `g`'s, read-only (configurations share slices: `step` returns
  `c.st` in a new configuration);
- `boxIn x`, `boxOut y`, `boxSt sl`: a Go `Input`, `Output`, `state` boxed (`any(x)`); `decOp`, the
  model's decoder of porcupine's operations (a boxed `Input` and `Output` is the input and
  `ansOf` the output, `decOp_box`; any other pair is no operation);
- `stRepB n v S`: a Go state value (a boxed `state`, its slice and configurations read-only) whose
  configurations `gs` represent `S` (`GOk`), each `Bounded n`;
- `k8setcd3S g0`, the model's `ModelSpec` from the seeded store `g0`: `pM (kSpec g0) decOp`,
  `rep k` = `stRepB (k + g0.items.length + 1)` (a value made by `k` steps), and `ioOk i o` (a
  boxed `Input` and a boxed `Output`: what `Step`'s type assertions need).

`Input_intoVal_inj`/`Output_intoVal_inj`: a struct's `intoVal` is injective, from the
translation's field projections (`proj_eq`, as linkvtxn's).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.KSteps
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8setcd3 (mstore mcfg item Input Output state)

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

/-- A Go store holds `g` (see the file header). -/
def storeOwn (s : mstore) (g : GSt) : IProp GF :=
  iprop(s.items' ↦*□ g.items ∗ ⌜s.rv' = g.rv⌝)

instance storeOwn_persistent (s : mstore) (g : GSt) : Persistent (storeOwn (GF := GF) s g) := by
  unfold storeOwn; infer_instance

/-- A Go configuration holds `g` (see the file header). -/
def cfgOwn (c : mcfg) (g : GCfg) : IProp GF := iprop(storeOwn c.st' g.st ∗ c.pend' ↦*□ g.pend)

instance cfgOwn_persistent (c : mcfg) (g : GCfg) : Persistent (cfgOwn (GF := GF) c g) := by
  unfold cfgOwn; infer_instance

/-- The input `x`, boxed (`any(x)`). -/
abbrev boxIn (x : Input) : GoInterface := interface.mkOk Input.ty #x

/-- The output `y`, boxed (`any(y)`). -/
abbrev boxOut (y : Output) : GoInterface := interface.mkOk Output.ty #y

/-- The state slice `sl`, boxed (`any(state(sl))`). -/
abbrev boxSt (sl : GoSlice) : GoInterface := interface.mkOk state.ty #sl

open Classical in
/-- The model's decoder of porcupine's operations (see the file header). -/
def decOp (io : github_com.anishathalye.porcupine.OpV) : Option (Input × linkv.Ans Output) :=
  if h : ∃ p : Input × Output, io = (boxIn p.1, boxOut p.2) then
    some (h.choose.1, ansOf h.choose.2)
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
theorem Input_intoVal_inj : Function.Injective (intoVal (V := Input)) := by
  intro x y h
  have h : (#x : val) = #y := h
  have e1 := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get_Kind x) (Input.TypeAssumptions.get_Kind y) h))
  have e2 := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get_Key x) (Input.TypeAssumptions.get_Key y) h))
  have e3 := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get_Val x) (Input.TypeAssumptions.get_Val y) h))
  have e4 := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get_Reject x) (Input.TypeAssumptions.get_Reject y) h))
  have e5 := GoGlobalContext.intoVal_inj_bool (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get_NoOp x) (Input.TypeAssumptions.get_NoOp y) h))
  have e6 := GoGlobalContext.intoVal_inj_bool (Expr.Val.inj (proj_eq
    (Input.TypeAssumptions.get_IgnoreNotFound x) (Input.TypeAssumptions.get_IgnoreNotFound y) h))
  cases x; cases y; simp_all

include sem package_sem in
theorem Output_intoVal_inj : Function.Injective (intoVal (V := Output)) := by
  intro x y h
  have h : (#x : val) = #y := h
  have e1 := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get_Err x) (Output.TypeAssumptions.get_Err y) h))
  have e2 := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get_ErrKey x) (Output.TypeAssumptions.get_ErrKey y) h))
  have e3 := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get_ErrRV x) (Output.TypeAssumptions.get_ErrRV y) h))
  have e4 := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get_Name x) (Output.TypeAssumptions.get_Name y) h))
  have e5 := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get_Value x) (Output.TypeAssumptions.get_Value y) h))
  have e6 := go.intoVal_inj (Expr.Val.inj (proj_eq
    (Output.TypeAssumptions.get_RV x) (Output.TypeAssumptions.get_RV y) h))
  cases x; cases y; simp_all

include sem package_sem in
/-- The decoder of a boxed input and output. -/
theorem decOp_box (x : Input) (y : Output) : decOp (boxIn x, boxOut y) = some (x, ansOf y) := by
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

/-- A Go state value represents `S`, its configurations `Bounded n` (see the file header). -/
def stRepB (g0 : GSt) (n : Nat) (v : GoInterface) (S : linkv.PSet GSt Input) : IProp GF :=
  iprop(∃ (sl : GoSlice) (cs : List mcfg) (gs : List GCfg),
    ⌜v = boxSt sl ∧ GOk g0 gs S ∧ ∀ g ∈ gs, Bounded n g⌝ ∗ sl ↦*□ cs ∗
      [∗list] c;g ∈ cs;gs, cfgOwn c g)

instance stRepB_persistent (g0 : GSt) (n : Nat) (v : GoInterface) (S : linkv.PSet GSt Input) :
    Persistent (stRepB (GF := GF) g0 n v S) := by
  unfold stRepB; infer_instance

/-- **The model's specification** (see the file header). -/
def k8setcd3S (g0 : GSt) : github_com.anishathalye.porcupine.ModelSpec GF (linkv.PSet GSt Input) where
  M := linkv.pM (kSpec g0) decOp
  rep k := stRepB g0 (k + g0.items.length + 1)
  ioOk i o := iprop(⌜∃ x y, i = boxIn x ∧ o = boxOut y⌝)
  ioOk_pers _ _ := by infer_instance

end defs

end k8setcd3
end EtcdGrove
end Perennial
