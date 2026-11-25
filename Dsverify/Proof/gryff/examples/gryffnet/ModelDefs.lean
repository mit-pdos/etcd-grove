/-
The definitions of `ModelProof.lean` that other modules use (porcupine's model `casS0`/`casS` of
the register, its values `inV`/`outV` and decoder `casDec`, the configurations' `cfgOk`/`cfgsOk`,
and `Model()`'s spec `Model.spec`), apart so that they import no proof (CLAUDE.md, "Import tiers").
-/
module

public import Dsverify.Proof.gryff.examples.gryffnet.ModelSet
public import Dsverify.Proof.gryff.examples.gryffnet.Base
public import Proof.github_com.anishathalye.porcupine.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace gryff.examples.gryffnet

open EtcdGrove EtcdGrove.linkv

/-! ## porcupine's model -/

section model
variable [GooseExts] [GoGlobalContext]

/-- An input, boxed (`any` holding an `In`). -/
abbrev inV (x : In) : GoInterface := interface.mkOk In.ty #x

/-- An output, boxed (`any` holding an `Out`). -/
abbrev outV (y : Out) : GoInterface := interface.mkOk Out.ty #y

open Classical in
/-- porcupine's operations as the register's: a boxed `In` and a boxed `Out`, unknown (`err`) or
not (`ok o`); anything else decodes to nothing. -/
def casDec (io : OpV) : Option (In × Ans Out) :=
  if h : ∃ (x : In) (y : Out), io = (inV x, outV y) then
    let x := choose h
    let y := choose (choose_spec h)
    some (x, if y.Unknown' then .err else .ok y)
  else none

/-- **The register's porcupine model**, as the pending library's invariant sees it (its
sequential model only): `pSeq casB` through `casDec`. -/
def casS0 {GF : BundledGFunctors} : ModelSpec GF (PSet w64 In) where
  M := pM casB casDec
  rep _ _ _ := iprop(True)
  ioOk i o := iprop(⌜(∃ x : In, i = inV x) ∧ ∃ y : Out, o = outV y⌝)
  ioOk_pers _ _ := by infer_instance

end model

section dec
variable [GooseExts] [go_gctx : GoGlobalContext] [lctx : GoLocalContext] [GoSemanticsFunctions]
variable [sem : go.Semantics] [bvi : go.BasicIntoValInj]
variable [package_sem : gryff.examples.gryffnet.Assumptions]

/-- `Out`'s values are injective (its fields are read off by deterministic steps). -/
theorem out_intoVal_inj {x y : Out} (h : (#x : val) = #y) : x = y := by
  have hV := (Out.TypeAssumptions.get_V x).isGoStep_det_internal.isGoStep_pure_det
  have hV' := (Out.TypeAssumptions.get_V y).isGoStep_det_internal.isGoStep_pure_det
  have hU := (Out.TypeAssumptions.get_Unknown x).isGoStep_det_internal.isGoStep_pure_det
  have hU' := (Out.TypeAssumptions.get_Unknown y).isGoStep_det_internal.isGoStep_pure_det
  rw [h, hV'] at hV
  rw [h, hU'] at hU
  have eV : Val #x.V' = Val #y.V' := (congrFun hV (Val #y.V')) ▸ rfl
  have eU : Val #x.Unknown' = Val #y.Unknown' := (congrFun hU (Val #y.Unknown')) ▸ rfl
  injection eV with eV
  injection eU with eU
  have eV' := go.intoVal_inj eV
  have eU' := GoGlobalContext.intoVal_inj_bool eU
  cases x; cases y
  simp only at eV' eU'
  subst eV' eU'
  rfl

/-- `In`'s values are injective. -/
theorem in_intoVal_inj {x y : In} (h : (#x : val) = #y) : x = y := by
  have hO := (In.TypeAssumptions.get_Op x).isGoStep_det_internal.isGoStep_pure_det
  have hO' := (In.TypeAssumptions.get_Op y).isGoStep_det_internal.isGoStep_pure_det
  have hA := (In.TypeAssumptions.get_A x).isGoStep_det_internal.isGoStep_pure_det
  have hA' := (In.TypeAssumptions.get_A y).isGoStep_det_internal.isGoStep_pure_det
  have hB := (In.TypeAssumptions.get_B x).isGoStep_det_internal.isGoStep_pure_det
  have hB' := (In.TypeAssumptions.get_B y).isGoStep_det_internal.isGoStep_pure_det
  rw [h, hO'] at hO
  rw [h, hA'] at hA
  rw [h, hB'] at hB
  have eO : Val #x.Op' = Val #y.Op' := (congrFun hO (Val #y.Op')) ▸ rfl
  have eA : Val #x.A' = Val #y.A' := (congrFun hA (Val #y.A')) ▸ rfl
  have eB : Val #x.B' = Val #y.B' := (congrFun hB (Val #y.B')) ▸ rfl
  injection eO with eO
  injection eA with eA
  injection eB with eB
  have eO' := go.intoVal_inj eO
  have eA' := go.intoVal_inj eA
  have eB' := go.intoVal_inj eB
  cases x; cases y
  simp only at eO' eA' eB'
  subst eO' eA' eB'
  rfl

theorem inV_inj {a b : In} (h : inV a = inV b) : a = b := by
  simp only [inV, interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq,
    _root_.true_and] at h
  exact in_intoVal_inj h

theorem outV_inj {a b : Out} (h : outV a = outV b) : a = b := by
  simp only [outV, interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq,
    _root_.true_and] at h
  exact out_intoVal_inj h

/-- `casDec` on a boxed `In` and a boxed `Out`. -/
theorem casDec_box (x : In) (y : Out) :
    casDec (inV x, outV y) = some (x, if y.Unknown' then .err else .ok y) := by
  unfold casDec
  split
  · next h =>
    have hs := Classical.choose_spec (Classical.choose_spec h)
    obtain ⟨h1, h2⟩ := Prod.mk.inj hs
    have e1 := inV_inj h1
    have e2 := outV_inj h2
    dsimp only
    rw [← e2, ← e1]
  · next hn => exact absurd ⟨x, y, rfl⟩ hn

end dec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : gryff.examples.gryffnet.Assumptions]
variable [bvi : go.BasicIntoValInj]
local notation "kpkg" => pkg_id.gryff.examples.gryffnet

section isWrite
set_option goose.wp.extras true
attribute [local goose_wp_simp_extra] OpRead OpWrite OpCAS

/-- `isWrite(i)` (kit.go), which `KitProof.lean`'s generator also calls. -/
theorem wp_isWrite (i : In) :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! gryff.examples.gryffnet.isWrite)) (Val #i))
    {{ RET #(isWriteG i); True }} := by
  wp_start as #Hk
  wp_auto
  unfold isWriteG
  by_cases h1 : i.Op' = W64 1
  · simp only [h1, _root_.decide_true, Bool.true_or]
    wp_auto
    iapply HΦ; itrivial
  · simp only [h1, _root_.decide_false, Bool.false_or]
    wp_auto
    iapply HΦ; itrivial

end isWrite

/-! ## The model's configurations in Go -/

theorem gcfg_eq (x y : GCfg) : x = y ↔ x.st = y.st ∧ x.pend = y.pend := by
  cases x; cases y; simp

instance GCfg.decEq : DecidableEq GCfg := fun a b =>
  decidable_of_iff (a.st = b.st ∧ a.pend = b.pend) (gcfg_eq a b).symm


/-- A Go `Cfg` stands for the configuration `g`: its value, and its pending slice, read-only,
holding `g.pend`. -/
def cfgOk (c : Cfg) (g : GCfg) : IProp GF := iprop(⌜c.V' = g.st⌝ ∗ c.Pend' ↦*□ g.pend)

instance cfgOk_pers (c : Cfg) (g : GCfg) : Persistent (cfgOk (GF := GF) c g) := by
  unfold cfgOk; infer_instance

/-- A list of Go `Cfg`s stands for the list of configurations `L`, element by element. -/
def cfgsOk (cs : List Cfg) (L : List GCfg) : IProp GF :=
  iprop(⌜cs.length = L.length⌝ ∗
    □ ∀ (j : Nat) (c : Cfg) (g : GCfg), ⌜cs[j]? = some c⌝ -∗ ⌜L[j]? = some g⌝ -∗ cfgOk c g)

instance cfgsOk_pers (cs : List Cfg) (L : List GCfg) : Persistent (cfgsOk (GF := GF) cs L) := by
  unfold cfgsOk; infer_instance

/-! ## The model value and `Model()` -/

/-- A model value: the boxed `State{Cfgs: sl}` with `sl` read-only, holding Go configurations
standing for the nonempty list `L`; its set is `cfgSet L`; each pending list has at most `k`
operations (a step adds at most one). -/
def casRep (k : Nat) (v : GoInterface) (s : PSet w64 In) : IProp GF :=
  iprop(∃ (sl : GoSlice) (cs : List Cfg) (L : List GCfg),
    ⌜v = interface.mkOk State.ty #(State.mk sl) ∧ s = cfgSet L ∧ L ≠ [] ∧
      ∀ x ∈ L, x.pend.length ≤ k⌝ ∗ sl ↦*□ cs ∗ cfgsOk cs L)

/-- **The register's porcupine model** (pending writes and CASes): `pSeq casB` through
`casDec`. -/
def casS : ModelSpec GF (PSet w64 In) where
  M := (casS0 (GF := GF)).M
  rep k v s := casRep k v s
  ioOk := (casS0 (GF := GF)).ioOk
  ioOk_pers := (casS0 (GF := GF)).ioOk_pers

/-- `Model()`: the register's porcupine model. -/
abbrev Model.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) kpkg }}
    (App (Val (@! gryff.examples.gryffnet.Model)) (Val #()))
  {{ (m : github_com.anishathalye.porcupine.Model), RET #m; isModel (casS (GF := GF)) m }}

end proof

end gryff.examples.gryffnet

end Perennial
