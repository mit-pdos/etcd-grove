/-
The definitions, specs and lemmas of `OptCondF.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.GeneratedProof.github_com.imdea_software.swiftpaxos.hook
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Inv
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Base

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace hook.ocf

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [hook.Assumptions]

/-- The `*OptCondF` at `cf`: condition `cond`, stored functions `fs` (a prefix of its slice). -/
def ownOcf (cf : Loc) (cond : GoFunc) (fs : List GoFunc) : IProp netDistGF :=
  iprop(∃ (sl : GoSlice) (L : List GoFunc), cf ↦ hook.OptCondF.mk cond sl (W64 fs.length) ∗
    sl ↦* L ∗ ownSliceCap GoFunc sl (DFrac.own 1) ∗ ⌜fs <+: L ∧ fs.length < 2 ^ 62⌝)

/-- The condition: on the state `Pc v` it returns `v`. -/
def condOk (cond : GoFunc) (Pc : Bool → IProp netDistGF) : IProp netDistGF :=
  iprop(∀ (v : Bool), {{ Pc v }} (App (Val #cond) (Val #())) {{ RET #v; Pc v }})

/-- Running `fs` in order ends with `Q`. -/
def chain : List GoFunc → IProp netDistGF → IProp netDistGF
  | [], Q => Q
  | g :: gs, Q => iprop(WP (App (Val #g) (Val #())) {{ fun rv => iprop(⌜rv = #()⌝ ∗ chain gs Q) }})

end defs

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [hook.Assumptions]

/-- `NewOptCondF(cond)`. -/
abbrev NewOptCondF.specI : Prop :=
  ∀ (cond : GoFunc),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.hook }}
    (App (Val (@! hook.NewOptCondF)) (Val #cond))
  {{ (cf : Loc), RET #cf; ownOcf cf cond [] }}

/-- `cf.ReinitCondF(cond)`: `cf` itself (any store before) or, for `nil`, a new one. -/
abbrev OptCondF.ReinitCondF.specI : Prop :=
  ∀ (cf : Loc) (cond0 : GoFunc) (fs : List GoFunc) (cond : GoFunc),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.hook ∗
      (⌜cf = null⌝ ∨ ownOcf cf cond0 fs) }}
    (App (Val (cf @!! go.GoType.PointerType hook.OptCondF.ty @!! go!"ReinitCondF")) (Val #cond))
  {{ (cf' : Loc), RET #cf'; ownOcf cf' cond [] }}

/-- `cf.Call(f)` with the condition's state `Pc v`: `v` true: the stored functions and `f` run
(`chain`, given the condition's state back first), the store is empty; `v` false: `f` stored
(premise: the store is not huge). -/
abbrev OptCondF.Call.specI : Prop :=
  ∀ (cf : Loc) (cond : GoFunc) (fs : List GoFunc) (f : GoFunc) (Pc : Bool → IProp netDistGF)
    (v : Bool) (Q : IProp netDistGF),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.hook ∗
      ownOcf cf cond fs ∗ □ condOk cond Pc ∗ Pc v ∗ ⌜fs.length + 1 < 2 ^ 62⌝ ∗
      (if v then iprop(Pc v -∗ ownOcf cf cond [] -∗ chain (fs ++ [f]) Q) else iprop(True)) }}
    (App (Val (cf @!! go.GoType.PointerType hook.OptCondF.ty @!! go!"Call")) (Val #f))
  {{ (b : Bool), RET #b; ⌜b = v⌝ ∗
      (if v then Q else iprop(ownOcf cf cond (fs ++ [f]) ∗ Pc v)) }}

/-- `cf.Recall()` with the condition's state `Pc v`: with stored functions and `v` true they run
(`chain`) and the store is empty; else nothing (the condition's state back; its `cond` is
read only when the store is not empty). -/
abbrev OptCondF.Recall.specI : Prop :=
  ∀ (cf : Loc) (cond : GoFunc) (fs : List GoFunc) (Pc : Bool → IProp netDistGF) (v : Bool)
    (Q : IProp netDistGF),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.hook ∗
      ownOcf cf cond fs ∗ □ condOk cond Pc ∗ Pc v ∗
      (if v && !fs.isEmpty then iprop(Pc v -∗ ownOcf cf cond [] -∗ chain fs Q) else iprop(True)) }}
    (App (Val (cf @!! go.GoType.PointerType hook.OptCondF.ty @!! go!"Recall")) (Val #()))
  {{ (b : Bool), RET #b; ⌜b = (v && !fs.isEmpty)⌝ ∗
      (if v && !fs.isEmpty then Q else iprop(ownOcf cf cond fs ∗ Pc v)) }}

end specs

end hook.ocf

namespace hook.ocf

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [hook.Assumptions]

set_option goose.wp.extras true

theorem prefix_set_snoc {α : Type} (fs L : List α) (f : α) (h : fs <+: L) (hl : fs.length < L.length) :
    fs ++ [f] <+: L.set fs.length f := by
  obtain ⟨u, rfl⟩ := h
  cases u with
  | nil => simp at hl
  | cons a u =>
    refine ⟨u, ?_⟩
    rw [List.set_append_right _ _ (Nat.le_refl _)]
    simp

end proofs

end hook.ocf

end Perennial.github_com.imdea_software.swiftpaxos
