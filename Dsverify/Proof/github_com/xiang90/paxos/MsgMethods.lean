/-
Ported from dsverify-lab examples/paxos/proof/Paxos/Proof/MsgMethods.lean (lab master 7a84fb35; notes/dsv-paxos.md).

Internal specs of `message`'s methods (`number`, `proposalValue`, `proposalNumber`), as used by
the acceptor and the learner (package accept-learn). Named under `AccLrn` to stay apart from
other packages' internal specs.
-/
module

public import Dsverify.Proof.github_com.xiang90.paxos.Agents

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.xiang90.paxos

attribute [local instance] GooseGlobalGS.gooseInvGS

namespace AccLrn

theorem prop_not_acc {x : w64} (h : x ∈ propIds) : x ∉ accIds := by
  simp only [propIds, accIds, List.mem_cons, List.not_mem_nil, or_false] at *
  rcases h with rfl | rfl | rfl | rfl <;> decide

theorem lrn_not_acc {x : w64} (h : x ∈ lrnIds) : x ∉ accIds := by
  simp only [lrnIds, accIds, List.mem_cons, List.not_mem_nil, or_false] at *
  rcases h with rfl | rfl <;> decide

theorem lrn_not_prop {x : w64} (h : x ∈ lrnIds) : x ∉ propIds := by
  simp only [lrnIds, propIds, List.mem_cons, List.not_mem_nil, or_false] at *
  rcases h with rfl | rfl <;> decide

section msgok
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] 
variable {GF : BundledGFunctors} [GooseGlobalGS HasLC.hasLC GF]

/-- What a message to an acceptor means (unfolds `msgOK`). -/
theorem msgOK_acc (Γ : Names) (m : message) (a : w64) (hto : m.to' = a) (h : a ∈ accIds) :
    msgOK (GF := GF) Γ m ⊢ (⌜m.typ' = W64 1 ∧ m.from' ∈ propIds⌝ ∨
      (⌜m.typ' = W64 2⌝ ∗ propW Γ m.n' m.value' ∗ ∃ k w, pfW Γ a m.n' k w)) := by
  subst hto; unfold msgOK; simp only [h, ↓reduceIte]; exact .rfl

/-- What a message to a learner means (unfolds `msgOK`). -/
theorem msgOK_lrn (Γ : Names) (m : message) (h : m.to' ∈ lrnIds) :
    msgOK (GF := GF) Γ m ⊣⊢ (⌜m.typ' = W64 4 ∧ m.from' ∈ accIds⌝ ∗ accW Γ m.from' m.n' m.value') := by
  unfold msgOK; simp only [lrn_not_acc h, lrn_not_prop h, h, ↓reduceIte]; exact .rfl

/-- What a message to a proposer means (unfolds `msgOK`). -/
theorem msgOK_prop (Γ : Names) (m : message) (h : m.to' ∈ propIds) :
    msgOK (GF := GF) Γ m ⊣⊢
      (⌜m.typ' = W64 3 ∧ m.from' ∈ accIds⌝ ∗ pfW Γ m.from' m.n' m.prevn' m.value') := by
  unfold msgOK; simp only [prop_not_acc h, h, ↓reduceIte]; exact .rfl

end msgok



section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [π : NetProtoGS]
variable [package_sem : paxos.Assumptions]

set_option goose.wp.extras true

local notation "pkg" => pkg_id.github_com.xiang90.paxos

/-- `m.number()` (value receiver). -/
theorem wp_number (m : message) :
  {{ isPkgInit (PROP := IProp GF) pkg }}
    (App (Val (m @!! message.ty @!! go!"number")) (Val #()))
  {{ RET #m.n'; True }} := by
  wp_start
  wp_auto
  wp_end

/-- `m.proposalNumber()` of an `Accept`. -/
theorem wp_proposalNumber (m : message) (h : m.typ' = W64 4) :
  {{ isPkgInit (PROP := IProp GF) pkg }}
    (App (Val (m @!! message.ty @!! go!"proposalNumber")) (Val #()))
  {{ RET #m.n'; True }} := by
  wp_start
  wp_auto
  wp_if_destruct
  · simp_all
  wp_if_destruct
  · wp_end
  · exact absurd h Hif

/-- `m.proposalValue()` of an `Accept`. -/
theorem wp_proposalValue (m : message) (h : m.typ' = W64 4) :
  {{ isPkgInit (PROP := IProp GF) pkg }}
    (App (Val (m @!! message.ty @!! go!"proposalValue")) (Val #()))
  {{ RET #m.value'; True }} := by
  wp_start
  wp_auto
  wp_if_destruct
  · wp_end
  · exact absurd h Hif

/-- `(&m).number()` (the pointer-receiver wrapper). -/
theorem wp_number_ptr (l : Loc) (dq : DFrac) (m : message) :
  {{ isPkgInit (PROP := IProp GF) pkg ∗ l ↦{dq} m }}
    (App (Val (l @!! go.GoType.PointerType message.ty @!! go!"number")) (Val #()))
  {{ RET #m.n'; l ↦{dq} m }} := by
  wp_start as Hl
  wp_auto
  wp_apply wp_number
  iapply HΦ $$ Hl

/-- A learner's initial entry for an acceptor: `message{typ: Accept}`. -/
abbrev lrnInit : GoInterface := interface.mkOk message.ty #({ (zero_val message) with typ' := W64 4 } : message)

/-- `Printf`'s arguments of the acceptor's and learner's logging: `int`s. -/
def intArgs (zs : List w64) : List GoInterface := zs.map (fun z => interface.mkOk go.int #z)

theorem intArgs_wf (zs : List w64) : fmt.ArgsWf (intArgs zs) := by
  induction zs with
  | nil => exact fmt.ArgsWf.nil
  | cons z zs ih => exact fmt.ArgsWf.cons_int _ _ _ (.int z) ih

theorem wp_ints2 (a b : w64) (Φ : val → IProp GF) :
    (∀ sl : GoSlice, sl ↦* intArgs [a, b] -∗ Φ #sl) ⊢
    WP (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType (go.GoType.InterfaceType [])))))
      (Val (LiteralValueV
        [KeyedElement none (ElementExpression (go.GoType.InterfaceType []) #(interface.mkOk go.int #a)),
         KeyedElement none (ElementExpression (go.GoType.InterfaceType []) #(interface.mkOk go.int #b))])))
      {{ Φ }} := by
  iintro HΦ
  iapply wp_slice_literal (V := GoInterface) (t := go.GoType.InterfaceType []) (intArgs [a, b])
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl ⟨Hs, -⟩
  iapply HΦ $$ Hs

theorem wp_ints3 (a b c : w64) (Φ : val → IProp GF) :
    (∀ sl : GoSlice, sl ↦* intArgs [a, b, c] -∗ Φ #sl) ⊢
    WP (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType (go.GoType.InterfaceType [])))))
      (Val (LiteralValueV
        [KeyedElement none (ElementExpression (go.GoType.InterfaceType []) #(interface.mkOk go.int #a)),
         KeyedElement none (ElementExpression (go.GoType.InterfaceType []) #(interface.mkOk go.int #b)),
         KeyedElement none (ElementExpression (go.GoType.InterfaceType []) #(interface.mkOk go.int #c))])))
      {{ Φ }} := by
  iintro HΦ
  iapply wp_slice_literal (V := GoInterface) (t := go.GoType.InterfaceType []) (intArgs [a, b, c])
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl ⟨Hs, -⟩
  iapply HΦ $$ Hs

theorem wp_ints4 (a b c d : w64) (Φ : val → IProp GF) :
    (∀ sl : GoSlice, sl ↦* intArgs [a, b, c, d] -∗ Φ #sl) ⊢
    WP (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType (go.GoType.InterfaceType [])))))
      (Val (LiteralValueV
        [KeyedElement none (ElementExpression (go.GoType.InterfaceType []) #(interface.mkOk go.int #a)),
         KeyedElement none (ElementExpression (go.GoType.InterfaceType []) #(interface.mkOk go.int #b)),
         KeyedElement none (ElementExpression (go.GoType.InterfaceType []) #(interface.mkOk go.int #c)),
         KeyedElement none (ElementExpression (go.GoType.InterfaceType []) #(interface.mkOk go.int #d))])))
      {{ Φ }} := by
  iintro HΦ
  iapply wp_slice_literal (V := GoInterface) (t := go.GoType.InterfaceType []) (intArgs [a, b, c, d])
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl ⟨Hs, -⟩
  iapply HΦ $$ Hs

end specs

end AccLrn

end github_com.xiang90.paxos

end Perennial
