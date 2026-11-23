/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/WriterExcl.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
Two owners of one `*bufio.Writer` are contradictory (what makes a client writer's first
registration fresh). Unfolds the harness's `ownWriter`/`writerRep` (a missing `bufio` law).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.Defs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-- The clients' writers map stays within the registered writers: a fresh registration. -/
theorem cwInv_fresh (cw : GMap w32 Loc) (ws : GMap Loc w32) (cl : w32) (w : Loc)
    (h : ∀ id w', cw !! id = some w' → ws !! w' = some id) (hw : ws !! w = none) :
    ∀ id w', (<[cl := w]> cw) !! id = some w' → (<[w := cl]> ws) !! w' = some id := by
  intro id w' hl
  simp only [GMap.lookup_insert_eq_iff] at hl ⊢
  by_cases hid : cl = id
  · subst hid; simp at hl; subst hl; simp
  · rw [if_neg hid] at hl
    have := h id w' hl
    have hne : w ≠ w' := by intro e; subst e; rw [hw] at this; cases this
    rw [if_neg hne]; exact this

/-- The same for a writer registered before. -/
theorem cwInv_reg (cw : GMap w32 Loc) (ws : GMap Loc w32) (cl : w32) (w : Loc)
    (h : ∀ id w', cw !! id = some w' → ws !! w' = some id) (hw : ws !! w = some cl) :
    ∀ id w', (<[cl := w]> cw) !! id = some w' → ws !! w' = some id := by
  intro id w' hl
  simp only [GMap.lookup_insert_eq_iff] at hl
  by_cases hid : cl = id
  · subst hid; simp at hl; subst hl; exact hw
  · rw [if_neg hid] at hl; exact h id w' hl

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]

theorem iface_excl (l : Loc) (v1 v2 : GoInterface) :
    typedPointsto (GF := netDistGF) l v1 (DFrac.own 1) ∗ typedPointsto l v2 (DFrac.own 1) ⊢ False := by
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %He
  subst He
  ihave H := (typedPointsto_frac_add (GF := netDistGF) l v1 1 1).2 $$ [H1 H2]
  · iframe
  rw [typedPointsto_unseal_eq]
  icases H with ⟨H, -⟩
  have hh : (typedPointstoDef (GF := netDistGF) l v1 (DFrac.own (1 + 1)) : IProp netDistGF) ⊢
      heapPointsto l (DFrac.own (1 + 1)) #v1 := .rfl
  ihave H := hh $$ H
  ihave %Hv := heapPointsto_frac_valid l (1 + 1) #v1 $$ H
  exfalso
  rw [Qp.val_add] at Hv
  have h1 : (1 : Qp).val = 1 := rfl
  rw [h1] at Hv
  grind

theorem writer_excl (w : Loc) (cv cv' : GoInterface) (J Q J' Q' : List w8 → IProp netDistGF)
    (s p s' p' : List w8) (e e' : GoInterface) :
    bufio.ownWriter w cv J Q s p e ∗ bufio.ownWriter w cv' J' Q' s' p' e' ⊢ False := by
  unfold bufio.ownWriter bufio.writerRep
  iintro ⟨⟨-, -, %b, %n, %rest, H1, -⟩, ⟨-, -, %b', %n', %rest', H2, -⟩⟩
  iStructNamed H1
  iStructNamedSuffix H2 "'"
  iapply iface_excl _ e e'
  isplitl [err]
  · iexact err
  · iexact err'

/-- A writer its listener owns is not registered. -/
theorem clientWrs_fresh (γ : sp.Names) (γc γm γw : GName) (ws : GMap Loc w32) (w : Loc)
    (cv : GoInterface) (J Q : List w8 → IProp netDistGF) (s p : List w8) (e : GoInterface) :
    ([∗map] w' ↦ cl ∈ ws, sp.wrSt γ γc γm w' (.client cl)) ∗ bufio.ownWriter w cv J Q s p e ⊢
      ⌜ws.lookup w = none⌝ ∗ ([∗map] w' ↦ cl ∈ ws, sp.wrSt γ γc γm w' (.client cl)) ∗
      bufio.ownWriter w cv J Q s p e := by
  iintro ⟨Hm, Hw⟩
  cases hl : ws.lookup w with
  | none => iframe; ipureintro; rfl
  | some cl0 =>
    icases (BigSepM.bigSepM_lookup_acc (Φ := fun w' cl => sp.wrSt γ γc γm w' (.client cl))
      (m := ws) (i := w) (x := cl0) hl).1 $$ Hm with ⟨Hs, -⟩
    iunfold sp.wrSt at Hs
    icases Hs with ⟨%cv0, %cid0, %s0, %p0, %e0, -, -, -, Ho, -⟩
    iexfalso
    iapply writer_excl
    isplitl [Ho]
    · iexact Ho
    · iexact Hw

end lemmas

end Perennial.github_com.imdea_software.swiftpaxos
