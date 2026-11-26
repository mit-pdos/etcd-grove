/-
The kit model's decoder laws, masks and `PendDec` (out of `ModelProof.lean`, a proof file, so
that `CodecProof` and `OrchProof` see them without importing a proof; CLAUDE.md, "Import tiers").
-/
module

public import Dsverify.Proof.rabia.examples.rabianet.KitModel

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace rabia.examples.rabianet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote Perennial.rabia
  Perennial.rabia.model

/-! ## The decoder -/

section dec
variable [GooseExts] [go_gctx : GoGlobalContext] [lctx : GoLocalContext] [GoSemanticsFunctions]
variable [sem : go.Semantics] [bvi : go.BasicIntoValInj]
variable [package_sem : rabia.examples.rabianet.Assumptions]

attribute [local instance] Assumptions.In_instance Assumptions.Out_instance

theorem in_intoVal_inj {x y : In} (h : (#x : val) = #y) : x = y := by
  have hP := (In.TypeAssumptions.get_Put x).isGoStep_det_internal.isGoStep_pure_det
  have hP' := (In.TypeAssumptions.get_Put y).isGoStep_det_internal.isGoStep_pure_det
  have hK := (In.TypeAssumptions.get_K x).isGoStep_det_internal.isGoStep_pure_det
  have hK' := (In.TypeAssumptions.get_K y).isGoStep_det_internal.isGoStep_pure_det
  have hV := (In.TypeAssumptions.get_V x).isGoStep_det_internal.isGoStep_pure_det
  have hV' := (In.TypeAssumptions.get_V y).isGoStep_det_internal.isGoStep_pure_det
  rw [h, hP'] at hP
  rw [h, hK'] at hK
  rw [h, hV'] at hV
  have eP : Val #x.Put' = Val #y.Put' := (congrFun hP (Val #y.Put')) ▸ rfl
  have eK : Val #x.K' = Val #y.K' := (congrFun hK (Val #y.K')) ▸ rfl
  have eV : Val #x.V' = Val #y.V' := (congrFun hV (Val #y.V')) ▸ rfl
  injection eP with eP
  injection eK with eK
  injection eV with eV
  have eP' := GoGlobalContext.intoVal_inj_bool eP
  have eK' := go.intoVal_inj eK
  have eV' := go.intoVal_inj eV
  cases x; cases y
  simp only at eP' eK' eV'
  subst eP' eK' eV'
  rfl

theorem out_intoVal_inj {x y : Out} (h : (#x : val) = #y) : x = y := by
  have hU := (Out.TypeAssumptions.get_Unknown x).isGoStep_det_internal.isGoStep_pure_det
  have hU' := (Out.TypeAssumptions.get_Unknown y).isGoStep_det_internal.isGoStep_pure_det
  have hP := (Out.TypeAssumptions.get_Put x).isGoStep_det_internal.isGoStep_pure_det
  have hP' := (Out.TypeAssumptions.get_Put y).isGoStep_det_internal.isGoStep_pure_det
  have hF := (Out.TypeAssumptions.get_Found x).isGoStep_det_internal.isGoStep_pure_det
  have hF' := (Out.TypeAssumptions.get_Found y).isGoStep_det_internal.isGoStep_pure_det
  have hV := (Out.TypeAssumptions.get_V x).isGoStep_det_internal.isGoStep_pure_det
  have hV' := (Out.TypeAssumptions.get_V y).isGoStep_det_internal.isGoStep_pure_det
  rw [h, hU'] at hU
  rw [h, hP'] at hP
  rw [h, hF'] at hF
  rw [h, hV'] at hV
  have eU : Val #x.Unknown' = Val #y.Unknown' := (congrFun hU (Val #y.Unknown')) ▸ rfl
  have eP : Val #x.Put' = Val #y.Put' := (congrFun hP (Val #y.Put')) ▸ rfl
  have eF : Val #x.Found' = Val #y.Found' := (congrFun hF (Val #y.Found')) ▸ rfl
  have eV : Val #x.V' = Val #y.V' := (congrFun hV (Val #y.V')) ▸ rfl
  injection eU with eU
  injection eP with eP
  injection eF with eF
  injection eV with eV
  have eU' := GoGlobalContext.intoVal_inj_bool eU
  have eP' := GoGlobalContext.intoVal_inj_bool eP
  have eF' := GoGlobalContext.intoVal_inj_bool eF
  have eV' := go.intoVal_inj eV
  cases x; cases y
  simp only at eU' eP' eF' eV'
  subst eU' eP' eF' eV'
  rfl

theorem inV_inj {a b : KIn} (h : inV a.1 = inV b.1) : a = b := by
  simp only [inV, interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, _root_.true_and] at h
  have e := in_intoVal_inj h
  rcases a with ⟨a, ha⟩; rcases b with ⟨b, hb⟩
  apply Subtype.ext
  simp only at e ⊢
  cases a <;> cases b <;> simp_all [inVal]
  all_goals (rename_i k v; exact absurd e (by simp [inputOk] at *))

theorem outV_eq {a b : Out} (h : interface.mkOk Out.ty #a = interface.mkOk Out.ty #b) : a = b := by
  simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, _root_.true_and] at h
  exact out_intoVal_inj h

theorem outVal_inj {a b : KOut} (h : outVal a.1 = outVal b.1) : a = b := by
  rcases a with ⟨a, ha⟩; rcases b with ⟨b, hb⟩
  apply Subtype.ext; simp only at h ⊢
  cases a with
  | done => cases b with
    | done => rfl
    | got w => cases w <;> simp [outVal] at h
  | got v => cases b with
    | done => cases v <;> simp [outVal] at h
    | got w => cases v <;> cases w <;> simp_all [outVal]

theorem outVal_ne_unk (o : KOut) : outVal o.1 ≠ Out.mk true false false [] := by
  rcases o with ⟨o, _⟩
  cases o with
  | done => simp [outVal]
  | got w => cases w <;> simp [outVal]

theorem ansV_inj {a b : linkv.Ans KOut} (h : ansV a = ansV b) : a = b := by
  cases a <;> cases b <;> simp only [ansV] at h
  · rw [outVal_inj (outV_eq h)]
  · exact absurd (outV_eq h) (outVal_ne_unk _)
  · exact absurd (outV_eq h).symm (outVal_ne_unk _)
  · rfl

/-- `kvDec` on a boxed input and a boxed answer. -/
theorem kvDec_box (i : KIn) (a : linkv.Ans KOut) : kvDec (inV i.1, ansV a) = some (i, a) := by
  unfold kvDec
  split
  · next h =>
    have hs := Classical.choose_spec (Classical.choose_spec h)
    obtain ⟨h1, h2⟩ := Prod.mk.inj hs
    rw [ansV_inj h2.symm, inV_inj h1.symm]
  · next hn => exact absurd ⟨i, a, rfl⟩ hn

/-- `Out{…}`'s bytes, for a bounded value. -/
theorem encOutV_out (x : Out) (hx : x.V'.length + 9 < 2 ^ 63) :
    encOutV (interface.mkOk Out.ty #x) = encOutB x := by
  unfold encOutV
  split
  · rename_i h
    rw [← outV_eq (Classical.choose_spec h).1]
  · rename_i h
    exact absurd ⟨x, rfl, hx⟩ h

theorem outVal_len (o : KOut) : (outVal o.1).V'.length + 9 < 2 ^ 63 := by
  rcases o with ⟨o, ho⟩
  cases o with
  | done => simp [outVal]
  | got w =>
    cases w with
    | none => simp [outVal]
    | some x => simp only [outVal]; exact (show valB x from ho).2

theorem outVal_unknown (o : KOut) : (outVal o.1).Unknown' = false := by
  rcases o with ⟨o, _⟩
  cases o with
  | done => rfl
  | got w => cases w <;> rfl

end dec

section masks
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF]

theorem pendN_rabia : (↑pendN : CoPset) ⊆ ⊤ \ rabiaE := by
  intro p hp
  have h1 := nclose_subseteq (nroot.@"remote") "pend" p hp
  rw [LawfulSet.mem_diff]
  refine ⟨CoPset.mem_full, ?_⟩
  unfold rabiaE rabiaR
  intro h
  exact ndot_ne_disjoint nroot (show "remote" ≠ "rabia" by decide) p ⟨h1, h⟩

theorem lintestN_rabia :
    (↑EtcdGrove.lintest.lintestN : CoPset) ⊆ ⊤ \ (rabiaE ∪ ↑pendN) := by
  intro p hp
  change p ∈ (↑(nroot.@"lintest") : CoPset) at hp
  rw [LawfulSet.mem_diff, LawfulSet.mem_union, not_or]
  refine ⟨CoPset.mem_full, ?_, ?_⟩
  · unfold rabiaE rabiaR
    intro h
    exact ndot_ne_disjoint nroot (show "lintest" ≠ "rabia" by decide) p ⟨hp, h⟩
  · intro h
    have h1 := nclose_subseteq (nroot.@"remote") "pend" p h
    exact ndot_ne_disjoint nroot (show "lintest" ≠ "remote" by decide) p ⟨hp, h1⟩

end masks

section pend
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [bvi : go.BasicIntoValInj] [package_sem : rabia.examples.rabianet.Assumptions]

/-- Distinct outputs have distinct bytes. -/
theorem kvR_encOut_inj (γ : Names) (o o' : KOut)
    (h : (kvR (Gg := hG.goose_globalGS) γ).encOut ((kvR (Gg := hG.goose_globalGS) γ).ov o) =
      (kvR (Gg := hG.goose_globalGS) γ).encOut ((kvR (Gg := hG.goose_globalGS) γ).ov o')) :
    o = o' := by
  simp only [kvR, outV] at h
  rw [encOutV_out _ (outVal_len o), encOutV_out _ (outVal_len o')] at h
  apply outVal_inj
  rcases o with ⟨o, ho⟩; rcases o' with ⟨o', ho'⟩
  simp only at h ⊢
  cases o with
  | done => cases o' with
    | done => rfl
    | got w => cases w <;> simp [outVal, encOutB] at h
  | got v => cases o' with
    | done => cases v <;> simp [outVal, encOutB] at h
    | got w => cases v <;> cases w <;> simp_all [outVal, encOutB]

/-- **porcupine's model is the pending-writes model** of the far side's store `kvR γ`. -/
theorem kvS_pendDec (γ : Names) : PendDec (kvR (Gg := hG.goose_globalGS) γ) (kvS (GF := GF)) :=
  .ofTotal (fun _ => rfl) {
  init := rfl
  ok s i o := linkv.pM_step kvB kvDec s _ i _ (kvDec_box i (.ok o))
  err s i := linkv.pM_step kvB kvDec s _ i _ (kvDec_box i .err)
  ioOk_ok i o := BI.pure_intro ⟨⟨i, rfl⟩, .ok o, rfl⟩
  ioOk_err i := BI.pure_intro ⟨⟨i, rfl⟩, .err, rfl⟩
  noObs _ := rfl }

theorem pendCtx_kvS (γ : Names) (γp : PendNames) :
    pendCtx (Gg := hG.goose_globalGS) (kvR γ) (kvS0 (GF := GF)) γp =
      pendCtx (Gg := hG.goose_globalGS) (kvR γ) (kvS (GF := GF)) γp := rfl

theorem pendLib_kvS (γp : PendNames) :
    pendLib (Gg := hG.goose_globalGS) (kvS0 (GF := GF)) γp (kvS0 (GF := GF)).M.init =
      pendLib (Gg := hG.goose_globalGS) (kvS (GF := GF)) γp (kvS (GF := GF)).M.init := rfl

end pend

end rabia.examples.rabianet
end Perennial
