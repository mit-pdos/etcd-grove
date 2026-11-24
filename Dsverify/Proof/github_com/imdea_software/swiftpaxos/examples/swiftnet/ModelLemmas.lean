/-
The kit model's decoder laws and `PendDec` (as dsv-rabia's `ModelLemmas.lean`: out of the proof
file, so that the orchestrator's proof sees them without importing a proof; CLAUDE.md, "Import
tiers"): the boxed inputs and answers are injective (`swDec_box`), `Out`'s bytes are `encOutB`
(`encOutV_out`), distinct outputs have distinct bytes (`swR_encOut_inj`), and porcupine's model is
the pending-writes model of the far side's store (`swS_pendDec`), for any base state and mask.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.KitModel

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace github_com.imdea_software.swiftpaxos.examples.swiftnet

open EtcdGrove EtcdGrove.linkv github_com.mit_pdos.etcd_grove.examples.lib.remote

section dec
variable [GooseExts] [go_gctx : GoGlobalContext] [lctx : GoLocalContext] [GoSemanticsFunctions]
variable [sem : go.Semantics] [bvi : go.BasicIntoValInj]
variable [package_sem : github_com.imdea_software.swiftpaxos.examples.swiftnet.Assumptions]

attribute [local instance] Assumptions.instance'In Assumptions.instance'Out

theorem in_intoVal_inj {x y : In} (h : (#x : val) = #y) : x = y := by
  have hP := (In.TypeAssumptions.get'Put x).isGoStep_det_internal.isGoStep_pure_det
  have hP' := (In.TypeAssumptions.get'Put y).isGoStep_det_internal.isGoStep_pure_det
  have hK := (In.TypeAssumptions.get'K x).isGoStep_det_internal.isGoStep_pure_det
  have hK' := (In.TypeAssumptions.get'K y).isGoStep_det_internal.isGoStep_pure_det
  have hV := (In.TypeAssumptions.get'V x).isGoStep_det_internal.isGoStep_pure_det
  have hV' := (In.TypeAssumptions.get'V y).isGoStep_det_internal.isGoStep_pure_det
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
  have hU := (Out.TypeAssumptions.get'Unknown x).isGoStep_det_internal.isGoStep_pure_det
  have hU' := (Out.TypeAssumptions.get'Unknown y).isGoStep_det_internal.isGoStep_pure_det
  have hV := (Out.TypeAssumptions.get'V x).isGoStep_det_internal.isGoStep_pure_det
  have hV' := (Out.TypeAssumptions.get'V y).isGoStep_det_internal.isGoStep_pure_det
  rw [h, hU'] at hU
  rw [h, hV'] at hV
  have eU : Val #x.Unknown' = Val #y.Unknown' := (congrFun hU (Val #y.Unknown')) ▸ rfl
  have eV : Val #x.V' = Val #y.V' := (congrFun hV (Val #y.V')) ▸ rfl
  injection eU with eU
  injection eV with eV
  have eU' := GoGlobalContext.intoVal_inj_bool eU
  have eV' := go.intoVal_inj eV
  cases x; cases y
  simp only at eU' eV'
  subst eU' eV'
  rfl

theorem inV_inj {a b : KIn} (h : inV a = inV b) : a = b := by
  simp only [inV, interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq,
    _root_.true_and] at h
  have e := in_intoVal_inj h
  simp only [inVal, In.mk.injEq] at e
  obtain ⟨e1, e2, e3⟩ := e
  have hk : a.key = b.key := by
    have ha := a.key_lt
    have hb := b.key_lt
    have h1 : uint.Z (W64 (a.key : Int)) = a.key := by word
    have h2 : uint.Z (W64 (b.key : Int)) = b.key := by word
    rw [e2, h2] at h1
    omega
  rcases a with ⟨⟨pa, ka, va⟩, ha⟩
  rcases b with ⟨⟨pb, kb, vb⟩, hb⟩
  apply Subtype.ext
  change pa = pb at e1
  change va = vb at e3
  change ka = kb at hk
  subst e1 e3 hk
  rfl

theorem outV_inj {u v u' v'} (h : outV u v = outV u' v') : u = u' ∧ v = v' := by
  simp only [outV, interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq,
    _root_.true_and] at h
  have := out_intoVal_inj h
  simp only [Out.mk.injEq] at this
  exact this

theorem ansV_inj {a b : Ans BStr} (h : ansV a = ansV b) : a = b := by
  cases a <;> cases b <;> simp only [ansV] at h
  · obtain ⟨-, e⟩ := outV_inj h
    rw [Subtype.ext e]
  · exact absurd (outV_inj h).1 (by decide)
  · exact absurd (outV_inj h).1 (by decide)
  · rfl

/-- `swDec` on a boxed input and a boxed answer. -/
theorem swDec_box (i : KIn) (a : Ans BStr) : swDec (inV i, ansV a) = some (i, a) := by
  unfold swDec
  split
  · next h =>
    have hs := Classical.choose_spec (Classical.choose_spec h)
    obtain ⟨h1, h2⟩ := Prod.mk.inj hs
    rw [ansV_inj h2.symm, inV_inj h1.symm]
  · next hn => exact absurd ⟨i, a, rfl⟩ hn

/-- `Out{u, w}`'s bytes, for a bounded value. -/
theorem encOutV_outV (u : Bool) (w : BStr) : encOutV (outV u w.1) = encOutB u w.1 := by
  unfold encOutV
  split
  · rename_i h
    obtain ⟨h1, h2⟩ := outV_inj (Classical.choose_spec h)
    rw [← h1, ← h2]
  · rename_i h
    exact absurd ⟨(u, w), rfl⟩ h

end dec

section pend
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [bvi : go.BasicIntoValInj]
variable [package_sem : github_com.imdea_software.swiftpaxos.examples.swiftnet.Assumptions]

/-- Distinct outputs have distinct bytes. -/
theorem swR_encOut_inj (sys : St → IProp GF) (E : CoPset) (o o' : BStr)
    (h : (swR sys E).encOut ((swR sys E).ov o) = (swR sys E).encOut ((swR sys E).ov o')) :
    o = o' := by
  simp only [swR] at h
  rw [encOutV_outV false o, encOutV_outV false o'] at h
  simp only [encOutB, Bool.false_eq_true, ↓reduceIte, List.cons.injEq, _root_.true_and] at h
  exact Subtype.ext h

/-- **porcupine's model is the pending-writes model** of the far side's store `swR sys E`. -/
theorem swS_pendDec (sys : St → IProp GF) (E : CoPset) :
    PendDec (swR sys E) (swS (GF := GF)) where
  init := rfl
  ok s i o := pM_step swB swDec s _ i _ (swDec_box i (.ok o))
  err s i := pM_step swB swDec s _ i _ (swDec_box i .err)
  ioOk_ok i o := BI.pure_intro ⟨⟨i, rfl⟩, .ok o, rfl⟩
  ioOk_err i := BI.pure_intro ⟨⟨i, rfl⟩, .err, rfl⟩
  noObs _ := rfl

theorem pendCtx_swS (sys : St → IProp GF) (E : CoPset) (γp : PendNames) :
    pendCtx (Gg := hG.goose_globalGS) (swR sys E) (swS0 (GF := GF)) γp =
      pendCtx (Gg := hG.goose_globalGS) (swR sys E) (swS (GF := GF)) γp := rfl

theorem pendLib_swS (γp : PendNames) :
    pendLib (Gg := hG.goose_globalGS) (swS0 (GF := GF)) γp (swS0 (GF := GF)).M.init =
      pendLib (Gg := hG.goose_globalGS) (swS (GF := GF)) γp (swS (GF := GF)).M.init := rfl

end pend

end github_com.imdea_software.swiftpaxos.examples.swiftnet
end Perennial
