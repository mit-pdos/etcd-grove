/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/HashLogKey.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`swift.CommandId` as a Go map key for `HashLog`'s maps (`nodes`, `pendingUpd`): decidable equality,
`intoVal` injective, `==` decides equality. A copy of the client group's `Proof/swift/client/CmdKey.lean`
(on its branch; namespace `swift.hlog` here): one shared module would avoid it.
-/
module

public import Dsverify.GeneratedProof.github_com.imdea_software.swiftpaxos.swift
public import Perennial.Golang.Theory.Map

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace swift.hlog

section base
variable [GooseExts]

instance cmdIdDecEq : DecidableEq swift.CommandId := fun a b =>
  decidable_of_iff (a.ClientId' = b.ClientId' ∧ a.SeqNum' = b.SeqNum') (by
    cases a; cases b; simp)

end base

section key
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : swift.Assumptions]

include sem package_sem in
theorem cmdId_intoVal_inj : Function.Injective (intoVal (V := swift.CommandId)) := by
  intro k k' h
  have h1 := (go.IsGoStepPureDet.isGoStep_pure_det (self :=
    (swift.CommandId.TypeAssumptions.get'ClientId k).isGoStep_det_internal))
  have h1' := (go.IsGoStepPureDet.isGoStep_pure_det (self :=
    (swift.CommandId.TypeAssumptions.get'ClientId k').isGoStep_det_internal))
  have h2 := (go.IsGoStepPureDet.isGoStep_pure_det (self :=
    (swift.CommandId.TypeAssumptions.get'SeqNum k).isGoStep_det_internal))
  have h2' := (go.IsGoStepPureDet.isGoStep_pure_det (self :=
    (swift.CommandId.TypeAssumptions.get'SeqNum k').isGoStep_det_internal))
  rw [h] at h1 h2
  rw [h1] at h1'; rw [h2] at h2'
  have e1 := congrFun h1' (Val #k'.ClientId'); simp at e1
  have e2 := congrFun h2' (Val #k'.SeqNum'); simp at e2
  cases k; cases k'
  simp only [swift.CommandId.mk.injEq]
  exact ⟨go.intoVal_inj e1, go.intoVal_inj e2⟩

/-- Not an instance (its semantics instance is not determined by the goal): `haveI` it. -/
def cmdId_intoValInj : go.IntoValInj swift.CommandId := ⟨cmdId_intoVal_inj (sem := sem)⟩

theorem wp_eq_cmdid (k k' : swift.CommandId) (s : Stuckness) (E : CoPset) (Φ : val → IProp GF) :
    Φ #(decide (k = k')) ⊢
      WP (App (Val (GoInstruction (GoOp GoEquals swift.CommandId.ty))) (Val (PairV #k #k'))) @ s; E
        {{ Φ }} := by
  iintro HΦ
  wp_auto
  wp_if_destruct
  · have : decide (k.SeqNum' = k'.SeqNum') = decide (k = k') := by
      cases k; cases k'; simp_all
    rw [this]; iexact HΦ
  · have : decide (k = k') = false := by
      cases k; cases k'; simp_all
    rw [this]; iexact HΦ

instance cmdId_safeMapKey (k : swift.CommandId) :
    SafeMapKey (GF := GF) (keys := mapKeys_all swift.CommandId) swift.CommandId.ty k where
  key_ok := trivial
  wp_go_eq_map_key k' _ s E Φ := wp_eq_cmdid k k' s E Φ

end key

end swift.hlog

end Perennial.github_com.imdea_software.swiftpaxos
