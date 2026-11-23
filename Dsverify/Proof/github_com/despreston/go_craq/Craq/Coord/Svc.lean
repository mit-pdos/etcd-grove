/-
The coordinator is its service (`coordinator.coord_svc.spec`): `AddNode` (from `addNode`),
`Write` and `RemoveNode`.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Coord.AddNode
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Coord.Write
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Coord.RemoveNode

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [log.Assumptions] [LogHyp GF] [examples.craqnet.Assumptions] [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]

theorem wp_AddNode (cfg : Cfg GF) (c : Loc) (a : GoString) (ha : a ∈ cfg.chain) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.coordinator ∗
        isCoord cfg c ∗ joinTicket cfg.γ a }}
      (App (Val (c @!! go.GoType.PointerType coordinator.Coordinator.ty @!! go!"AddNode")) (Val #a))
    {{ (p : Loc) (err : GoInterface), RET (PairV #p #err);
        (⌜err = interface.nil⌝ ∗ ∃ m : MetaV, metaPtr p (DFrac.own 1) m) ∨ errNE err }} := by
  wp_start as ⟨#Hc, Ht⟩
  wp_auto
  wp_apply wp_addNode cfg c a ha $$ [Ht] as %p %err Hres
  · iframe Hc Ht
  icases Hres with (⟨%Hnil, Hm⟩ | #Hany)
  · subst Hnil
    wp_auto
    iapply HΦ
    ileft; iframe Hm; ipureintro; rfl
  · ihave %Hne := models_lab.errAny_ne_nil $$ Hany
    obtain ⟨ie, rfl⟩ : ∃ ie, err = GoInterface.ok ie := by
      cases err with
      | nil => exact absurd rfl Hne
      | ok i => exact ⟨i, rfl⟩
    wp_auto
    ihave #Hany' := Hany
    unfold models_lab.errAny
    icases Hany' with ⟨%e', %He', -, #HE⟩
    cases He'
    wp_apply HE
    iintro %msg
    wp_auto
    wp_apply wp_errors_New_ne _ msg (by simp) as %err' Herr'
    iapply HΦ
    iright; iexact Herr'

/-- The coordinator is its service (`isCoordSvc`), from the protocol's `assign` and `collect`. -/
theorem coordinator.coord_svc (Hassign : assign.spec (GF := GF)) (Hcollect : collect.spec (GF := GF)) :
    coordinator.coord_svc.spec (GF := GF) (hG := hG) := by
  intro cfg c
  iintro ⟨#Hpkg, #Hc⟩
  unfold isCoordSvc ptrIface
  iexists ⟨go.GoType.PointerType coordinator.Coordinator.ty, #c⟩
  isplitr
  · ipureintro; rfl
  imodintro
  isplit
  · iintro %a %Φ %ha Ht HΦ
    iapply wp_AddNode cfg c a ha $$ [Ht] HΦ
    iframe Hpkg Hc Ht
  isplit
  · iintro %k %sl %x %Q %Φ #Hsl HAU HΦ
    iapply wp_Write Hassign Hcollect cfg c k sl x Q $$ [HAU] HΦ
    iframe Hpkg Hc Hsl HAU
  · iintro %a %Φ HΦ
    iapply wp_RemoveNode cfg c a $$ [] HΦ
    iframe Hpkg Hc

end proof

end github_com.despreston.go_craq

end Perennial
