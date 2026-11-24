/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/N/Register.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit N: `GetClientWriter` (and the generic replica's small methods)
-/
module

public import Dsverify.Proof.gryff.N.StateLaws
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]


/-- What `GetClientWriter` reads of `genericOk`: the client maps' mutex and its invariant. -/
theorem genericOk_clients (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc) :
    genericOk γ ρ k r gR h ⊢ ∃ (mu cwm crm : Loc),
      gR.[src.genericsmr.Replica, go!"clientIdMapsLock"] ↦□ mu ∗
      gR.[src.genericsmr.Replica, go!"clientWriters"] ↦□ cwm ∗
      sync.isMutex mu iprop(∃ (RM WM : GMap w32 Loc), crm ↦$ RM ∗ cwm ↦$ WM ∗
        ghostMapAuth ρ.writers (1 : Qp).half WM ∗
        [∗map] hs ↦ _w ∈ WM, ∃ c : Nat, clientConnAt γ hs c ∗ placedConn γ c) := by
  unfold genericOk
  iintro #H
  icases H with ⟨%rt, %ct, %st, %mu, %cwm, %crm, %M, %CM, -, -, -, -, -, -, -, -, #Hmu, #Hcw, -,
    #Hm, -⟩
  iexists mu, cwm, crm
  iframe #

set_option goose.wp.extras true

theorem GetClientWriter_wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3)
    (r gR h : Loc) (cid : w32) (w : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr ∗ genericOk γ ρ k r gR h ∗
        writerIs ρ cid w }}
      (App (Val (gR @!! go.GoType.PointerType src.genericsmr.Replica.ty @!! go!"GetClientWriter"))
        (Val #cid))
    {{ RET #w; True }} := by
  wp_start as ⟨#Hgen, Hw⟩
  ihave ⟨%mu, %cwm, %crm, #Hmuf, #Hcw, #Hmu⟩ := genericOk_clients γ ρ k r gR h $$ Hgen
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, ⟨%RM, %WM, Hrm, Hwm, Hauth, Hpl⟩⟩
  unfold writerIs
  ihave %Hlk := ghost_map_lookup $$ Hauth Hw
  wp_apply (wp_map_lookup2 (V := Loc) go.int32 _ cwm WM cid (DFrac.own 1)) $$ Hwm as Hwm
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hrm Hwm Hauth Hpl]
  · iexists RM, WM; iframe
  rw [Hlk]
  simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
  wp_auto
  iapply HΦ; itrivial

end

end Perennial.gryff.replica2
