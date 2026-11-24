/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/B/Run.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit B: `run()` and `SetForceWrite()` (`src/gryff/tupaq.go`).
-/
module

public import Dsverify.Proof.gryff.B.Loop
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.unitB

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open model replica2
open github_com.goose_lang.primitive (ProphId)

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]

theorem SetForceWrite_proof (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ isReplica γ ρ k r }}
      (App (repMB r go!"SetForceWrite") (Val #()))
    {{ RET #(); True }} := by
  unfold repMB
  wp_start as #Hrep
  icases (isReplica_open γ ρ k r).1 $$ Hrep with
    ⟨%gR, %h', #Hexec, #HgR, #Hshut, #Hproxy, #HsctR, #Hbeacon, #Hdreply, #Hdur, #Hchans, #Hgen⟩
  iunfold replicaChans at Hchans
  iunfold bagAt at Hchans
  icases Hchans with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    ⟨%c_fw, #Hf_fw, #Hb_fw⟩, -⟩
  wp_auto
  ihave HI : (True : IProp GF) $$ []
  · itrivial
  wp_for HI
  wp_apply time.wp_Sleep
  wp_apply (wp_bag_send (ρ.chans "forceWrite") c_fw true (fun _ : Bool => iprop(True))) $$ []
  · iframe #
  wp_for_post
  iframe

theorem wp_dlog_Println (v : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.dlog ∗
        globalAddr gryff.src.dlog.DLOG ↦□ false }}
      (App (Val (@! gryff.src.dlog.Println)) (Val #v))
    {{ RET #(); True }} := by
  wp_start as #Hd
  wp_auto
  wp_end

set_option hygiene false in
/-- `run`'s tail after the `shortcircuitTime` test (both branches). -/
local macro "run_rest" : tactic => `(tactic| (
  try wp_auto
  wp_apply wp_fork $$ [Hlis]
  · wp_method_call
    wp_call
    wp_auto
    wp_apply hWait $$ [Hlis]
    · iframe; iframe #
    itrivial
  ihave HI : loopTok γ ρ k r $$ [Htok]
  · iexact Htok
  wp_for HI
  try simp only [_root_.decide_true, decide_eq_true_eq, ↓reduceIte, ite_true]
  try wp_auto
  wp_apply (hLoop h' sc γsc) $$ [HI] as HI
  · iframe; iframe #
  wp_for_post
  iframe))

/-- `run()`, with the handlers' and the generic replica's specs as hypotheses (their units');
`CR`, `LO` are unit N's `connectRes`, `listenerOwn` (`Replica2/Specs.lean`). -/
theorem run_proof (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR : Loc)
    (CR LO : IProp GF)
    (hCTP : {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr ∗ isReplica γ ρ k r ∗
        r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ CR }}
      (App (Val (gR @!! go.GoType.PointerType src.genericsmr.Replica.ty @!! go!"ConnectToPeers"))
        (Val #()))
    {{ RET #(); loopTok γ ρ k r ∗ LO }})
    (hWait : {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr ∗ isReplica γ ρ k r ∗
        r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ LO }}
      (App (Val (gR @!! go.GoType.PointerType src.genericsmr.Replica.ty @!!
        go!"WaitForClientConnections")) (Val #()))
    {{ RET #(); True }})
    (hLoop : ∀ (h sc : Loc) (γsc : ChanNames),
      {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ isReplica γ ρ k r ∗
        handlerOfB r h ∗ isChanBag γsc sc (fun _ : Bool => iprop(False)) ∗ loopTok γ ρ k r }}
      (App (epMB h go!"Loop") (Val #sc))
    {{ RET #(); loopTok γ ρ k r }}) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ isReplica γ ρ k r ∗
        r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ CR }}
      (App (repMB r go!"run") (Val #()))
    {{ RET #(); True }} := by
  unfold repMB
  wp_start as ⟨#Hrep, #HgR0, Hcr⟩
  icases (isReplica_open γ ρ k r).1 $$ Hrep with
    ⟨%gR', %h', #Hexec, #HgR, #Hshut, #Hproxy, #HsctR, #Hbeacon, #Hdreply, #Hdur, #Hchans, #Hgen⟩
  icombine HgR0 HgR gives %HgRR
  subst HgRR
  icases (isExec_open γ ρ k r h').1 $$ Hexec with
    ⟨%gR'', %mtx, %ex, %pr, #HgR'', #Hh', -⟩
  icombine HgR0 HgR'' gives %HgR2
  subst HgR2
  ihave #Hdlog : globalAddr gryff.src.dlog.DLOG ↦□ false $$ []
  · iapply replica.dlog_init_access; iPkgInit
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  wp_apply hCTP $$ [Hcr] as ⟨Htok, Hlis⟩
  · iframe; iframe #
  wp_apply wp_slice_literal (V := GoInterface) _
  isplitr
  · ipureintro; rfl
  iintro %_ ⟨-, -⟩
  wp_auto
  wp_apply wp_dlog_Println $$ [$Hdlog]
  wp_apply (chan.wp_make2 (V := Bool) (W64 1)) $$ [] as %sc %γsc ⟨#Hsc, -, Hoc⟩
  · ipureintro; decide
  imod start_bag (fun _ : Bool => iprop(False)) _ sc γsc (by simp) $$ Hsc Hoc with #Hbag
  try wp_auto
  wp_apply wp_fork $$ []
  · wp_apply SetForceWrite_proof $$ []
    · iframe #
    itrivial
  run_rest

end

end Perennial.gryff.unitB
