/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/system/SigListen.lean`, run `rabia-r1wake-1`.)

The proof of `SigListen` (`SigListen.spec`): `sigIn` is a fresh channel that `signal.Notify(sigIn,
SIGINT, SIGTERM)` (the environment assumption `os.signal.NoSignals`: nobody sends those two) never sends on, a bag of `False`; `done` a bag of `False` (the premise): the `select` never
fires.
-/
module

public import Dsverify.Proof.rabia.internal.system.Spec
public import Dsverify.Proof.os.signal.Spec

@[expose] public section

noncomputable section

namespace Perennial.rabia.internal.system

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : rabia.internal.system.Assumptions]
variable [os.signal.NoSignals os.signal.quietSigs GF]

omit package_sem in
/-- A channel's `isChan` says it is not `nil` (here of `os.Signal`). -/
theorem isChan_ne_nil_signal (ch : GoChan) (γ : ChanNames) :
    isChan (GF := GF) ch γ os.Signal ⊢ ⌜ch ≠ chan.nil⌝ := by
  rw [isChan_unseal]
  iintro H
  iNamed H
  ipureintro; exact Hnotnull

set_option goose.wp.extras true in
theorem SigListen.wp_proof : SigListen.spec (GF := GF) := by
  intro done γ
  wp_start as #Hdone
  wp_auto
  wp_apply chan.wp_make2 (V := os.Signal) as %ch %γs ⟨#Hch, %Hcap, Hown⟩
  · ipureintro; decide
  imod start_bag (V := os.Signal) (fun _ => iprop(False)) _ ch γs (by simp) $$ Hch Hown with #Hsig
  wp_apply wp_slice_literal (V := os.Signal) (l := os.signal.quietSigs) _
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, _⟩
  wp_auto_lc 2
  ihave %Hnn := isChan_ne_nil_signal _ _ $$ Hch
  wp_apply (os.signal.NoSignals.notifyQuiet (sigs := os.signal.quietSigs) (GF := GF))
    (List.cons_ne_nil _ _) _ _ _ Hnn $$ [$Hsl] as -
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, done, γ
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hdone
    iapply bag_recv_au _ _ _ _ $$ [$Hlc1 $Hlc2] Hdone
    inext
    iintro %v Hv
    iexfalso; iexact Hv
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists os.Signal, inferInstance, inferInstance, inferInstance, inferInstance, ch, γs
    isplitr
    · ipureintro; rfl
    isplitr
    · iexact Hch
    iapply bag_recv_au _ _ _ _ $$ [$Hlc1 $Hlc2] Hsig
    inext
    iintro %v Hv
    iexfalso; iexact Hv
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end Perennial.rabia.internal.system
