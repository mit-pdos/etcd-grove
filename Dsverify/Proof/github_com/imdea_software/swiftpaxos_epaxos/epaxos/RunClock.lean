/-
The clock channels (`r.slowClockChan`, `r.fastClockChan`: `Replica` fields, fork workaround
EP-GLOBALS) and the `slowClock` goroutine.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.RunCalls

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [GooseExts]

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : StateTreemap GF]

/-- A clock channel field's value (`r.slowClockChan`, `r.fastClockChan`: fork workaround
EP-GLOBALS): `nil` or a channel whose contents carry nothing (`isChanBag`, never closed:
`slowClock`'s `r.slowClockChan <- true`, the run loop's `select`; `fastClockChan` is never sent
on, `batchWait` being 0). `run` stores both before it starts `slowClock`; read-only after. -/
def epaxosClockChanOk (ch : GoChan) : IProp GF :=
  iprop(⌜ch = null⌝ ∨ ∃ γc : ChanNames, isChanBag (V := Bool) γc ch (fun _ => iprop(True)))

instance epaxosClockChanOk_persistent (ch : GoChan) :
    Persistent (epaxosClockChanOk (GF := GF) ch) := by
  unfold epaxosClockChanOk; infer_instance

/-- A clock channel field, set (read-only) with its channel. (A plain definition, so that
`wp_auto` stops at its loads: `wp_loadClock` takes the step with its later credits.) -/
def clockFld (r : Loc) (X : GoString) (ch : GoChan) : IProp GF :=
  iprop(efld r X ↦□ ch ∗ epaxosClockChanOk ch)

instance clockFld_persistent (r : Loc) (X : GoString) (ch : GoChan) :
    Persistent (clockFld (GF := GF) r X ch) := by
  unfold clockFld; infer_instance

/-- Reading a clock field. -/
theorem wp_loadClock (r : Loc) (X : GoString) (ch : GoChan) :
    ⊢ ∀ Φ : val → IProp GF, clockFld r X ch -∗ (epaxosClockChanOk ch -∗ Φ #ch) -∗
      WP (App (Val (GoInstruction (GoLoad (go.GoType.ChannelType go.ChanDir.sendrecv go.bool))))
        (Val #(efld r X))) {{ Φ }} := by
  iintro %Φ #H HΦ
  unfold clockFld
  icases H with ⟨#Hf, #Hok⟩
  wp_auto
  iapply HΦ
  iexact Hok

set_option maxHeartbeats 1000000 in
/-- A send on a nil channel blocks forever. -/
theorem wp_send_nil (v : Bool) (Φ : val → IProp GF) :
    ⊢ WP (App (App (Val (chan.send go.bool)) (Val #(null : Loc))) (Val #v)) {{ Φ }} := by
  unfold chan.send
  wp_call
  wp_method_call
  wp_call
  wp_auto
  wp_for
  wp_for_post
  iframe

/-- `r.slowClock()` (never returns): sends `true` on `slowClockChan` every 150 ms. -/
theorem wp_slowClock (r rr : Loc) (ch : GoChan) :
    {{ pkgInit_epaxos (GF := GF) ∗ efld r go!"Replica" ↦□ rr ∗ fld rr go!"Shutdown" ↦□ false ∗
        clockFld r go!"slowClockChan" ch }}
      (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"slowClock")) (Val #()))
    {{ RET #(); False }} := by
  wp_start as ⟨#Hrr, #Hsh, #Hsc⟩
  wp_auto
  wp_for
  wp_apply time.wp_Sleep
  wp_apply wp_loadClock $$ Hsc as #Hok
  unfold epaxosClockChanOk
  icases Hok with (%Hnil | ⟨%γc, #Hbag⟩)
  · subst Hnil
    wp_apply wp_send_nil
  · wp_apply (wp_bag_send (V := Bool) γc ch true _) $$ [$Hbag]
    wp_for_post
    iframe

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
