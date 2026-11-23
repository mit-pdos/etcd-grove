/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/tcp/ClientTcpInit.lean`, run
`rabia-r1wake-1`.)

The proof of `rabia/internal/tcp.ClientTcpInit`.
-/
module

public import Dsverify.Proof.rabia.internal.tcp.Hub

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.rabia.internal.tcp

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode model Net rabia
  rabia.internal.message rabia.internal.config

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [π : NetProtoGS]
variable [sem : go.Semantics] [package_sem : rabia.internal.tcp.Assumptions] [sync.Assumptions]

set_option goose.wp.extras true

theorem ClientTcpInit.wp_proof : ClientTcpInit.spec (GF := GF) := by
  intro γ cf c addr hc
  wp_start as #Hconf
  unfold confRO
  icases Hconf with ⟨-, %ps, #Hconf, #Hps⟩
  ihave Hc2 := Hconf
  iStructNamed Hc2
  wp_auto
  wp_apply (chan.wp_make1 (V := Unit)) as %done %γd ⟨#Hdone, -, Hdo⟩
  wp_apply (chan.wp_make2 (V := Command) (W64 500000)) as %rc %γrc ⟨#Hrc, -, Hrco⟩
  · ipureintro; decide
  wp_apply +noauto (chan.wp_make2 (V := Command) (W64 500000)) as %sc %γsc ⟨#Hsc, -, Hsco⟩
  · ipureintro; decide
  imod start_bag (doneP (GF := GF)) .Idle done γd (by simp) $$ Hdone Hdo with #Hdb
  imod start_bag (repP (GF := GF) γ c.toNat) (.Buffered []) rc γrc (by simp) $$ Hrc Hrco with #Hrb
  imod start_spsc sc (clSendP (GF := GF) γ c.toNat) (fun _ => iprop(False)) γsc $$ Hsc [Hsco]
    with ⟨%γs, #Hsb, Hprod, Hcons⟩
  · iright; iexact Hsco
  imod wg_alloc «$v1_ptr» 2 (by decide) $$ «$v1» with Hwg
  wp_pures
  wp_alloc t as Ht
  iStructNamed Ht
  ipersist Id
  ipersist Wg
  ipersist Done
  ipersist ProxyAddr
  ipersist RecvChan
  ipersist SendChan
  wp_auto
  iapply HΦ
  iexists ⟨γs, γrc⟩
  iframe Hprod
  ihave #Hchans : clientChans γ c.toNat ⟨γs, γrc⟩ t $$ []
  · unfold clientChans
    iexists sc, rc
    iframe #
  iframe Hchans
  unfold clientOwn doneChan
  iexists «$v1_ptr», done, null, null, null
  iframe Hwg Hcons Conn Reader Writer
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  iframe #

end proof

end Perennial.rabia.internal.tcp
