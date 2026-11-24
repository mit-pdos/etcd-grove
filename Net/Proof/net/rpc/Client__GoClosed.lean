/-
The proof of `Client.Go.spec_closed` (`Net/Spec/net/rpc/Client__Go.lean`): `Client.Go`'s proof
(`Client__Go.lean`) with `send`'s refusal (`Client.send.spec_closed`).
-/
module

public import Net.Spec.net.rpc.Client__Go
public import Net.Spec.net.rpc.Client__send

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.rpc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

theorem Client.Go.wp_proof_closed (wp_send : Client.send.spec_closed (GF := GF) (hG := hG)) :
    Client.Go.spec_closed (GF := GF) (hG := hG) := by
  intro c W a γ sm args reply done γt γf K Φm D Θ
  wp_start as ⟨#Hcl, #Hclo, ⟨%Hdn, %Hcap⟩, HD, Hγt, Hdone⟩
  wp_auto
  rename_i pc
  rw [decide_eq_false (show done ≠ chan.nil from Hdn)]
  iunfold callDone at Hdone
  icases Hdone with ⟨#Hfut, Hful, HK⟩
  ihave #Hch : isChan done γf.chanName Loc $$ []
  · iunfold isFuture at Hfut; icases Hfut with ⟨$, -⟩
  wp_auto
  wp_apply (chan.wp_cap (V := Loc) done γf.chanName) $$ Hch
  have hc : γf.chanName.chanCap ≠ W64 0 := by
    intro h; rw [h] at Hcap; exact absurd Hcap (by decide)
  rw [decide_eq_false hc]
  wp_auto
  iStructNamed «$r0»
  ipersist ServiceMethod
  ipersist Args
  ipersist Reply
  ipersist Done
  ihave #Hf : callFields «$r0_ptr» sm args reply done $$ []
  · iunfold callFields
    iframe ServiceMethod Args Reply Done
  wp_apply wp_send c W a γ «$r0_ptr» sm args reply done γt γf K Φm D Θ
      $$ [$Hcl $Hclo $HD $Hγt $Hf $Error Hfut Hful HK] as #Ho
  · iunfold callDone
    iframe Hfut Hful HK
  iapply HΦ
  iframe Hf Ho

end proof

end net.rpc
end Perennial
