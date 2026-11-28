/-
The proof of `Client.Go` (`Net/Spec/net/rpc/Client__Go.lean`): a new `*Call`, its fields stored and
made read-only (but `Error`), the channel's capacity checked (`cap`, positive: no panic), then
`send`.
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
variable [package_sem' : net.rpc.Assumptions]
variable [π : NetProtoGS]

theorem Client.Go.wp_proof (wp_send : Client.send.spec (GF := GF) (hG := hG)) :
    Client.Go.spec (GF := GF) (hG := hG) := by
  intro c W a γ sm svc M S args reply done γt γf K Φm Rargs D Θ C
  wp_start as ⟨#Hcl, %Hsv, ⟨%Hdn, %Hcap⟩, %Hsm, #Hset, Henc, HD, #Hdec, Hγt, Hdone⟩
  wp_auto
  rename_i pc
  ihave %Hpc := typedPointsto_not_null $$ «$r0»
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
  wp_apply wp_send c W a γ «$r0_ptr» sm svc M S args reply done γt γf K Φm Rargs D Θ C
      $$ [$Hcl $Hset $Henc $HD $Hdec $Hγt $Hf $Error Hfut Hful HK] as ⟨%o, #Ho, Hres⟩
  · isplitr
    · ipureintro; exact ⟨Hsv.1, Hsv.2.1, Hsv.2.2, Hpc⟩
    isplitr
    · ipureintro; exact Hsm
    iunfold callDone
    iframe Hfut Hful HK
  iapply HΦ
  iframe Hf
  iexists o
  iframe Ho Hres

end proof

end net.rpc
end Perennial
