-- The copy for the part `KvRaft/` of `Net/Proof/net/Conn__Close.lean` (etc/copy-part.py; rerun it, do not edit).
/-
The proof of `Net/Spec/net/Conn__Close.lean`: the interface call resolves to
`conn.Close.impl` (`*TCPConn`'s promoted `Close`), the extension's `Close`, taking the caller's
update (`Net.wp_net_Close`).
-/
module

public import KvRaft.Spec.net.Conn__Close
public import KvRaft.Proof.net.Errors

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions] [field_sem : net.FieldAssumptions]
variable [go.BasicIntoValInj]

theorem Conn.Close.wp_proof : Conn.Close.spec (GF := GF) (hG := hG) := by
  intro t cn s a la ra Q
  unfold connAt
  wp_start as ⟨⟨%nw, %Hnw, #Ht, #Hla, #Hra, #Hat⟩, HAU⟩
  wp_method_call
  (try unfold conn.Close.impl)
  (try unfold model.connId)
  (try unfold model.connErr)
  (try rw [conn_ty_eq'])
  ihave #Ht2 := Ht
  iStructNamed Ht2
  iStructNamed conn
  ihave %Hne := netConnAt_endId_ne _ cn a s $$ Hat
  (try wp_auto)
  (try (rw [show decide (endId cn s = W64 0) = false by simpa using Hne]; wp_auto))
  wp_bind (ExternalOp _ _ _)
  iapply wp_net_Close cn s a $$ Hat
  imod HAU with ⟨%st, %d, Hend, Hdir, Hk⟩
  imodintro
  iexists st, d
  iframe Hend Hdir
  iintro %res %st' %d' %Hcr Hend Hdir
  imod Hk $$ %res %st' %d' %Hcr Hend Hdir with HQ
  imodintro
  rcases res with _ | k
  · wp_auto
    iapply HΦ
    iexists none
    iframe HQ
    unfold resErr
    ipureintro; rfl
  · have hk : k = .closed := by
      unfold CloseOutcome at Hcr; split at Hcr
      · exact Option.some.inj Hcr.1
      · cases Hcr.1
    subst hk
    wp_auto
    wp_apply wp_kindErr .closed none go!"close" (· = go!"close") rfl rfl $$ [] as %e #He
    (try wp_auto)
    (try unfold model.connNet)
    (try wp_auto)
    wp_apply wp_opError $$ %Hnw as %err #Herr
    iapply HΦ
    iexists some .closed
    iframe HQ
    unfold resErr
    iexists e
    iframe Herr He

end proof

end net
end Perennial
