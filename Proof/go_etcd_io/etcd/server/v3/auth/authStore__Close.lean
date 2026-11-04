/-
Proof of the spec of the same name (R2b-3c part 2, 2026-11-04). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__Close

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.authStore.Close.wp_proof : auth.authStore.Close.spec (GF := GF) (hG := hG) := by
  intro st R M
  wp_start as ⟨#Hinv, Htpa⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hinv' := Hinv
  iunfold authInv at Hinv'
  icases Hinv' with ⟨%Hst, -, -, -, -, #Hguard, -⟩
  iunfold tpAdmin at Htpa
  icases Htpa with ⟨%tp, %Atp, #Htp, #HtpokA, HA⟩
  ihave #Htpok := HtpokA
  iunfold tokenProviderOkA at Htpok
  icases Htpok with ⟨%tpi, %Htpi, -, -, #HDisable, -, -, -⟩
  subst Htpi
  (try wp_auto)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hguard] as ⟨Hlk, HP⟩
  iunfold enabledP at HP
  icases HP with ⟨%en', Hen', #Hev', Hg⟩
  (try wp_auto)
  cases en'
  · -- disabled: nothing
    (try wp_auto)
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hen' Hg]
    · inext; iunfold enabledP; iexists false; iframe Hen' Hg; iexact Hev'
    (try wp_auto)
    iapply HΦ
    isplitr
    · ipureintro; rfl
    iunfold tpAdmin; iexists (GoInterface.ok tpi), Atp; iframe HA; iframe #
  -- enabled: the provider's `disable()`
  (try wp_auto)
  wp_bind (App (Val #(methods tpi.ty go!"disable" tpi.v)) (Val #()))
  iapply HDisable $$ [HA] [-]
  · iexact HA
  inext
  iintro HA
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hen' Hg]
  · inext; iunfold enabledP; iexists true; iframe Hen' Hg; iexact Hev'
  (try wp_auto)
  iapply HΦ
  isplitr
  · ipureintro; rfl
  iunfold tpAdmin; iexists (GoInterface.ok tpi), Atp; iframe HA; iframe #

end proof

end EtcdGrove
end Perennial
