/-
Proof of `Spec/github_com/prometheus/client_golang/prometheus/Register.lean`: client_golang's real
`Register(c)` (route (b), notes/prom-registry.md, "Step 2"), `DefaultRegisterer.Register(c)` through the
`Registerer` interface (prometheus's fact: the default registry), over `(*Registry).Register`'s spec.
(Until 2026-11-22 the trust-boundary axiom `prometheus.Register.wp_proof`, item 4, whose post was `True`.)
-/
module

public import Spec.github_com.prometheus.client_golang.prometheus.Register
public import Spec.github_com.prometheus.client_golang.prometheus.Registry__Register

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode
open github_com.prometheus.client_golang.prometheus

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.prometheus.client_golang.prometheus.Assumptions]

theorem prometheus.Register.wp_proof
    (wp_Register : prometheus.Registry.Register.spec (GF := GF) (hG := hG)) :
    prometheus.Register.spec (GF := GF) (hG := hG) := by
  intro x c ps ds
  wp_start as ⟨#Hdesc, #Hps, Htoks, %Hok⟩
  ihave #Hp := promInit_of_isPkgInit $$ Hpkg
  iunfold promInit at Hp
  icases Hp with ⟨%r, #Hdr, #HDR, #Hreg⟩
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_apply (wp_Register (prometheus.PromRegGS.γ (GF := GF)) r c ps ds) $$ [Htoks]
  · iframe
    iframe #
    ipureintro; exact Hok
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
