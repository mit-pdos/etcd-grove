/-
Proof of `Spec/github_com/prometheus/client_golang/prometheus/MustRegister.lean`: client_golang's real
`MustRegister(cs...)` (route (b), notes/prom-registry.md, "Step 2"), `DefaultRegisterer.MustRegister(cs...)`
through the `Registerer` interface (prometheus's fact: the default registry), over
`(*Registry).MustRegister`'s spec. (Until 2026-11-22 the trust-boundary axiom
`prometheus.MustRegister.wp_proof`, over the right `nameFree n`.)
-/
module

public import Spec.github_com.prometheus.client_golang.prometheus.MustRegister
public import Spec.github_com.prometheus.client_golang.prometheus.Registry__MustRegister

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

theorem prometheus.MustRegister.wp_proof
    (wp_MustRegister : prometheus.Registry.MustRegister.spec (GF := GF) (hG := hG)) :
    prometheus.MustRegister.spec (GF := GF) (hG := hG) := by
  intro x s dq c n hn
  wp_start as ⟨Hs, #Hc, Htoks⟩
  ihave #Hp := promInit_of_isPkgInit $$ Hpkg
  iunfold promInit at Hp
  icases Hp with ⟨%r, #Hdr, #HDR, #Hreg⟩
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  icases prometheus.collectorName_desc c n hn $$ Hc with ⟨%p, %d, #Hdesc, #Hps, %Hd⟩
  obtain ⟨Hok, Hkeys⟩ := Hd
  wp_auto
  wp_apply (wp_MustRegister (prometheus.PromRegGS.γ (GF := GF)) r s dq c [p] [d]) $$ [Hs Htoks] as Hs
  · rw [Hkeys]
    iframe
    iframe #
    ipureintro; exact Hok
  (try wp_auto)
  iapply HΦ $$ Hs

end proof

end EtcdGrove
end Perennial
