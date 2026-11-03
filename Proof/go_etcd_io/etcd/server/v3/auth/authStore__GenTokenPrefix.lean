/-
Proof of the spec of the same name (C1's A4, 2026-10-29): the provider's `genTokenPrefix`, through
the store's invariant (`authInv`'s `tokenProviderOk`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__GenTokenPrefix

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

theorem auth.authStore.GenTokenPrefix.wp_proof :
    auth.authStore.GenTokenPrefix.spec (GF := GF) (hG := hG) := by
  intro st R M
  wp_start as Hinv
  iunfold authInv at Hinv
  icases Hinv with ⟨%Hst, -, -, -, ⟨%tp, #Htp, #Htpok⟩, -, -⟩
  iunfold tokenProviderOk at Htpok
  icases Htpok with ⟨%Atp, %ti, %Hti, -, -, -, -, -, #HGtp⟩
  subst Hti
  (try wp_auto)
  wp_apply HGtp as %s %err %Herr
  (try wp_auto)
  iapply HΦ; ipureintro; exact Herr

end proof

end EtcdGrove
end Perennial
