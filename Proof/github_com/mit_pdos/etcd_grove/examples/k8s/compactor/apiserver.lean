/-
The proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8s/compactor/apiserver.lean`. Lean-first.

The compactor's contracts come from the invariant (`casOk_of_cinv`, `keyReadOk_of_cinv`, at
`Seen := seenOk γ`, `recorded := True`): its own (`NewCompactor`, no `onClose`) or the process's
(`StartCompactorPerEndpoint`, with the endpoints' claims); then `check`, through the interface.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.apiserver
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.NewCompactor
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.StartCompactorPerEndpoint
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.check
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Aus

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_compactor

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver k8s

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [sync_sem : sync.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Assumptions]

theorem apiserver.wp_proof
    (wp_NewCompactor : k8s.NewCompactor.spec (GF := GF) (hG := hG))
    (wp_StartCompactorPerEndpoint : k8s.StartCompactorPerEndpoint.spec (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG)) :
    apiserver.spec (GF := GF) (hG := hG) := by
  intro _ _ _ _ cl ms V γr γk γ shared hsame hcmp hcret
  wp_start as ⟨#Hcl, #Hone, #Hregs, #Hst, #Hko, #Hwo, #Heps, #Hinv, #Hkvi⟩
  ihave #Pe3 : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 $$ []
  · iPkgInit
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Hcas := casOk_of_cinv ms γk hsame γ $$ Hinv
  ihave #Hkr := keyReadOk_of_cinv γk γ $$ Hinv
  wp_auto
  cases shared
  · (try wp_auto)
    wp_apply (wp_NewCompactor cl ms V γk (seenOk γ) (fun _ => iprop(True)) _ _ _ hsame hcmp hcret
        (by decide)) $$ [] as %c %γc ⟨#Hc, #H0⟩
    · iframe #
      -- no `onClose`
      iapply k8s.closeOk_nil
    (try wp_auto)
    wp_apply (wp_check cl ms V γr γk γ c cl γc hsame) $$ []
    · iframe #
    (try wp_auto)
    iapply HΦ; itrivial
  · (try wp_auto)
    wp_apply (wp_StartCompactorPerEndpoint cl ms V γk (seenOk γ) (fun _ => iprop(True)) _ hsame
        hcmp hcret (by decide)) $$ [] as %c ⟨%cl', %γc, #Hc, #H0⟩
    · iframe #
    (try wp_auto)
    wp_apply (wp_check cl ms V γr γk γ c cl' γc hsame) $$ []
    · iframe #
    (try wp_auto)
    iapply HΦ; itrivial

end proof

end k8s_compactor
end EtcdGrove
end Perennial
