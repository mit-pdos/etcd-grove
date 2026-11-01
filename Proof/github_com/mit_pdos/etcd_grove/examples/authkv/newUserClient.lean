/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/authkv/newUserClient.lean` (`notes/authkv-main-plan.md`;
2026-10-30). Lean-first (no Rocq counterpart). As `common.NewClient`'s and `NewClients`': the
endpoint's slice literal (read-only from here on), then `New` over `clientCfgOk` of the
configuration's literal, with the user's credentials registered (`clientAuthPre`'s second
disjunct).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.newUserClient

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI Iris.ProofMode client

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.authkv.Assumptions]

theorem newUserClient.wp_proof (wp_New : clientv3.New.spec (GF := GF) (hG := hG)) :
    newUserClient.spec (GF := GF) (hG := hG) := by
  intro name pw lg V P Hlg Htb Hsz
  wp_start as ⟨#Hce, #Hreg⟩
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %eps ⟨Heps, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  imod ownSlice_persist _ _ _ $$ Heps with #Heps
  -- `clientv3.New(Config{Endpoints: {clientAddr}, ..., Username: name, Password: pw, Logger: lg})`
  wp_apply (wp_New _ [go!"127.0.0.1:23916"] V P) $$ [] as %cl %cerr Hcl
  · iframe #
    iunfold clientCfgOk
    simp only
    iframe #
    isplitr
    · isplitr
      · iapply ownSlice_nil
      ipureintro
      refine ⟨?_, ?_⟩
      · exact plainEndpoints_singleton _ (by unfold plainEndpoint; decide)
      · simp [Hlg]
    isplitr
    · iunfold clientAuthPre
      iright
      iframe #
      ipureintro; exact ⟨Htb, Hsz⟩
    ipureintro; omega
  iapply HΦ
  iexact Hcl

end proof

end authkv
end EtcdGrove
end Perennial
