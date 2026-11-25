/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/authN/newUserClient.lean` (auth3's proof, copied into authN, 2026-11-15; first written
2026-11-14): authkv's proof, verbatim. Lean-first (no Rocq counterpart). As `etcdstart.NewClient`'s and `NewClients`': the
endpoint's slice literal (read-only from here on), then `New` over `clientCfgOk` of the
configuration's literal, with the user's credentials registered (`clientAuthPre`'s second
disjunct).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.authN.newUserClient

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_authN

open Iris Iris.BI Iris.ProofMode client

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.authN.Assumptions]

theorem newUserClient.wp_proof (wp_New : clientv3.New.spec (GF := GF) (hG := hG)) :
    newUserClient.spec (GF := GF) (hG := hG) := by
  intro addr name pw lg V P Hpe Htb Hsz
  wp_start as ⟨Hlt, #Hzlg, #Hce, #Hreg⟩
  ihave %Hlg := zapLoggerOk_ne_null lg $$ Hzlg
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
  haveI : ThreadBoundLe GF (2 ^ 30) := ⟨by omega⟩
  wp_apply (wp_New _ [addr] V P) $$ [$Hlt] as %cl %cerr ⟨Hlt, Hcl⟩
  · iframe #
    iunfold clientCfgOk
    simp only
    iframe #
    isplitr
    · isplitr
      · iapply ownSlice_nil
      ipureintro
      refine ⟨?_, ?_⟩
      · exact plainEndpoints_singleton _ Hpe
      · simp [Hlg]
    iunfold clientAuthPre
    iright
    iframe #
    ipureintro; exact ⟨Htb, Hsz⟩
  iapply HΦ
  iframe Hlt
  iexact Hcl

end proof

end etcd_authN
end EtcdGrove
end Perennial
