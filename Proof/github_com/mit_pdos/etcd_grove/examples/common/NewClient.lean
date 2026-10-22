/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/common/NewClient.lean` (2026-10-22, D33).
Lean-first (no Rocq counterpart).

The endpoints' slice literal (read-only from here on), then `clientv3.New` (`clientCfgOk` from the
configuration's literal: one plain endpoint, no dial options, no TLS, no credentials, the logger),
whose result is returned.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.common.NewClient

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace common

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.common.Assumptions]

theorem NewClient.wp_proof
    (wp_New : clientv3.New.spec (GF := GF) (hG := hG)) :
    NewClient.spec (GF := GF) (hG := hG) := by
  intro addr lg V Hlg Hpl Htb
  wp_start
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
  wp_apply (wp_New _ [addr] V) $$ [] as %cl %cerr Hcl
  · iframe #
    iunfold clientCfgOk
    simp only
    iframe #
    isplitr
    · isplitr
      · iapply ownSlice_nil
      ipureintro
      refine ⟨?_, ?_⟩
      · exact plainEndpoints_singleton _ Hpl
      · simp [Hlg]
    ipureintro; exact Htb
  (try wp_auto)
  iapply HΦ
  iexact Hcl

end proof

end common
end EtcdGrove
end Perennial
