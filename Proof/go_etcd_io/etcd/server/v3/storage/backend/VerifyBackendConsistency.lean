/-
`backend.VerifyBackendConsistency`'s proof (`verify.go`; etcdstorage, 2026-11-20, until then the trust
boundary, an axiom): one `verify.Verify` call, over its spec with assertions off (`EtcdVerifyOff`): its
closure (which locks the backend and compares the buckets) is not run.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.VerifyBackendConsistency
public import Spec.go_etcd_io.etcd.client.pkg.v3.verify.Verify

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [verify_sem : go_etcd_io.etcd.client.pkg.v3.verify.Assumptions]

theorem backend.VerifyBackendConsistency.wp_proof
    (hVerify : verify.Verify.spec (GF := GF) (hG := hG)) :
    backend.VerifyBackendConsistency.spec (GF := GF) (hG := hG) := by
  intro b lg skip bs
  wp_start as %Hvoff
  ihave #Hvpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.verify $$ []
  · iPkgInit
  wp_auto
  wp_apply (hVerify _ _ iprop(True)) $$ []
  · iframe #
    isplitr
    · itrivial
    iright; ipureintro; exact Hvoff
  try wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
