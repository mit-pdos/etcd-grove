/-
Proof of `Spec/go_etcd_io/etcd/client/pkg/v3/verify/Assert.lean`. `Assert` is translated with its
body (2026-10-26; the rest of `verify` stays names-only: its package reads `ETCD_VERIFY`); the
trust boundary until then. Of a true condition the `panic` branch (formatting the message with
`fmt.Sprintf` of `...any`) is not taken.
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.verify.Assert

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.pkg.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.pkg.v3.verify.Assumptions]

theorem verify.Assert.wp_proof : verify.Assert.spec (GF := GF) (hG := hG) := by
  intro msg v
  wp_start
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
