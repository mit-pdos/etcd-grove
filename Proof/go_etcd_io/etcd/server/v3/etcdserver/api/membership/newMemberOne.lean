/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/newMember.lean`: the URL strings
(`StringSlice`), the member's literal, allocated. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.newMemberOne
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.URLs__StringSlice

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Assumptions]

theorem membership.newMember.wp_proofOne
    [go_etcd_io.etcd.client.pkg.v3.types.Assumptions]
    (hSS : types.URLs.StringSlice.spec (GF := GF) (hG := hG)) :
    membership.newMember.specOne (GF := GF) (hG := hG) := by
  intro name sl us id l
  wp_start as #Hsl
  wp_auto
  wp_apply (hSS peerURLs_ptr (DFrac.own 1) sl us) $$ [peerURLs] as %out ⟨peerURLs, %ss, Hout, %Hss⟩
  · iframe; iframe #
  iapply HΦ
  iframe
  ipureintro; rfl

end proof

end EtcdGrove
end Perennial
