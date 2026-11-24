/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/NewMember.lean`: `computeMemberID`
then `newMember`. Lean-first (no Rocq counterpart). (An interim trust-boundary axiom until 2026-11-24,
`notes/axiom-review/membership-NewMember.md`: retired by this proof once `computeMemberID` was translated
with its body over Perennial's `hash`.)
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.NewMemberOne
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.computeMemberIDOne
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.newMemberOne

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

theorem membership.NewMember.wp_proofOne
    (hCompute : membership.computeMemberID.specOne (GF := GF) (hG := hG))
    (hNew : membership.newMember.specOne (GF := GF) (hG := hG)) :
    membership.NewMember.specOne (GF := GF) (hG := hG) := by
  intro name sl p token hfips
  wp_start as #Hsl
  wp_auto
  wp_apply (hCompute sl (membership.urlHttp p) token hfips) $$ [] as %id %hid
  · iframe #
  wp_apply (hNew name sl [membership.urlHttp p] id false) $$ [] as %m %mv ⟨Hm, %hmv⟩
  · iframe #
  iapply HΦ
  iframe
  ipureintro
  intro hp
  rw [hmv]
  exact hid hp

end proof

end EtcdGrove
end Perennial
