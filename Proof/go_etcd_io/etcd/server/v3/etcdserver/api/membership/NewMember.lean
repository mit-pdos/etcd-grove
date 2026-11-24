/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/NewMember.lean` (claim #34, stage 2,
2026-11-25). Lean-first. `computeMemberID`, then `newMember` with that id, a voter.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.NewMember
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.computeMemberID
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.newMember

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem membership.NewMember.wp_proof
    (hCID : membership.computeMemberID.spec (GF := GF) (hG := hG))
    (hNM : membership.newMember.spec (GF := GF) (hG := hG)) :
    membership.NewMember.spec (GF := GF) (hG := hG) := by
  intro name sl us token Hfips Hplain Hlen
  wp_start as #Hus
  wp_auto
  wp_apply (hCID sl us token Hfips Hplain Hlen) $$ [] as -
  · iframe #
  (try wp_auto)
  wp_apply (hNM name sl us _ false Hplain) $$ [] as %m Hm
  · iframe #
  (try wp_auto)
  iapply HΦ
  unfold membership.memberOfURLs
  iexact Hm

end proof

end EtcdGrove
end Perennial
