/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/newMember.lean` (claim #34, stage 2,
2026-11-25). Lean-first. The URLs' strings (`StringSlice`, plain) into a fresh `Member` literal.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.newMember
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
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem membership.newMember.wp_proof
    (hSS : types.URLs.StringSlice.specP (GF := GF) (hG := hG)) :
    membership.newMember.spec (GF := GF) (hG := hG) := by
  intro name sl us id il Hplain
  wp_start as #Hus
  wp_auto
  ihave #Htpk : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types $$ []
  · iPkgInit
  wp_apply (hSS peerURLs_ptr (DFrac.own 1) sl us Hplain) $$ [peerURLs] as %out ⟨-, Hout⟩
  · iframe #; iframe peerURLs
  (try wp_auto)
  ihave %Hr0nn := typedPointsto_not_null _ _ _ $$ «$r0»
  iStructNamed «$r0»
  iStructNamed RaftAttributes
  iStructNamed Attributes
  have hstr : (us.map fun u => go!"http://" ++ u.Host') = us.map membership.urlStrOf := rfl
  rw [hstr]
  iapply HΦ
  iunfold membership.memberAt
  simp only
  isplitr
  · ipureintro; exact Hr0nn
  iexists out, _
  iframe
  iapply ownSlice_nil

end proof

end EtcdGrove
end Perennial
