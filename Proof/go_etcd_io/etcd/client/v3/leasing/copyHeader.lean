/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/copyHeader.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.copyHeader
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.ResponseHeader__GetClusterId
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.ResponseHeader__GetMemberId
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.ResponseHeader__GetRevision
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.ResponseHeader__GetRaftTerm
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.ResponseHeader__GetLeaderId

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem copyHeader.wp_proof
    (hcid : ResponseHeader.GetClusterId.spec (GF := GF) (hG := hG))
    (hmid : ResponseHeader.GetMemberId.spec (GF := GF) (hG := hG))
    (hrev : ResponseHeader.GetRevision.spec (GF := GF) (hG := hG))
    (hraft : ResponseHeader.GetRaftTerm.spec (GF := GF) (hG := hG))
    (hlead : ResponseHeader.GetLeaderId.spec (GF := GF) (hG := hG)) :
    copyHeader.spec (GF := GF) (hG := hG) := by
  intro h hm
  wp_start as Hh
  unfold headerOk
  by_cases hn : h = null
  · subst hn
    wp_auto
    iapply HΦ
    ileft; ipureintro; exact ⟨rfl, rfl⟩
  · simp only [hn, ↓reduceIte]
    unfold hdrFull
    icases Hh with ⟨%-, #Hc, #Hm, #Hr, #Ht, #Hl⟩
    wp_auto
    rw [decide_eq_false hn]
    wp_auto
    wp_apply hcid $$ [$Hc]
    · ipureintro; exact hn
    wp_apply hmid $$ [$Hm]
    · ipureintro; exact hn
    wp_apply hrev $$ [] as -
    · unfold hdrAt; iright; iframe #; ipureintro; exact hn
    wp_apply hraft $$ [$Ht]
    · ipureintro; exact hn
    wp_apply hlead $$ [$Hl]
    · ipureintro; exact hn
    wp_alloc h' as Hh'
    ihave %Hnn' := typedPointsto_not_null $$ Hh'
    iStructNamed Hh'
    ipersist ClusterId
    ipersist MemberId
    ipersist Revision
    ipersist RaftTerm
    ipersist LeaderId
    wp_auto
    iapply HΦ
    iright
    iframe #
    ipureintro; exact ⟨hn, Hnn'⟩

end proof

end leasing
end EtcdGrove
end Perennial
