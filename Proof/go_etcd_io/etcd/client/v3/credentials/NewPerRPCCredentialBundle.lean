/-
Proof of `Spec/go_etcd_io/etcd/client/v3/credentials/NewPerRPCCredentialBundle.lean` (the auth
plan's E2d). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.credentials.NewPerRPCCredentialBundle

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.credentials.Assumptions]

theorem credentials.NewPerRPCCredentialBundle.wp_proof :
    credentials.NewPerRPCCredentialBundle.spec (GF := GF) (hG := hG) := by
  intro _ P
  wp_start as #Hpi
  have Htb : threadBound GF ≤ 2 ^ 30 := ThreadBoundLe.le (GF := GF) _
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_alloc b as Hb
  iStructNamed Hb
  ipersist rc
  iStructNamed «$v0»
  ihave #Hrpc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes $$ []
  · iPkgInit
  imod sync.init_RWMutex_threadPoolL (credTokR «$v0_ptr» P) credTokN 0 _ Htb $$ [authToken] authTokenMu
    with ⟨%γp, #Hg, #Hpool⟩
  · inext
    iunfold credTokR
    iexists _
    iframe authToken
    ileft; ipureintro; rfl
  wp_auto
  iapply HΦ
  unfold tokenBundleInv credTokInv
  iexists b, «$v0_ptr»
  iframe rc Hsync Hrpc Hg
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; exact Htb
  iexists γp
  iexact Hpool

end proof

end EtcdGrove
end Perennial
