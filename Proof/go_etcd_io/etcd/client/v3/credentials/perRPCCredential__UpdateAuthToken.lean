/-
Proof of `Spec/go_etcd_io/etcd/client/v3/credentials/perRPCCredential__UpdateAuthToken.lean` (the auth
plan's C1; a trust-boundary axiom until 2026-11-22, prove-ps2-client). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.credentials.perRPCCredential__UpdateAuthToken
public import Perennial.Proof.sync

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

/-- `UpdateAuthToken(t)` stores `t` in `rc.authToken` under `authTokenMu.Lock()`, taken through
the lock's guard (`credTokInv`), so it holds `credTokR` whole while it writes. -/
theorem credentials.perRPCCredential.UpdateAuthToken.wp_proof :
    credentials.perRPCCredential.UpdateAuthToken.spec (GF := GF) (hG := hG) := by
  intro rc P t
  wp_start as ⟨#Hinv, #Ht⟩
  iunfold credTokInv at Hinv
  icases Hinv with ⟨%Htb, #Hsync, #Hg, %γp, #Hpool⟩
  wp_auto
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hg] as ⟨Hl, HR⟩
  iunfold credTokR at HR
  icases HR with ⟨%t0, Hpt, -⟩
  wp_auto
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hl Hpt]
  · inext
    iunfold credTokR
    iexists t
    iframe Hpt Ht
  iapply HΦ
  ipureintro; trivial

end proof

end EtcdGrove
end Perennial
