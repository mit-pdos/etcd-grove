/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/Lease__Remaining.lean`. Lean-first (no Rocq
counterpart); the lease-read plan (2026-10-31).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.Lease__Remaining
public import Spec.time.Time__IsZero
public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.Lease.Remaining.wp_proof
    (hIZ : time.Time.IsZero.spec (GF := GF) (hG := hG)) :
    lease.Lease.Remaining.spec (GF := GF) (hG := hG) := by
  intro γl l
  wp_start as ⟨#Hlo, Htt, %Hb⟩
  iunfold isLeaseObj at Hlo
  icases Hlo with ⟨%Hnn, -, -, #HexG, -, #Hpe⟩
  icases Hpe $$ %Hb with ⟨%γe, #Hpe⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  iapply fupd_wp
  imod threadPool.borrow leaseExpPoolN γe (sync.ownRWMutex (lsF go!"expiryMu" l) (leaseExpiry l)) ⊤
    (fun _ _ => CoPset.mem_full) $$ [Hpe Htt] with ⟨Hslot, Hloan⟩
  · iframe #; iframe
  imodintro
  wp_auto
  wp_apply wp_with_defer as %defer defer
  wp_apply (sync.RWMutex.wp_RLock (lsF go!"expiryMu" l) (leaseExpiry l)) $$ [$Hslot] as ⟨Hlk, HR⟩
  iunfold leaseExpiry at HR
  icases HR with ⟨%e, He⟩
  wp_apply hIZ $$ [$He] as %b He
  wp_if_destruct
  · -- the expiry set: the time until it
    wp_apply _root_.Perennial.time.wp_Until as %d -
    iapply wp_fupd
    wp_apply (sync.RWMutex.wp_RUnlock (lsF go!"expiryMu" l) (leaseExpiry l)) $$ [$Hlk He] as Hslot
    · inext; iunfold leaseExpiry; iexists e; iexact He
    imod threadPool.giveBack leaseExpPoolN γe (sync.ownRWMutex (lsF go!"expiryMu" l) (leaseExpiry l))
      ⊤ (fun _ _ => CoPset.mem_full) $$ [Hpe Hloan Hslot] with Htt
    · iframe #; iframe
    imodintro
    (try wp_auto)
    iapply HΦ
    iexact Htt
  · -- the expiry unset: `MaxInt64`
    iapply wp_fupd
    wp_apply (sync.RWMutex.wp_RUnlock (lsF go!"expiryMu" l) (leaseExpiry l)) $$ [$Hlk He] as Hslot
    · inext; iunfold leaseExpiry; iexists e; iexact He
    imod threadPool.giveBack leaseExpPoolN γe (sync.ownRWMutex (lsF go!"expiryMu" l) (leaseExpiry l))
      ⊤ (fun _ _ => CoPset.mem_full) $$ [Hpe Hloan Hslot] with Htt
    · iframe #; iframe
    imodintro
    (try wp_auto)
    iapply HΦ
    iexact Htt

end proof

end EtcdGrove
end Perennial
