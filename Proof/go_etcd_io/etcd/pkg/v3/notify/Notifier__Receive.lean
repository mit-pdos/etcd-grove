/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/notify/Notifier__Receive.lean`. Lean-first (no Rocq
counterpart); the request path's unit 4b.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.notify.Notifier__Receive

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.notify.Assumptions]

theorem notify.Notifier.Receive.wp_proof : notify.Notifier.Receive.spec (GF := GF) (hG := hG) := by
  intro n
  wp_start as Hrd
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold notifyReader at Hrd
  icases Hrd with ⟨%γ, Hrd⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hrl, HP⟩
  iunfold notifyLockInv at HP
  iNamed HP
  wp_auto
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hcur Hch Hpend] as Hrd
  · inext
    iunfold notifyLockInv
    iexists c
    simp only [named]
    iframe
    iexact Hbc
  (try wp_auto)
  iapply HΦ
  isplitl [Hrd]
  · iunfold notifyReader; iexists γ; iexact Hrd
  iunfold notifyChan
  iexists c.γch
  iapply ownBroadcastChan_close _ _ _ .Unknown c.γi
  iframe Hbc

end proof

end EtcdGrove
end Perennial
