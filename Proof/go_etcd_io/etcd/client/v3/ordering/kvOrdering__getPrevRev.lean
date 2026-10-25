/-
Proof of `Spec/go_etcd_io/etcd/client/v3/ordering/kvOrdering__getPrevRev.lean`.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ordering.kvOrdering__getPrevRev

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ordering

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.ordering

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.ordering.Assumptions]

theorem kvOrdering.getPrevRev.wp_proof : kvOrdering.getPrevRev.spec (GF := GF) (hG := hG) := by
  intro kvp R
  wp_start as Hh
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  unfold kvOrderingHandle
  wp_apply +noauto sync.RWMutex.wp_RLock $$ [$Hh] as ⟨Hrl, HP⟩
  wp_auto_lc 1
  imod lc_fupd_elim_later (E := ⊤) $$ Hlc1 HP with HP
  unfold kvOrderingLockInv
  icases HP with ⟨%prev, Hprev, #HR⟩
  wp_auto
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hprev] as Hh
  · inext
    iexists prev
    iframe; iexact HR
  iapply HΦ
  iframe; iexact HR

end proof

end ordering
end EtcdGrove
end Perennial
