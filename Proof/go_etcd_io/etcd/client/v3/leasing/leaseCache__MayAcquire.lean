/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leaseCache__MayAcquire.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__MayAcquire

@[expose] public section

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

theorem leaseCache.MayAcquire.wp_proof : leaseCache.MayAcquire.spec (GF := GF) (hG := hG) := by
  intro lc γ pfx X Qr key
  wp_start as ⟨#Hlc, Hrd, #Hpeek⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  unfold leaseCacheReader
  wp_auto
  wp_apply sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hrl, HP⟩
  icases leaseCacheInv_open $$ HP with ⟨%st, Hown, HX, Hinst, #Hfacts, %Hwf, Hclose⟩
  unfold lcPeek
  icases Hpeek $$ %st %_ HX with ⟨HX, #HQr⟩
  unfold lcOwn
  icases Hown with ⟨Hentries, Hemap, Hrv, Hrmap, Hhdr, #HhdrOk, Hents, #Hfrozen⟩
  wp_auto
  wp_apply wp_map_lookup2 $$ [$Hrmap] as Hrmap
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hclose Hentries Hemap Hrv Hrmap Hhdr Hents HX Hinst]
    as Hrd
  · inext
    iapply Hclose $$ [Hentries Hemap Hrv Hrmap Hhdr Hents] HX Hinst
    iframe
    iframe #
  cases hk : st.revokes !! key with
  | none =>
    simp only [Option.isSome_none, decide_false, Bool.false_eq_true]
    wp_auto
    iapply HΦ
    iframe
    iexists st
    iframe #
    ipureintro; intro _; rfl
  | some t =>
    simp only [Option.isSome_some]
    wp_auto
    wp_apply time.wp_Since as %d -
    iapply HΦ
    iframe
    iexists st
    iframe #
    ipureintro; intro h; rw [hk] at h; cases h

end proof

end leasing
end EtcdGrove
end Perennial
