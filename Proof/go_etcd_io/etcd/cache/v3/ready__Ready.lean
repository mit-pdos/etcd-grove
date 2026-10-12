/-
Proof of `Spec/ready__Ready.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.ready__Ready

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem ready.Ready.wp_proof : ready.Ready.spec (GF := GF) (hG := hG) := by
  intro r γ e0
  wp_start as ⟨#Hr, #Hlb⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  unfold isReady
  wp_apply sync.Mutex.wp_Lock $$ [$Hr] as ⟨Hlocked, Hinv⟩
  unfold readyLockInv
  iNamed Hinv
  ihave #Hlb' := monoNatLbOwn_get $$ Hauth
  unfold readyEpochLb
  ihave %Hle := monoNatLbOwn_valid $$ Hauth Hlb
  wp_auto
  wp_apply sync.Mutex.wp_Unlock $$ [$Hr $Hlocked HisReady HstateCh Hch Hauth]
  · inext; iexists b, ch, γch, e; simp only [named]; iframe; ipureintro; exact Hb
  iapply HΦ
  unfold readySeen readyEpochLb
  iexists e
  iframe Hlb'
  ipureintro; exact ⟨Hle.2, Hb.symm⟩

end proof

end EtcdGrove
end Perennial
