/-
Proof of `Spec/demux__LatestRev.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.demux__LatestRev

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem demux.LatestRev.wp_proof : demux.LatestRev.spec (GF := GF) (hG := hG) := by
  intro d γd cap C
  wp_start as ⟨#Hd, Hh⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  unfold demuxHandle
  wp_apply sync.RWMutex.wp_RLock $$ [$Hh] as ⟨Hrl, HP⟩
  unfold demuxLockInv demuxLockRest
  icases HP with ⟨Hwtok, HP⟩
  iNamed HP
  wp_auto
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hwtok Hcore Hregs Hviews HminRev HmaxRev HactF HlagF Hact Hlag Hhist]
  · inext; iframe; iframe #; ipureintro; exact ⟨Hinv, Hok, Hstart⟩
  iintro Hh
  wp_auto
  iapply HΦ
  iframe
  ipureintro; exact ⟨c, Hinv, rfl⟩

end proof

end EtcdGrove
end Perennial
