/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/lessor__GetLease.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__GetLease
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.lessor.GetLease.wp_proof : lease.lessor.GetLease.spec (GF := GF) (hG := hG) := by
  intro lp γl item
  wp_start as ⟨#Hinv, Hrd⟩
  iunfold lessorInv at Hinv
  icases Hinv with ⟨%Hlp, #Hpin, #Hmu⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold lessorRd at Hrd
  wp_auto
  wp_apply sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hlk, HR⟩
  iunfold lessorMu at HR
  icases HR with ⟨%lm, %im, %M, %I, %rd0, %L, Hlm, HM, Him, HI, Hrdf, Ha, Hg, %HL, #Hls, Hx⟩
  wp_auto
  wp_apply (wp_map_lookup1 LeaseItem.ty LeaseID.ty im I item) $$ HI as HI
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hlk Hlm HM Him HI Hrdf Ha Hg Hx] as Hrd
  · inext
    iunfold lessorMu
    iexists lm, im, M, I, rd0, L
    iframe
    iframe Hls
    ipureintro; exact HL
  iapply HΦ
  iunfold lessorRd
  iexact Hrd

end proof

end EtcdGrove
end Perennial
