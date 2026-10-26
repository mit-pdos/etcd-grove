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
  intro lp γl item L0 I0
  wp_start as ⟨#Hinv, Hrd, Hown⟩
  iunfold lessorInv at Hinv
  icases Hinv with ⟨%Hlp, #Hpin, #Hmu⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold lessorRd at Hrd
  wp_auto
  wp_apply sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hlk, HR⟩
  iunfold lessorMu at HR
  icases HR with ⟨%lm, %im, %M, %I, %rd0, %L, Hlm, HM, Him, HI, Hrdf, Ha, Hg, %HL, #Hls, Hx⟩
  -- the owner's half of the item map agrees with the lock's
  iunfold leaseOwn at Hown
  icases Hown with ⟨Hown, Hcls⟩
  iunfold leaseClosers at Hcls
  icases Hcls with ⟨%lp', %γga, %γcl, %C, %im', #Hp, %HC, Him', HI', %HIL, Hcs⟩
  ihave %Hpl := lessorPin_agree γl lp lp' $$ [$Hpin]
  · iunfold lessorPin; iexists γga, γcl; iexact Hp
  subst Hpl
  icombine Him Him' gives %Him_eq
  subst Him_eq
  ihave %HIeq := ownMap_agree im _ _ I I0 $$ [$HI $HI']
  subst HIeq
  wp_auto
  wp_apply (wp_map_lookup1 LeaseItem.ty LeaseID.ty im I item) $$ HI as HI
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hlk Hlm HM Him HI Hrdf Ha Hg Hx] as Hrd
  · inext
    iunfold lessorMu
    iexists lm, im, M, I, rd0, L
    iframe
    iframe Hls
    ipureintro; exact HL
  rw [show (zero_val w64) = W64 0 from rfl]
  iapply HΦ
  iunfold lessorRd
  iframe Hrd
  iunfold leaseOwn
  iframe Hown
  iunfold leaseClosers
  iexists lp, γga, γcl, C, im
  iframe Hp Him' HI' Hcs
  ipureintro; exact ⟨HC, HIL⟩

end proof

end EtcdGrove
end Perennial
