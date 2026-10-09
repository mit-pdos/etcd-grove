/-
Proof of `Spec/consistentIndex__SetBackend.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex__SetBackend
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex__SetConsistentIndex

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.cindex
  go_etcd_io.etcd.server.v3.storage

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.cindex.Assumptions]

theorem consistentIndex.SetBackend.wp_proof
    (hS : consistentIndex.SetConsistentIndex.spec (GF := GF) (hG := hG)) :
    consistentIndex.SetBackend.spec (GF := GF) (hG := hG) := by
  intro ci γ b0 be
  wp_start as ⟨#Hci, Hown⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  unfold isCI
  icases Hci with ⟨#Hinv, #Hmu⟩
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HL⟩
  iunfold ciLockInv at HL
  iunfold ciOwner at Hown
  icases HL with ⟨%b1, Hb1⟩
  icombine Hown Hb1 gives %Heq
  subst Heq
  ihave Hb := (ciBe_halves ci b0).1 $$ [Hown Hb1]
  · iframe
  wp_auto
  ihave ⟨Hb, Hb'⟩ := (ciBe_halves ci be).2 $$ Hb
  wp_apply_core (hS ci γ (W64 0) (W64 0)) $$ [] [HΦ Hb Hb' Hlocked defer]
  · iframe Hpkg; unfold isCI; iframe Hinv Hmu
  imod HΦ with ⟨%k, Hk, HΦ⟩
  imodintro
  iexists k
  iframe Hk
  iintro Hk
  imod HΦ $$ Hk with HΦ
  imodintro
  wp_auto
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hb']
  · inext; iunfold ciLockInv; iexists be; iexact Hb'
  iapply HΦ
  iunfold ciOwner
  iexact Hb

end proof

end EtcdGrove
end Perennial
