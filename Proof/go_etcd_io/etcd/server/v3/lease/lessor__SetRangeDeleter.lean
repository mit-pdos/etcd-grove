/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/lessor__SetRangeDeleter.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__SetRangeDeleter
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

theorem lease.lessor.SetRangeDeleter.wp_proof : lease.lessor.SetRangeDeleter.spec (GF := GF) (hG := hG) := by
  intro lp γl rd
  wp_start as #Hinv
  iunfold lessorInv at Hinv
  icases Hinv with ⟨%Hlp, #Hpin, #Hmu⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hmu] as ⟨Hlk, HR⟩
  iunfold lessorMu at HR
  icases HR with ⟨%lm, %im, %M, %I, %rd0, %L, Hlm, HM, Him, HI, Hrd, Ha, Hg, %HL, #Hls, Hx⟩
  wp_auto
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hlm HM Him HI Hrd Ha Hg Hx]
  · inext
    iunfold lessorMu
    iexists lm, im, M, I, rd, L
    iframe
    iframe Hls
    ipureintro; exact HL
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
