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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.lessor.SetRangeDeleter.wp_proof : lease.lessor.SetRangeDeleter.spec (GF := GF) (hG := hG) := by
  intro lp γl rd0 rd
  wp_start as ⟨#Hinv, Hown⟩
  iunfold lessorInv at Hinv
  icases Hinv with ⟨%Hlp, #Hpin, #Hmu⟩
  iunfold rdOwn at Hown
  icases Hown with ⟨%lp', #Hpin', Hro⟩
  ihave %Heq := lessorPin_agree γl lp lp' $$ [$Hpin $Hpin']
  subst Heq
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hmu] as ⟨Hlk, HR⟩
  iunfold lessorMu at HR
  icases HR with ⟨%lm, %im, %M, %I, %rd1, %L, Hlm, HM, Him, HI, Hrd, Ha, Hg, %HL, #Hls, Hx⟩
  ihave ⟨%Hrd1, Hrd⟩ := typedPointsto_half_combine (lF go!"rd" lp) rd1 rd0 1 $$ [$Hrd $Hro]
  wp_auto
  icases (typedPointsto_half_split (lF go!"rd" lp) rd 1).1 $$ Hrd with ⟨Hrd, Hro⟩
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hlm HM Him HI Hrd Ha Hg Hx]
  · inext
    iunfold lessorMu
    iexists lm, im, M, I, rd, L
    iframe
    iframe Hls
    ipureintro; exact HL
  iapply HΦ
  iunfold rdOwn
  iexists lp
  iframe Hpin Hro

end proof

end EtcdGrove
end Perennial
