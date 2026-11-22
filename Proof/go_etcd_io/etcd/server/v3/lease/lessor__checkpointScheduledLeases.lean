/- Proof of `Spec/go_etcd_io/etcd/server/v3/lease/lessor__checkpointScheduledLeases.lean`. Lean-first. -/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__checkpointScheduledLeases
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__findDueScheduledCheckpoints
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__isPrimary

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

theorem lease.lessor.checkpointScheduledLeases.wp_proof
    (hPrim : lease.lessor.isPrimary.spec (GF := GF) (hG := hG))
    (hDue : lease.lessor.findDueScheduledCheckpoints.spec (GF := GF) (hG := hG)) :
    lease.lessor.checkpointScheduledLeases.spec (GF := GF) (hG := hG) := by
  intro lp γl
  wp_start as #Hinv
  iunfold lessorInv at Hinv
  icases Hinv with ⟨%Hlp, #Hpin, #Hmu, #Hrdi⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave Hli : (leaseInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hli with ⟨-, -, -, ⟨-, -, #Hcr, #Hmx, -⟩, -⟩
  wp_auto
  wp_for
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hmu] as ⟨Hlk, HR⟩
  iunfold lessorMu at HR
  icases HR with ⟨%lm, %im, %M, %I', %rd0, %L', Hlm, HM, Him, HI, Hrdf, Ha, Hg, %HL, #Hsz, #Hls, Hx,
    Hhist⟩
  iunfold lessorExtra at Hx
  icases Hx with ⟨%dc, %np, %h, %hx, %bl, Hdc, Hnp, Hns, Hh, Hhq, Hcp, Hmeta, Hbl, Hdt, #Hstr⟩
  (try wp_auto)
  wp_apply (hPrim lp dc _) $$ [$Hpkg $Hdc] as Hdc
  by_cases hdc : dc = chan.nil
  · simp only [hdc, decide_true, Bool.not_true]
    (try wp_auto)
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hlm HM Him HI Hrdf Ha Hg Hdc Hnp Hns Hh Hhq Hcp Hmeta
        Hbl Hdt Hhist]
    · iframe #
      inext
      iunfold lessorMu
      iexists lm, im, M, I', rd0, L'
      iframe
      iframe Hsz Hls
      isplitr
      · ipureintro; exact HL
      iunfold lessorExtra
      iexists _, np, h, hx, bl
      iframe; iframe #
    (try wp_auto)
    wp_for_post
    (try wp_auto)
    iapply HΦ
    itrivial
  · simp only [hdc, decide_false, Bool.not_false]
    (try wp_auto)
    wp_apply (hDue lp _ _) $$ [$Hpkg $Hcp] as Hcp
    (try wp_auto)
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hlm HM Him HI Hrdf Ha Hg Hdc Hnp Hns Hh Hhq Hcp Hmeta
        Hbl Hdt Hhist]
    · iframe #
      inext
      iunfold lessorMu
      iexists lm, im, M, I', rd0, L'
      iframe
      iframe Hsz Hls
      isplitr
      · ipureintro; exact HL
      iunfold lessorExtra
      iexists _, np, h, hx, bl
      iframe; iframe #
    (try wp_auto)
    wp_for_post
    (try wp_auto)
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
