/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/New.lean`. Lean-first (no Rocq
counterpart). The spec-first pilot's phase 1 (`notes/compactor-pilot-plan.md`): the spec is written,
the proof is phase 1's glue.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.New
public import Spec.go_uber_org.zap.NewNop
public import Spec.github_com.jonboulle.clockwork.NewRealClock
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.newPeriodic
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.newRevision
public import Spec.fmt.Errorf
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic__Run
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic__Stop
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic__Pause
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic__Resume
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Revision__Run
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Revision__Stop
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Revision__Pause
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Revision__Resume

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api v3compactor

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Assumptions]

theorem v3compactor.New.wp_proof
    (hNewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (hNewRealClock : clockwork.NewRealClock.spec (GF := GF) (hG := hG))
    (hnewPeriodic : v3compactor.newPeriodic.spec (GF := GF) (hG := hG))
    (hnewRevision : v3compactor.newRevision.spec (GF := GF) (hG := hG))
    (hErrorf : fmt.Errorf.spec (GF := GF) (hG := hG))
    (hPeriodic_Run : v3compactor.Periodic.Run.spec (GF := GF) (hG := hG))
    (hPeriodic_Stop : v3compactor.Periodic.Stop.spec (GF := GF) (hG := hG))
    (hPeriodic_Pause : v3compactor.Periodic.Pause.spec (GF := GF) (hG := hG))
    (hPeriodic_Resume : v3compactor.Periodic.Resume.spec (GF := GF) (hG := hG))
    (hRevision_Run : v3compactor.Revision.Run.spec (GF := GF) (hG := hG))
    (hRevision_Stop : v3compactor.Revision.Stop.spec (GF := GF) (hG := hG))
    (hRevision_Pause : v3compactor.Revision.Pause.spec (GF := GF) (hG := hG))
    (hRevision_Resume : v3compactor.Revision.Resume.spec (GF := GF) (hG := hG)) :
    v3compactor.New.spec (GF := GF) (hG := hG) := by
  intro lg mode ret E Hper
  wp_start as -
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Pclk : isPkgInit (PROP := IProp GF) pkg_id.github_com.jonboulle.clockwork $$ []
  · iPkgInit
  ihave #Pfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_auto
  -- `if lg == nil { lg = zap.NewNop() }`
  wp_join iprop(∃ l : Loc, "lg" ∷ lg_ptr ↦ l ∗ ⌜l ≠ null⌝) at next with [lg] as ⟨%l, lg, %Hl⟩
  · wp_if_destruct
    · wp_apply hNewNop as %l %Hl
      (try wp_auto)
      wp_join_done
      iexists l; iframe; ipureintro; exact Hl
    · wp_join_done
      iexists lg; iframe; ipureintro; exact Hif
  (try wp_auto)
  wp_if_destruct
  · -- `periodic`
    wp_apply hNewRealClock as %clk #Hclk
    (try wp_auto)
    wp_apply (hnewPeriodic l clk ret E (Hper rfl)) $$ [] as %pc ⟨#Hpc, %γf, Htok⟩
    · iframe #; ipureintro; exact Hl
    (try wp_auto)
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists (periodicRunTok pc γf), γf
    iframe Htok
    unfold compactorOk
    iexists _
    isplitr
    · ipureintro; rfl
    isplitr
    · iintro !> %Φ' !> ⟨Htok, Hpre⟩ HΦ'
      simp only [modePermit, show ¬ (go!"periodic" = go!"revision") by decide, if_false]
      wp_apply (hPeriodic_Run pc E (sint.Z ret) γf) $$ [Htok Hpre]
      · iframe #; iframe
      iapply HΦ'; itrivial
    isplitr
    · iintro !> %Φ' !> - HΦ'
      wp_apply (hPeriodic_Stop pc E (sint.Z ret)) $$ []
      · iframe #
      iapply HΦ'; itrivial
    isplitr
    · iintro !> %Φ' !> - HΦ'
      wp_apply (hPeriodic_Pause pc E (sint.Z ret)) $$ []
      · iframe #
      iapply HΦ'; itrivial
    · iintro !> %Φ' !> - HΦ'
      wp_apply (hPeriodic_Resume pc E (sint.Z ret)) $$ []
      · iframe #
      iapply HΦ'; itrivial
  · wp_if_destruct
    · -- `revision`
      wp_apply hNewRealClock as %clk #Hclk
      (try wp_auto)
      wp_apply (hnewRevision l clk ret E) $$ [] as %rc #Hrc
      · iframe #; ipureintro; exact Hl
      (try wp_auto)
      iapply HΦ
      ileft
      isplitr
      · ipureintro; rfl
      -- (the first sample's name is the periodic mode's: any)
      iexists iprop(True), (default : GName)
      isplitl
      · unfold compactorOk
        iexists _
        isplitr
        · ipureintro; rfl
        isplitr
        · iintro !> %Φ' !> ⟨-, Hpre⟩ HΦ'
          simp only [modePermit, if_true]
          wp_apply (hRevision_Run rc E (sint.Z ret)) $$ [Hpre]
          · iframe #; iframe
          iapply HΦ'; itrivial
        isplitr
        · iintro !> %Φ' !> - HΦ'
          wp_apply (hRevision_Stop rc E (sint.Z ret)) $$ []
          · iframe #
          iapply HΦ'; itrivial
        isplitr
        · iintro !> %Φ' !> - HΦ'
          wp_apply (hRevision_Pause rc E (sint.Z ret)) $$ []
          · iframe #
          iapply HΦ'; itrivial
        · iintro !> %Φ' !> - HΦ'
          wp_apply (hRevision_Resume rc E (sint.Z ret)) $$ []
          · iframe #
          iapply HΦ'; itrivial
      · itrivial
    · -- another mode: an error
      wp_apply wp_slice_literal (V := GoInterface)
      isplitr
      · ipureintro; rfl
      iintro %asl ⟨Hasl, -⟩
      wp_apply hErrorf _ _ _ _ $$ [Hasl] as %e -
      · iframe #; iframe Hasl
        simp only [fmt.argsOk, fmt.argOk]
        isplitr
        · ileft; ipureintro
          apply fmt.argWf_of_argsWf
          exact .cons_string _ _ .nil
        itrivial
      (try wp_auto)
      iapply HΦ
      iright
      ipureintro
      refine ⟨(by simp), ?_, ?_⟩ <;> assumption

end proof

end EtcdGrove
end Perennial
