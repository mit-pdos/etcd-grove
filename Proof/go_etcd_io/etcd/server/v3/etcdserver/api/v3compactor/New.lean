/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/New.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.New
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.newAutoPeriodic
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.newPeriodic
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.newRevision
public import Spec.github_com.jonboulle.clockwork.NewRealClock
public import Spec.go_uber_org.zap.NewNop
public import Spec.fmt.Errorf

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Assumptions]
variable [package_sem_ctx : context.Assumptions]
variable [package_sem_fmt : _root_.Perennial.fmt.Assumptions]

theorem v3compactor.New.wp_proof
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_NewRealClock : clockwork.NewRealClock.spec (GF := GF) (hG := hG))
    (wp_newPeriodic : v3compactor.newPeriodic.spec (GF := GF) (hG := hG))
    (wp_newRevision : v3compactor.newRevision.spec (GF := GF) (hG := hG))
    (wp_newAutoPeriodic : v3compactor.newAutoPeriodic.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.Errorf.spec (GF := GF) (hG := hG)) :
    v3compactor.New.spec (GF := GF) (hG := hG) := by
  intro lg mode retention rg c sg maxBytes
  wp_start as ⟨Hcci, %Hper⟩
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Hcw : isPkgInit (PROP := IProp GF) pkg_id.github_com.jonboulle.clockwork $$ []
  · iPkgInit
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_auto
  -- the logger: `zap.NewNop()` if `nil`
  wp_if_destruct
  all_goals try (wp_apply wp_NewNop as %l %Hl)
  -- the mode's switch, in both cases (the logger variable `lg` holds a non-nil logger)
  all_goals
    wp_if_destruct
    · -- periodic
      wp_apply wp_NewRealClock as %clk -
      wp_apply wp_newPeriodic as %p -
      · ipureintro; exact Hper rfl
      iapply HΦ
      unfold v3compactor.newResult
      simp only [_root_.true_or, ↓reduceIte]
      ipureintro
      exact ⟨by first | trivial | rfl, fun h => by cases h⟩
    wp_if_destruct
    · -- revision
      wp_apply wp_NewRealClock as %clk -
      wp_apply wp_newRevision as %p -
      iapply HΦ
      unfold v3compactor.newResult
      simp only [_root_.or_true, ↓reduceIte]
      ipureintro
      exact ⟨by first | trivial | rfl, fun h => by cases h⟩
    wp_if_destruct
    · -- auto-periodic
      wp_apply wp_NewRealClock as %clk #Hclk
      wp_apply wp_newAutoPeriodic ⟨_, clk, retention, maxBytes, rg, c, sg⟩ $$ [$Hcci] as %ac #Hac
      iapply HΦ
      unfold v3compactor.newResult
      simp only [show ¬ (go!"auto-periodic" = go!"periodic" ∨ go!"auto-periodic" = go!"revision") by decide, ↓reduceIte]
      isplitr
      · ipureintro; first | trivial | rfl
      iexists ac, _, clk
      iframe #
      ipureintro
      refine ⟨rfl, ?_, ?_⟩ <;> simp_all
    -- any other mode
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_Errorf $$ [$Hfmt $Hsl] as %err ⟨-, -⟩
    · fmt_args_ok
    iapply HΦ
    unfold v3compactor.newResult
    simp only [show ¬ (mode = go!"periodic" ∨ mode = go!"revision") by simp_all, show ¬ mode = go!"auto-periodic" by simp_all, ↓reduceIte]
    ipureintro
    exact ⟨by first | trivial | rfl, fun h => by cases h⟩

end proof

end EtcdGrove
end Perennial
