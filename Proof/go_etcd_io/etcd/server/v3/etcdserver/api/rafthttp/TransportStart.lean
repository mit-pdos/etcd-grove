/-
**`Transport.Start`, field by field** (rafthttp stage 6c; its axiom's statement is restated over
this in 6d): the two round trippers, the two empty maps, the two probers and the dial-retry
rate. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.newStreamRoundTripper
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.NewRoundTripper
public import Spec.golang_org.x.time.rate.Every

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

/-- **`t.Start()`** on the fields it reads (`TLSInfo`, `DialTimeout`) and writes, for the network
`H`: an error (the round trippers' fields written), or the two round trippers of `H`, the two maps
empty, the two probers and a dial-retry rate. -/
theorem rafthttp.Transport.Start_core
    (hNSRT : rafthttp.newStreamRoundTripper.spec (GF := GF) (hG := hG))
    (hNRT : rafthttp.NewRoundTripper.spec (GF := GF) (hG := hG))
    (hNewProber : probing.NewProber.spec (GF := GF) (hG := hG))
    (hEvery : rate.Every.spec (GF := GF) (hG := hG))
    (H : http.HttpNet GF) (t : Loc) (tls : go_etcd_io.etcd.client.pkg.v3.transport.TLSInfo)
    (dt : w64) (dq1 dq2 : DFrac) (srt0 prt0 pp0 sp0 : GoInterface) (pm0 rm0 : Loc) (drf0 : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
        t.[rafthttp.Transport, go!"TLSInfo"] ↦{dq1} tls ∗
        t.[rafthttp.Transport, go!"DialTimeout"] ↦{dq2} dt ∗
        t.[rafthttp.Transport, go!"streamRt"] ↦ srt0 ∗
        t.[rafthttp.Transport, go!"pipelineRt"] ↦ prt0 ∗
        t.[rafthttp.Transport, go!"peers"] ↦ pm0 ∗
        t.[rafthttp.Transport, go!"remotes"] ↦ rm0 ∗
        t.[rafthttp.Transport, go!"pipelineProber"] ↦ pp0 ∗
        t.[rafthttp.Transport, go!"streamProber"] ↦ sp0 ∗
        t.[rafthttp.Transport, go!"DialRetryFrequency"] ↦ drf0 }}
      (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"Start")) (Val #()))
    {{ (err : GoInterface), RET #err;
        t.[rafthttp.Transport, go!"TLSInfo"] ↦{dq1} tls ∗
        t.[rafthttp.Transport, go!"DialTimeout"] ↦{dq2} dt ∗
        (⌜err ≠ GoInterface.nil⌝ ∗ (∃ srt prt : GoInterface,
          t.[rafthttp.Transport, go!"streamRt"] ↦ srt ∗
          t.[rafthttp.Transport, go!"pipelineRt"] ↦ prt) ∗
          t.[rafthttp.Transport, go!"peers"] ↦ pm0 ∗
          t.[rafthttp.Transport, go!"remotes"] ↦ rm0 ∗
          t.[rafthttp.Transport, go!"pipelineProber"] ↦ pp0 ∗
          t.[rafthttp.Transport, go!"streamProber"] ↦ sp0 ∗
          t.[rafthttp.Transport, go!"DialRetryFrequency"] ↦ drf0 ∨
         ⌜err = GoInterface.nil⌝ ∗ ∃ (srt prt pp sp : GoInterface) (pm rm : Loc) (drf : w64),
          t.[rafthttp.Transport, go!"streamRt"] ↦ srt ∗ http.roundTripperOk H srt ∗
          t.[rafthttp.Transport, go!"pipelineRt"] ↦ prt ∗ http.roundTripperOk H prt ∗
          t.[rafthttp.Transport, go!"peers"] ↦ pm ∗ pm ↦$ (∅ : GMap w64 GoInterface) ∗
          t.[rafthttp.Transport, go!"remotes"] ↦ rm ∗ rm ↦$ (∅ : GMap w64 Loc) ∗
          t.[rafthttp.Transport, go!"pipelineProber"] ↦ pp ∗ probing.proberOk pp ∗
          t.[rafthttp.Transport, go!"streamProber"] ↦ sp ∗ probing.proberOk sp ∗
          t.[rafthttp.Transport, go!"DialRetryFrequency"] ↦ drf) }} := by
  wp_start as ⟨Htls, Hdt, Hsrt, Hprt, Hpm, Hrm, Hpp, Hsp, Hdrf⟩
  wp_alloc_auto
  wp_auto
  wp_apply hNSRT H tls dt as %srt %err1 Hsrtok
  (try wp_auto)
  icases Hsrtok with (%Hne1 | ⟨%Heq1, #Hsrtok⟩)
  · cases err1 with
    | nil => exact absurd rfl Hne1
    | ok ei =>
      wp_auto
      iapply HΦ
      iframe
      ileft
      iframe
      ipureintro; simp
  subst Heq1
  wp_auto
  wp_apply hNRT H tls dt as %prt %err2 Hprtok
  (try wp_auto)
  icases Hprtok with (%Hne2 | ⟨%Heq2, #Hprtok⟩)
  · cases err2 with
    | nil => exact absurd rfl Hne2
    | ok ei =>
      wp_auto
      iapply HΦ
      iframe
      ileft
      iframe
      ipureintro; simp
  subst Heq2
  (try wp_auto)
  wp_apply (wp_map_make1 (K := w64) (V := Loc) _ _) as %rm Hrmm
  (try wp_auto)
  wp_apply (wp_map_make1 (K := w64) (V := GoInterface) _ _) as %pm Hpmm
  (try wp_auto)
  wp_apply hNewProber prt as %pp #Hppok
  (try wp_auto)
  wp_apply hNewProber srt as %sp #Hspok
  (try wp_auto)
  -- `DialRetryFrequency == 0` on a float64: the uninterpreted `float64Eq` (Perennial `08d191151`)
  cases float64Eq drf0 (W64 0)
  rotate_left
  all_goals (try wp_auto)
  · wp_apply hEvery as %drf _
    (try wp_auto)
    iapply HΦ
    iframe
    iright
    iframe
    iframe #
    ipureintro; rfl
  · iapply HΦ
    iframe
    iright
    iframe
    iframe #
    ipureintro; rfl

end proof

end EtcdGrove
end Perennial
