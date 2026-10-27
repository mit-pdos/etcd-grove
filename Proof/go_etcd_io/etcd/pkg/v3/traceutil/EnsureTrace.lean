/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/traceutil/EnsureTrace.lean`. Lean-first (no Rocq counterpart); unit P1b (2026-10-14).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.EnsureTrace
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Get
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__IsEmpty
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.newTrace
public import Spec.context.WithValue

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3 go_etcd_io.etcd.pkg.v3.traceutil

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.traceutil.Assumptions]

set_option hygiene false in
/-- The new trace (`IsEmpty()` true): `newTrace`, then `context.WithValue(ctx, TraceKey{}, t)`. -/
local macro "et_new" : tactic => `(tactic| (
  (try wp_auto)
  wp_apply hNew op lg fields $$ [Hf] as %t1 ⟨%Ht1n, Ht1⟩
  · iframe #; iframe Hf
  (try wp_auto)
  wp_apply hWV ctx ⟨go_etcd_io.etcd.pkg.v3.traceutil.TraceKey.ty,
      #(zero_val go_etcd_io.etcd.pkg.v3.traceutil.TraceKey)⟩ _ $$ []
    as %c ⟨%Hcnn, -, -, %c', %vs, %Hc, #Htx, #Hic, #Htr, -⟩
  · iframe #; ipureintro; right; right; right; left; rfl
  subst Hc
  (try wp_auto)
  iapply HΦ
  iframe Ht1
  isplitr
  · ipureintro
    refine ⟨Ht1n, ?_⟩
    intro t0 _ hf
    simp_all
  isplitr
  · iapply Htr
    ipureintro; first | exact ⟨rfl, Ht1n, rfl⟩ | exact ⟨Ht1n, rfl⟩ | simp [Ht1n]
  iexists vs
  isplitr
  · iapply Htx $$ Hctr
  iintro Hi
  iapply Hic $$ Hi))

theorem traceutil.EnsureTrace.wp_proof
    (hGet : traceutil.Get.spec (GF := GF) (hG := hG))
    (hIE : traceutil.Trace.IsEmpty.spec (GF := GF) (hG := hG))
    (hNew : traceutil.newTrace.spec (GF := GF) (hG := hG))
    (hWV : context.WithValue.spec (GF := GF) (hG := hG)) :
    traceutil.EnsureTrace.spec (GF := GF) (hG := hG) := by
  intro ctx cd o e lg op fields
  wp_start as ⟨#Hctr, #Hctx, Ho, Hf⟩
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  wp_auto
  wp_apply hGet ctx o $$ [] as %t0 ⟨%Ht0n, Ht0⟩
  · iframe #
  cases o with
  | some t' =>
    icases Ht0 with %Ht0
    subst Ht0
    simp only [traceutil.ownTraceOpt]
    (try wp_auto)
    wp_apply hIE t0 e $$ [Ho] as Ho
    · iframe #; iframe Ho
    cases e
    · (try wp_auto)
      iapply HΦ
      iframe Ho
      isplitr
      · ipureintro
        refine ⟨Ht0n, ?_⟩
        intro t1 h _
        cases h; rfl
      isplitr
      · iexact Hctx
      iexists cd.Values
      have hcd : ({ cd with Values := cd.Values } : context.ContextDesc (IProp GF)) = cd := by
        cases cd; rfl
      rw [hcd]
      iframe Hctr
      iintro Hi; iexact Hi
    · et_new
  | none =>
    (try wp_auto)
    wp_apply hIE t0 true $$ [Ht0] as Ht0
    · iframe #; iframe Ht0
    et_new

end proof

end EtcdGrove
end Perennial
