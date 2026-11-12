/-
Proof of `Spec/.../mvcc/keyIndex__restore.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__restore
public import Spec.go_uber_org.zap.Int
public import Spec.go_uber_org.zap.Logger__Panic

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.keyIndex.restore.wp_proof
    (hZI : zap.Int'.spec (GF := GF) (hG := hG))
    (hPanic : zap.Logger.Panic.spec (GF := GF) (hG := hG)) :
    mvcc.keyIndex.restore.spec (GF := GF) (hG := hG) := by
  intro p gs ki lg created modified ver
  wp_start as ⟨%Hlg, Hki⟩
  ihave Hinit : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, -, -, ⟨%gg, #Hgauge, #Hgspec, -⟩, -⟩
  iunfold gaugeSpec at Hgspec
  icases Hgspec with ⟨#HInc, -, -⟩
  iunfold mvcc.ownKi at Hki
  icases Hki with ⟨Hmod, Hgs, Hgens⟩
  ihave %Hlen := mvcc.ownGens_len _ _ _ $$ Hgens
  wp_auto
  wp_if_destruct
  · -- no generation: the one generation, appended
    have hnil : ki.gens = [] := by
      apply List.eq_nil_of_length_eq_zero; rw [Hlen.1, Hif]; rfl
    iunfold mvcc.ownGens at Hgens
    icases Hgens with ⟨%gvs, Hgvs, Hcap, Hall⟩
    ihave %Hgl := mvcc.ownGensL_len _ _ _ $$ Hall
    rw [hnil] at Hgl
    have hgvs : gvs = [] := List.eq_nil_of_length_eq_zero Hgl
    subst hgvs
    wp_apply wp_slice_literal (V := Revision) [mvcc.revVal modified]
    try (isplitr; (ipureintro; rfl))
    iintro %rs ⟨Hrs, Hrcap⟩
    (try wp_auto)
    wp_apply wp_slice_literal
    try (isplitr; (ipureintro; rfl))
    iintro %sl ⟨Hsl, -⟩
    (try wp_auto)
    wp_apply wp_slice_append $$ [$Hgvs $Hcap $Hsl] as %gs1 ⟨Hgvs, Hcap, -⟩
    (try wp_auto)
    wp_apply HInc
    (try wp_auto)
    iapply HΦ
    simp only [hnil, ↓reduceIte]
    isplitr
    · ipureintro; trivial
    iexists gs1
    iunfold mvcc.ownKi
    simp only [mvcc.kiRestore]
    iframe Hmod Hgs
    iunfold mvcc.ownGens
    iexists _
    iframe Hgvs Hcap
    simp only [mvcc.ownGensL, List.nil_append]
    isplitl
    · iunfold mvcc.ownGen
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      simp only [List.map_cons, List.map_nil]
      iframe Hrs Hrcap
    · itrivial
  · -- some generations: `lg.Panic(...)` before any write
    have hne : ki.gens ≠ [] := by
      intro h; rw [h] at Hlen; simp only [List.length_nil] at Hlen; apply Hif; word
    wp_apply hZI _ _ as %f1 -
    (try wp_auto)
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    (try wp_auto)
    wp_apply hPanic lg _ _ $$ [] as %r %Hr
    · ipureintro; exact Hlg
    subst Hr
    (try wp_auto)
    iapply HΦ
    simp only [hne, ↓reduceIte]
    isplitr
    · ipureintro; trivial
    iunfold mvcc.ownKi
    iframe Hmod Hgs Hgens

end proof

end EtcdGrove
end Perennial
