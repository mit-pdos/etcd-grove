/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Trace__loglineIsEvent`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__loglineIsEvent
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__logline

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

theorem Trace.loglineIsEvent.wp_proof (wp_logline : Trace.logline.spec (GF := GF) (hG := hG)) :
    Trace.loglineIsEvent.spec (GF := GF) (hG := hG) := by
  intro t tr g ts e es
  wp_start as ⟨#Ht, #Hts, %He, %Hl1⟩
  ihave #Ht0 := Ht
  iunfold traceRO at Ht0
  icases Ht0 with ⟨%Hv, %gt, #Hp, ⟨%lns, #Hlns, #Hl⟩, -⟩
  ihave #Hts0 := Hts
  iunfold tstateRO at Hts0
  icases Hts0 with ⟨-, %Hg⟩
  ihave %Hlen := ownSlice_len $$ Hlns
  ihave %Hll := BigSepL2.bigSepL2_length $$ Hl
  have hlenZ : (tr.len : Int) = sint.Z gt.lines'.len := by unfold Trace.len; rw [← Hll, Hlen.1]; word
  icases typedPointsto_split _ _ _ $$ Hp with Hpf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hpf
  wp_auto
  by_cases hle : ts.l ≤ tr.len
  · rw [decide_eq_true (show sint.Z g.L' ≤ sint.Z gt.lines'.len by rw [Hg.1, ← hlenZ]; exact_mod_cast hle)]
    wp_auto
    wp_apply wp_logline t tr g ts $$ [Ht Hts] as %q ⟨%ln, #Hq, #Hln⟩
    · iframe Ht Hts; ipureintro; exact ⟨Hl1, hle⟩
    iunfold lineRO at Hln
    icases Hln with ⟨⟨%ge, #Hev, #Hevr⟩, -⟩
    iunfold eventRO at Hevr
    icases Hevr with ⟨%Hef, -⟩
    icases typedPointsto_split _ _ _ $$ Hq with Hqf
    simp only [TypedPointsto.typedPointstoDef]
    iNamed Hqf
    icases typedPointsto_split _ _ _ $$ Hev with Hevf
    simp only [TypedPointsto.typedPointstoDef]
    iNamed Hevf
    wp_auto
    rw [decide_strRel Hef.1 He]
    have : tr.isEvent ts es = decide ((tr.line ts.l).ev.name = es) := by
      unfold Trace.isEvent; simp [hle]; rfl
    rw [this]
    iapply HΦ; ipureintro; trivial
  · rw [decide_eq_false (show ¬ sint.Z g.L' ≤ sint.Z gt.lines'.len by rw [Hg.1, ← hlenZ]; exact_mod_cast hle)]
    wp_auto
    have : tr.isEvent ts es = false := by unfold Trace.isEvent; simp [hle]
    rw [this]
    iapply HΦ; ipureintro; trivial

end proof

end Etcdraft
end EtcdGrove
end Perennial
