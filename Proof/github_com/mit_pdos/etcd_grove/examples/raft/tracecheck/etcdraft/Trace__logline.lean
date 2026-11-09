/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Trace__logline`.
-/
module

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

theorem Trace.logline.wp_proof : Trace.logline.spec (GF := GF) (hG := hG) := by
  intro t tr g ts
  wp_start as ⟨#Ht, #Hts, %Hl1, %Hl2⟩
  iunfold traceRO at Ht
  icases Ht with ⟨%Hv, %gt, #Hp, ⟨%lns, #Hlns, #Hl⟩, -⟩
  iunfold tstateRO at Hts
  icases Hts with ⟨-, %Hg⟩
  ihave %Hlen := ownSlice_len $$ Hlns
  ihave %Hll := BigSepL2.bigSepL2_length $$ Hl
  icases typedPointsto_split _ _ _ $$ Hp with Hpf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hpf
  wp_auto
  have hlenZ : (tr.lines.length : Int) = sint.Z gt.lines'.len := by rw [← Hll, Hlen.1]; word
  have hi : sint.Z (g.L' - W64 1) = (ts.l : Int) - 1 := by
    have : (ts.l : Int) ≤ (tr.lines.length : Int) := by unfold Trace.len at Hl2; omega
    rw [hlenZ] at this
    word
  have hb : 0 ≤ sint.Z (g.L' - W64 1) ∧ sint.Z (g.L' - W64 1) < sint.Z gt.lines'.len := by
    unfold Trace.len at Hl2; rw [hi]; constructor <;> omega
  rw [ite_eq_left_of_eq_true _ _ (eq_true hb)]
  have hx := Trace.line_eq tr ts.l Hl1 Hl2
  have hn : (sint.Z (g.L' - W64 1)).toNat < lns.length := by
    unfold Trace.len at Hl2; rw [hi]; omega
  obtain ⟨x, Hx⟩ : ∃ x, lns[(sint.Z (g.L' - W64 1)).toNat]? = some x := ⟨_, List.getElem?_eq_getElem hn⟩
  have hk : (sint.Z (g.L' - W64 1)).toNat = ts.l - 1 := by rw [hi]; omega
  rw [hk] at Hx
  ihave #Hxy := BigSepL2.bigSepL2_lookup (Φ := fun _ a b => lineRO (GF := GF) a b) Hx hx $$ Hl
  rw [← hk] at Hx
  icases ownSlice_elem_acc _ x _ _ lns hb.1 Hx $$ Hlns with ⟨#Hxe, -⟩
  wp_auto
  iapply HΦ
  iexists x
  isplitr
  · iexact Hxe
  · iexact Hxy

end proof

end Etcdraft
end EtcdGrove
end Perennial
