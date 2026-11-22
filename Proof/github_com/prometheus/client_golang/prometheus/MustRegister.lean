/-
Proof of `Spec/github_com/prometheus/client_golang/prometheus/MustRegister.lean` (prom-registry,
2026-11-22, notes/prom-registry.md): `MustRegister` runs the trusted glue (`TrustedCode/.../prometheus.lean`),
which registers the collector's descriptors (`collectorDescs`, what its constructor says:
`collectorName`) with the model's registry (`promreg.Registry.Register`, verified). Until then the
trust-boundary axiom `prometheus.MustRegister.wp_proof` (item 8; mustreg, 2026-11-20).
-/
module

public import Spec.github_com.prometheus.client_golang.prometheus.MustRegister
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.promreg.Registry__Register

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode
open _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.lib

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.prometheus.client_golang.prometheus.Assumptions]
variable [promreg_sem : promreg.Assumptions]

theorem prometheus.eraseDups_single (x : w64) : List.eraseDups [x] = [x] := rfl

/-- A collector of one descriptor registers its ID only (`descKeys`: the collector ID, the XOR of one
ID, is that ID). Stated of any descriptor, so the kernel never unfolds a name's ID. -/
theorem prometheus.descKeys_single (d : promreg.Desc) : promreg.descKeys [d] = [d.ID'] := by
  unfold promreg.descKeys
  simp only [List.map_cons, List.map_nil, prometheus.eraseDups_single]
  simp

theorem prometheus.descKeys_single_toks (d : promreg.Desc) (k : w64) (hk : d.ID' = k) :
    promreg.idTok (GF := GF) k ⊢ promreg.idToks (GF := GF) (promreg.descKeys [d]) := by
  subst hk
  rw [prometheus.descKeys_single]
  iintro H
  iapply (promreg.idToks_cons (GF := GF) _ []).2; iframe H
  unfold promreg.idToks; iapply BigSepL.bigSepL_nil.2; iempintro

/-- (Proved by unfolding `nameDesc` only: a bare `rfl` makes the kernel unfold `descId`, the xxhash,
on a variable, to the recursion limit.) -/
theorem prometheus.nameDesc_ID (n : GoString) (dh : w64) :
    (prometheus.nameDesc n dh).ID' = prometheus.descId n := by
  rw [prometheus.nameDesc.eq_def]

/-- The descriptors of a label-free collector named `n` are accepted (`descsOk`). -/
theorem prometheus.nameDesc_ok (n : GoString) (dh : w64) (hn : n ∉ promreg.builtinNames) :
    promreg.descsOk prometheus.descId [prometheus.nameDesc n dh] := by
  refine ⟨?_, ?_, List.cons_ne_nil _ _⟩
  · intro d hd; simp only [List.mem_singleton] at hd; subst hd
    exact ⟨rfl, rfl, hn⟩
  · intro d hd d' hd' _; simp only [List.mem_singleton] at hd hd'; subst hd hd'; rfl

/-- `Registry.Register` of one descriptor takes the right to its ID only. -/
theorem prometheus.wp_Register_single (hReg : promreg.Registry.Register.spec (GF := GF) (hG := hG))
    (f : GoString → w64) (r : Loc) (s : GoSlice) (dq : DFrac) (d : promreg.Desc)
    (hok : promreg.descsOk f [d]) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.promreg ∗
        promreg.isRegistry (GF := GF) f r ∗ s ↦*{dq} [d] ∗ promreg.idTok (GF := GF) d.ID' }}
      (App (Val (r @!! go.GoType.PointerType promreg.Registry.ty @!! go!"Register")) (Val #s))
    {{ RET #(W64 0); s ↦*{dq} [d] }} := by
  iintro %Φ ⟨#Hp, #Hr, Hs, Ht⟩ HΦ
  iapply (hReg f r s dq [d] hok) $$ [Hs Ht] HΦ
  iframe #
  iframe Hs
  rw [prometheus.descKeys_single d]
  unfold promreg.idToks
  iapply BigSepL.bigSepL_cons.2
  iframe Ht
  iapply BigSepL.bigSepL_nil.2; iempintro

theorem prometheus.MustRegister.wp_proof
    (hReg : promreg.Registry.Register.spec (GF := GF) (hG := hG)) :
    prometheus.MustRegister.spec (GF := GF) (hG := hG) := by
  intro s dq c n Hcn
  obtain ⟨dh, Hd⟩ := Hcn
  wp_start as ⟨Hs, Hfree⟩
  ihave #Hp : (github_com.prometheus.client_golang.prometheus.promInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  iunfold github_com.prometheus.client_golang.prometheus.promInit at Hp
  icases Hp with ⟨%l, #Hl, #Hreg⟩
  ihave #Hpr : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.promreg $$ []
  · iPkgInit
  iunfold prometheus.regFree at Hfree
  icases Hfree with ⟨%Hnb, Htok⟩
  have Hok := prometheus.nameDesc_ok n dh Hnb
  have HdID := prometheus.nameDesc_ID n dh
  -- (the descriptor kept a variable: the kernel would otherwise unfold `descKeys` of it, and `descId`)
  generalize prometheus.nameDesc n dh = d at Hd Hok HdID
  generalize prometheus.descId n = k at HdID ⊢
  simp only [prometheus.model_Collector_eq, prometheus.model_Register_eq]
  ihave %Hsl := ownSlice_len $$ Hs
  rw [← HdID]
  wp_auto
  ihave IH : iprop(∃ (j : w64), "i" ∷ i_ptr ↦ j ∗ "c" ∷ (∃ v : GoInterface, c_ptr ↦ v) ∗
      "Hs" ∷ s ↦*{dq} [GoInterface.ok c] ∗
      "Ht" ∷ ((⌜j = W64 0⌝ ∗ promreg.idTok (GF := GF) d.ID') ∨
        ⌜j = W64 1⌝)) $$ [i c Hs Htok]
  · iexists W64 0; iframe
    isplitl [c]
    · iexists _; iexact c
    ileft; iframe; ipureintro; rfl
  wp_for IH
  wp_if_destruct
  · icases Ht with (⟨%Hj, Htok⟩ | %Hj)
    · subst Hj
      have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z s.len := ⟨by word, Hif⟩
      rw [ite_eq_left hb]
      wp_apply wp_load_slice_index s (sint.Z (W64 0)) [GoInterface.ok c] dq (GoInterface.ok c) hb.1 $$ [Hs] as Hs
      · iframe; ipureintro; rfl
      icases c with ⟨%v0, c⟩
      wp_auto
      wp_func_call
      wp_call
      simp only [prometheus.model_Collector_eq, prometheus.model_defaultRegistry_eq]
      try wp_auto
      wp_apply (Hd GF) as %sd Hsd
      try wp_auto
      wp_apply (prometheus.wp_Register_single hReg prometheus.descId l sd (DFrac.own 1) d Hok) $$ [Hsd Htok] as -
      · iframe #; iframe
      try wp_auto
      wp_for_post
      iframe
      iexists W64 1
      iframe
      isplitl [c]
      · iexists _; iexact c
      iright; ipureintro; rfl
    · subst Hj
      exfalso; have := Hsl.1; simp at this; word
  · (try wp_auto)
    iapply HΦ; iexact Hs

end proof

end EtcdGrove
end Perennial
