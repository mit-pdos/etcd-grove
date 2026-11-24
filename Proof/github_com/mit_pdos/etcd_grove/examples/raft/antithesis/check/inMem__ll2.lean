/-
Lean-first (no Rocq counterpart). #33 S3b W3 (2026-11-23): the proof of `x.ll2()` (B 214-230, `InMem.ll2`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__ll2
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__app
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__ll1
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__T
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__es
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermLogs__Has
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermLogs__Get
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermLogs__With
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Concat
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.InMemLaws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
set_option linter.unusedSimpArgs false
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem inMem.ll2.wp_proof
    (wp_app : inMem.app.spec (GF := GF) (hG := hG))
    (wp_ll1 : inMem.ll1.spec (GF := GF) (hG := hG))
    (wp_T : inMem.T.spec (GF := GF) (hG := hG))
    (wp_es : inMem.es.spec (GF := GF) (hG := hG))
    (wp_Has : TermLogs.Has.spec (GF := GF) (hG := hG))
    (wp_Get : TermLogs.Get.spec (GF := GF) (hG := hG))
    (wp_With : TermLogs.With.spec (GF := GF) (hG := hG))
    (wp_Concat : Concat.spec (GF := GF) (hG := hG)) :
    inMem.ll2.spec (GF := GF) (hG := hG) := by
  intro gx x v
  wp_start as ⟨#Hx, %Hv⟩
  ihave #Hx' := Hx
  iunfold inMemRO at Hx'
  icases Hx' with ⟨#Hs, #He, %Hp⟩
  obtain ⟨-, -, bb, EE, HW, HN, HC, hbb, -⟩ := Hp
  unfold numBound Event.weight at hbb
  wp_auto
  unfold InMem.ll2 at Hv
  obtain ⟨c, hc, Hv⟩ := bind_ok Hv
  obtain ⟨a, ha, hat, haf⟩ := andM_ok hc
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_app_unfold.method_unfold]
  try wp_auto
  wp_apply wp_app gx x a $$ [Hx]
  · iframe Hx; ipureintro; exact ha
  try wp_auto
  cases a
  · rw [haf rfl] at Hv
    simp only [Bool.false_eq_true, ite_false] at Hv
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_ll1_unfold.method_unfold]
    try wp_auto
    wp_apply wp_ll1 gx x v $$ [Hx] as %u #Hu
    · iframe Hx; ipureintro; exact Hv
    try wp_auto
    iapply HΦ; iexact Hu
  obtain ⟨l1, hl1, hc'⟩ := bind_ok (hat rfl)
  obtain ⟨t, ht, hc'⟩ := bind_ok hc'
  simp only [pure_ok, Except.ok.injEq] at hc'
  subst hc'
  have hl1w := InMem.ll1_within HW HN hl1
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_T_unfold.method_unfold]
  try wp_auto
  wp_apply wp_T gx x t $$ [Hx] as %ut %Hut
  · iframe Hx; ipureintro; exact ht
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_ll1_unfold.method_unfold]
  try wp_auto
  wp_apply wp_ll1 gx x l1 $$ [Hx] as %u1 #Hu1
  · iframe Hx; ipureintro; exact hl1
  try wp_auto
  wp_apply wp_Has u1 l1 ut $$ [Hu1]
  · iexact Hu1
  rw [Hut]
  cases hh : l1.has t
  · simp only [hh, Bool.false_eq_true, ite_false] at Hv
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_ll1_unfold.method_unfold]
    try wp_auto
    wp_apply wp_ll1 gx x v $$ [Hx] as %u #Hu
    · iframe Hx; ipureintro; exact Hv
    try wp_auto
    iapply HΦ; iexact Hu
  simp only [hh, ite_true, hl1, ht, ok_bind] at Hv
  obtain ⟨g, hg, Hv⟩ := bind_ok Hv
  obtain ⟨es, hes, Hv⟩ := bind_ok Hv
  simp only [pure_ok, Except.ok.injEq] at Hv
  subst Hv
  have hgw := InMem.ll1_get_within HW HN hl1 hg
  have hesw := InMem.es_within HN HC hes
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_ll1_unfold.method_unfold]
  try wp_auto
  wp_apply wp_ll1 gx x l1 $$ [Hx] as %u2 #Hu2
  · iframe Hx; ipureintro; exact hl1
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_T_unfold.method_unfold]
  try wp_auto
  wp_apply wp_T gx x t $$ [Hx] as %ut2 %Hut2
  · iframe Hx; ipureintro; exact ht
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_T_unfold.method_unfold]
  try wp_auto
  wp_apply wp_T gx x t $$ [Hx] as %ut3 %Hut3
  · iframe Hx; ipureintro; exact ht
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermLogs.TypeAssumptions.ptr_Get_unfold.method_unfold]
  try wp_auto
  wp_apply wp_Get u2 l1 ut3 g $$ [Hu2] as %ug #Hug
  · iframe Hu2; ipureintro; rw [Hut3]; exact hg
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_es_unfold.method_unfold]
  try wp_auto
  wp_apply wp_es gx x es $$ [Hx] as %ue #Hue
  · iframe Hx; ipureintro; exact hes
  try wp_auto
  wp_apply wp_Concat ug g ue es $$ [Hug Hue] as %uc #Huc
  · iframe Hug; iframe Hue; ipureintro; have := hgw.1; have := hesw.1; omega
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermLogs.TypeAssumptions.ptr_With_unfold.method_unfold]
  try wp_auto
  wp_apply wp_With u2 l1 ut2 uc (g ++ es) $$ [Hu2 Huc] as %u #Hu
  · iframe Hu2; iframe Huc; ipureintro; have := hl1w.1; omega
  try wp_auto
  rw [Hut2]
  iapply HΦ; iexact Hu

end proof

end AntCheck
end EtcdGrove
end Perennial
