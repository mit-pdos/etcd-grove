/-
Lean-first (no Rocq counterpart). #33 S3b W4a (2026-11-23): the proof of `x.conf1()` (B 291-359, `OnDisk.conf1`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__conf1
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__stores
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__T1
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__last
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__acks
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__below
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Max
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.OnDiskLaws

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

theorem onDisk.conf1.wp_proof
    (wp_stores : onDisk.stores.spec (GF := GF) (hG := hG))
    (wp_T1 : onDisk.T1.spec (GF := GF) (hG := hG))
    (wp_last : onDisk.last.spec (GF := GF) (hG := hG))
    (wp_acks : onDisk.acks.spec (GF := GF) (hG := hG))
    (wp_below : onDisk.below.spec (GF := GF) (hG := hG))
    (wp_Max : Max.spec (GF := GF) (hG := hG)) :
    onDisk.conf1.spec (GF := GF) (hG := hG) := by
  intro gx x v
  wp_start as ⟨#Hx, %Hv⟩
  ihave #Hx' := Hx
  iunfold onDiskRO at Hx'
  icases Hx' with ⟨#Hs, #Hq, #Hro, #Hld, #Hll, #Hch, #Htl, #Hvi, %Hp⟩
  obtain ⟨Hn, Hlt, -, -, HB⟩ := Hp
  obtain ⟨b, E, hb, HW⟩ := HB.get
  have hb' := hb; unfold numBound at hb'
  have Hn0 : 0 ≤ sint.Z gx.n' := by omega
  have hnn : sint.nat gx.n' = x.n := by have := sint_nat_cast Hn0; omega
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp
  icases confirmedsRO_at g.Confirmed' x.s.confirmed gx.n' ⟨Hn0, by rw [HWf.len_confirmed]; omega⟩ $$ HConfirmed with ⟨%cv, #Hcv, %Hcr⟩
  rw [hnn] at Hcr
  unfold OnDisk.conf1 at Hv
  obtain ⟨st, hst, Hv⟩ := bind_ok Hv
  wp_auto
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'stores.method_unfold]
  try wp_auto
  wp_apply wp_stores gx x st $$ [Hx]
  · iframe Hx; ipureintro; exact hst
  try wp_auto
  cases st
  · simp only [Bool.false_eq_true, ite_false] at Hv
    obtain ⟨ab, hab, Hv⟩ := bind_ok Hv
    obtain ⟨ak, hak, ht, hf⟩ := andM_ok hab
    try wp_auto
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'acks.method_unfold]
    try wp_auto
    wp_apply wp_acks gx x ak $$ [Hx]
    · iframe Hx; ipureintro; exact hak
    try wp_auto
    -- `!x.below()` evaluated only after `acks`
    have hres : ab = false → v = x.s.confirmed[x.n]! := by
      intro h; subst h; simp only [Bool.false_eq_true, ite_false, pure_ok, Except.ok.injEq] at Hv; exact Hv.symm
    cases ak
    · rw [hf rfl] at hres
      try wp_auto
      wp_apply wp_load_at _ _ cv Hn0 $$ [Hcv]
      · iexact Hcv
      try wp_auto
      rw [hres rfl]; iapply HΦ; ipureintro; exact Hcr
    · have hnb := ht rfl
      unfold notM at hnb
      obtain ⟨bl, hbl, hnb⟩ := bind_ok hnb
      simp only [pure_ok, Except.ok.injEq] at hnb
      subst hnb
      try wp_auto
      try wp_auto
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'below.method_unfold]
      try wp_auto
      wp_apply wp_below gx x bl $$ [Hx]
      · iframe Hx; ipureintro; exact hbl
      try wp_auto
      cases bl
      · simp only [Bool.not_false, ite_true] at Hv
        obtain ⟨t1, ht1, Hv⟩ := bind_ok Hv
        try wp_auto
        wp_apply wp_load_at _ _ cv Hn0 $$ [Hcv]
        · iexact Hcv
        try wp_auto
        try wp_auto
        rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'T1.method_unfold]
        try wp_auto
        wp_apply wp_T1 gx x t1 $$ [Hx] as %ut %Hut
        · iframe Hx; ipureintro; exact ht1
        try wp_auto
        rw [decide_w64_eq, Hcr.1, Hut]
        by_cases hct : x.s.confirmed[x.n]!.term = t1
        · rw [decide_eq_true hct]
          simp only [hct, beq_self_eq_true, ite_true] at Hv
          obtain ⟨t1', ht1', Hv⟩ := bind_ok Hv
          rw [ht1] at ht1'; cases ht1'
          obtain ⟨la, hla, Hv⟩ := bind_ok Hv
          simp only [pure_ok, Except.ok.injEq] at Hv
          subst Hv
          try wp_auto
          try wp_auto
          rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'T1.method_unfold]
          try wp_auto
          wp_apply wp_T1 gx x t1 $$ [Hx] as %ut2 %Hut2
          · iframe Hx; ipureintro; exact ht1
          try wp_auto
          try wp_auto
          rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'last.method_unfold]
          try wp_auto
          wp_apply wp_last gx x la $$ [Hx] as %ul %Hul
          · iframe Hx; ipureintro; exact hla
          try wp_auto
          wp_apply wp_Max cv.Index' ul as %w %Hw
          try wp_auto
          iapply HΦ; ipureintro
          exact ⟨Hut2, by rw [Hw, Hcr.2, Hul]⟩
        · rw [decide_eq_false hct]
          have hct' : (x.s.confirmed[x.n]!.term == t1) = false := by simpa using hct
          simp only [hct', Bool.false_eq_true, ite_false] at Hv
          obtain ⟨t1', ht1', Hv⟩ := bind_ok Hv
          rw [ht1] at ht1'; cases ht1'
          obtain ⟨la, hla, Hv⟩ := bind_ok Hv
          simp only [pure_ok, Except.ok.injEq] at Hv
          subst Hv
          try wp_auto
          try wp_auto
          rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'T1.method_unfold]
          try wp_auto
          wp_apply wp_T1 gx x t1 $$ [Hx] as %ut2 %Hut2
          · iframe Hx; ipureintro; exact ht1
          try wp_auto
          try wp_auto
          rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'last.method_unfold]
          try wp_auto
          wp_apply wp_last gx x la $$ [Hx] as %ul %Hul
          · iframe Hx; ipureintro; exact hla
          try wp_auto
          iapply HΦ; ipureintro
          exact ⟨Hut2, Hul⟩
      · rw [hres (by rfl)]
        try wp_auto
        wp_apply wp_load_at _ _ cv Hn0 $$ [Hcv]
        · iexact Hcv
        try wp_auto
        iapply HΦ; ipureintro; exact Hcr
  · simp only [ite_true] at Hv
    obtain ⟨t1, ht1, Hv⟩ := bind_ok Hv
    obtain ⟨la, hla, Hv⟩ := bind_ok Hv
    simp only [pure_ok, Except.ok.injEq] at Hv
    subst Hv
    try wp_auto
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'T1.method_unfold]
    try wp_auto
    wp_apply wp_T1 gx x t1 $$ [Hx] as %ut %Hut
    · iframe Hx; ipureintro; exact ht1
    try wp_auto
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'last.method_unfold]
    try wp_auto
    wp_apply wp_last gx x la $$ [Hx] as %ul %Hul
    · iframe Hx; ipureintro; exact hla
    try wp_auto
    iapply HΦ; ipureintro
    exact ⟨Hut, Hul⟩

end proof

end AntCheck
end EtcdGrove
end Perennial
