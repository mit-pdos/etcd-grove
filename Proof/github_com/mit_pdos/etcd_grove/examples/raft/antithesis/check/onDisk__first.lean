/-
Lean-first (no Rocq counterpart). #33 S3b W4a (2026-11-23): the proof of `x.first()` (B 291-359, `OnDisk.first`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__first
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__w
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__snaps
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__takes
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__fm
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__K
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__L0
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__has
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__first
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

theorem onDisk.first.wp_proof
    (wp_w : onDisk.w.spec (GF := GF) (hG := hG))
    (wp_snaps : onDisk.snaps.spec (GF := GF) (hG := hG))
    (wp_takes : onDisk.takes.spec (GF := GF) (hG := hG))
    (wp_fm : onDisk.fm.spec (GF := GF) (hG := hG))
    (wp_K : onDisk.K.spec (GF := GF) (hG := hG))
    (wp_L0 : onDisk.L0.spec (GF := GF) (hG := hG))
    (wp_has : Event.has.spec (GF := GF) (hG := hG))
    (wp_first : Event.first.spec (GF := GF) (hG := hG)) :
    onDisk.first.spec (GF := GF) (hG := hG) := by
  intro gx x v
  wp_start as ⟨#Hx, %Hv⟩
  ihave #Hx' := Hx
  iunfold onDiskRO at Hx'
  icases Hx' with ⟨#Hs, #Hq, #Hro, #Hld, #Hll, #Hch, #Htl, #Hvi, %Hp⟩
  obtain ⟨-, -, -, -, HB⟩ := Hp
  obtain ⟨b, E, hb, HW⟩ := HB.get
  unfold numBound at hb
  unfold OnDisk.first at Hv
  wp_auto
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'snaps.method_unfold]
  try wp_auto
  wp_apply wp_snaps gx x  $$ [Hx]
  · iexact Hx
  try wp_auto
  obtain ⟨st, hst, Hv⟩ := bind_ok Hv
  obtain ⟨sn, hsn, hst1, hst2⟩ := orM_ok hst
  simp only [pure_ok, Except.ok.injEq] at hsn
  cases hsnap : x.snaps
  · rw [hsnap] at hsn; subst hsn
    have htk := hst2 rfl
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'takes.method_unfold]
    try wp_auto
    wp_apply wp_takes gx x st $$ [Hx]
    · iframe Hx; ipureintro; exact htk
    try wp_auto
    cases st
    · simp only [Bool.false_eq_true, ite_false] at Hv
      try wp_auto
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'w.method_unfold]
      try wp_auto
      wp_apply wp_w gx x  $$ [Hx] as %e #He
      · iexact Hx
      try wp_auto
      rw [show (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.FFirst : val) = #fFirst from rfl]
      wp_apply wp_has e x.w fFirst x.w.first.isSome $$ [He]
      · iframe He; ipureintro; exact Event.hasF_First _
      cases hf : x.w.first.isSome
      · simp only [hf, Bool.false_eq_true, ite_false, pure_ok, Except.ok.injEq] at Hv
        subst Hv
        try wp_auto
        try wp_auto
        rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'L0.method_unfold]
        try wp_auto
        wp_apply wp_L0 gx x  $$ [Hx] as %l0 #Hl0
        · iexact Hx
        try wp_auto
        ihave %Hl0l := logRO_len _ _ $$ Hl0
        have hl := OnDisk.L0_le HW
        iapply HΦ; ipureintro
        rw [sint_add_one (by omega), Hl0l]
      · simp only [hf, ite_true] at Hv
        try wp_auto
        try wp_auto
        rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'w.method_unfold]
        try wp_auto
        wp_apply wp_w gx x  $$ [Hx] as %e' #He'
        · iexact Hx
        try wp_auto
        wp_apply wp_first e' x.w v $$ [He'] as %u %Hu
        · iframe He'; ipureintro; exact Hv
        try wp_auto
        iapply HΦ; ipureintro; exact Hu
    · simp only [ite_true] at Hv
      obtain ⟨fm, hfm, Hv⟩ := bind_ok Hv
      obtain ⟨k, hk, Hv⟩ := bind_ok Hv
      simp only [pure_ok, Except.ok.injEq] at Hv
      subst Hv
      have hfw := OnDisk.fm_within HW hfm
      have hkb := OnDisk.K_bounds hfm hk
      unfold numOk numBound at hfw
      try wp_auto
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'fm.method_unfold]
      try wp_auto
      wp_apply wp_fm gx x fm $$ [Hx] as %u #Hu
      · iframe Hx; ipureintro; exact hfm
      try wp_auto
      iunfold appendFactRO at Hu
      icases Hu with ⟨%Hur, #-⟩
      try wp_auto
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'K.method_unfold]
      try wp_auto
      wp_apply wp_K gx x k $$ [Hx] as %uk %Huk
      · iframe Hx; ipureintro; exact hk
      try wp_auto
      iapply HΦ; ipureintro
      rw [sint_add (by rw [Hur.2.2.2.1, Huk]; omega) (by rw [Hur.2.2.2.1, Huk]; omega), Hur.2.2.2.1, Huk]
  · rw [hsnap] at hsn; subst hsn
    have hst := hst1 rfl
    subst hst
    simp only [ite_true] at Hv
    obtain ⟨fm, hfm, Hv⟩ := bind_ok Hv
    obtain ⟨k, hk, Hv⟩ := bind_ok Hv
    simp only [pure_ok, Except.ok.injEq] at Hv
    subst Hv
    have hfw := OnDisk.fm_within HW hfm
    have hkb := OnDisk.K_bounds hfm hk
    unfold numOk numBound at hfw
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'fm.method_unfold]
    try wp_auto
    wp_apply wp_fm gx x fm $$ [Hx] as %u #Hu
    · iframe Hx; ipureintro; exact hfm
    try wp_auto
    iunfold appendFactRO at Hu
    icases Hu with ⟨%Hur, #-⟩
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'K.method_unfold]
    try wp_auto
    wp_apply wp_K gx x k $$ [Hx] as %uk %Huk
    · iframe Hx; ipureintro; exact hk
    try wp_auto
    iapply HΦ; ipureintro
    rw [sint_add (by rw [Hur.2.2.2.1, Huk]; omega) (by rw [Hur.2.2.2.1, Huk]; omega), Hur.2.2.2.1, Huk]

end proof

end AntCheck
end EtcdGrove
end Perennial
