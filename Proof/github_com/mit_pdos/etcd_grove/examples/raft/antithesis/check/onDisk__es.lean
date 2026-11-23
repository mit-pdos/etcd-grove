/-
Lean-first (no Rocq counterpart). #33 S3b W4a (2026-11-23): the proof of `x.es()` (B 291-359, `OnDisk.es`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__es
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__w
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__snaps
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__takes
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__fm
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__K
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__bat
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SubSeq
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__entries
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Init0Laws

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

theorem onDisk.es.wp_proof (wp_w : onDisk.w.spec (GF := GF) (hG := hG))
    (wp_snaps : onDisk.snaps.spec (GF := GF) (hG := hG)) (wp_takes : onDisk.takes.spec (GF := GF) (hG := hG))
    (wp_fm : onDisk.fm.spec (GF := GF) (hG := hG)) (wp_K : onDisk.K.spec (GF := GF) (hG := hG))
    (wp_bat : onDisk.bat.spec (GF := GF) (hG := hG)) (wp_SubSeq : SubSeq.spec (GF := GF) (hG := hG))
    (wp_entries : Event.entries.spec (GF := GF) (hG := hG)) :
    onDisk.es.spec (GF := GF) (hG := hG) := by
  intro gx x v
  wp_start as ⟨#Hx, %Hv⟩
  unfold OnDisk.es at Hv
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_snaps_unfold.method_unfold]
  try wp_auto
  wp_apply wp_snaps gx x $$ [Hx]
  · iexact Hx
  obtain ⟨st, hst, Hv⟩ := bind_ok Hv
  obtain ⟨sn, hsn, hst1, hst2⟩ := orM_ok hst
  simp only [pure_ok, Except.ok.injEq] at hsn
  cases hsnap : x.snaps
  · rw [hsnap] at hsn; subst hsn
    have htk := hst2 rfl
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_takes_unfold.method_unfold]
    try wp_auto
    wp_apply wp_takes gx x st $$ [Hx]
    · iframe Hx; ipureintro; exact htk
    cases st
    · simp only [Bool.false_eq_true, ite_false] at Hv
      try wp_auto
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_bat_unfold.method_unfold]
      try wp_auto
      wp_apply wp_bat gx x $$ [Hx]
      · iexact Hx
      cases hbat : x.bat
      · simp only [hbat, Bool.false_eq_true, ite_false] at Hv
        try wp_auto
        rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_w_unfold.method_unfold]
        try wp_auto
        wp_apply wp_w gx x $$ [Hx] as %e #He
        · iexact Hx
        try wp_auto
        wp_apply wp_entries e x.w v $$ [He] as %r #Hr
        · iframe He; ipureintro; exact Hv
        try wp_auto
        iapply HΦ; iexact Hr
      · simp only [hbat, ite_true, pure_ok, Except.ok.injEq] at Hv
        subst Hv
        try wp_auto
        iapply HΦ; iapply Init0_logNil
    · simp only [ite_true] at Hv
      try wp_auto
      obtain ⟨fm, hfm, Hv⟩ := bind_ok Hv
      obtain ⟨k, hk, Hv⟩ := bind_ok Hv
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_fm_unfold.method_unfold]
      try wp_auto
      wp_apply wp_fm gx x fm $$ [Hx] as %u #Hu
      · iframe Hx; ipureintro; exact hfm
      iunfold appendFactRO at Hu
      icases Hu with ⟨%Hur, #Hes⟩
      ihave %Hesl := logRO_len _ _ $$ Hes
      try wp_auto
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_K_unfold.method_unfold]
      try wp_auto
      wp_apply wp_K gx x k $$ [Hx] as %uk %Huk
      · iframe Hx; ipureintro; exact hk
      try wp_auto
      wp_apply wp_SubSeq u.Entries' fm.entries uk u.Entries'.len v $$ [Hes] as %r #Hr
      · iframe Hes; ipureintro; rw [Huk, Hesl]; exact Hv
      try wp_auto
      iapply HΦ; iexact Hr
  · rw [hsnap] at hsn; subst hsn
    have hst := hst1 rfl
    subst hst
    simp only [ite_true] at Hv
    try wp_auto
    obtain ⟨fm, hfm, Hv⟩ := bind_ok Hv
    obtain ⟨k, hk, Hv⟩ := bind_ok Hv
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_fm_unfold.method_unfold]
    try wp_auto
    wp_apply wp_fm gx x fm $$ [Hx] as %u #Hu
    · iframe Hx; ipureintro; exact hfm
    iunfold appendFactRO at Hu
    icases Hu with ⟨%Hur, #Hes⟩
    ihave %Hesl := logRO_len _ _ $$ Hes
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_K_unfold.method_unfold]
    try wp_auto
    wp_apply wp_K gx x k $$ [Hx] as %uk %Huk
    · iframe Hx; ipureintro; exact hk
    try wp_auto
    wp_apply wp_SubSeq u.Entries' fm.entries uk u.Entries'.len v $$ [Hes] as %r #Hr
    · iframe Hes; ipureintro; rw [Huk, Hesl]; exact Hv
    try wp_auto
    iapply HΦ; iexact Hr

end proof

end AntCheck
end EtcdGrove
end Perennial
