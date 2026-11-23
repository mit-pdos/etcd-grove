/-
Lean-first (no Rocq counterpart). #33 S3b W4a (2026-11-23): the proof of `x.takes()` (B 291-359, `OnDisk.takes`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__takes
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__isApp
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__below
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__fm
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__PrevOk
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws

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

theorem onDisk.takes.wp_proof (wp_isApp : onDisk.isApp.spec (GF := GF) (hG := hG))
    (wp_below : onDisk.below.spec (GF := GF) (hG := hG)) (wp_fm : onDisk.fm.spec (GF := GF) (hG := hG))
    (wp_PrevOk : State.PrevOk.spec (GF := GF) (hG := hG)) :
    onDisk.takes.spec (GF := GF) (hG := hG) := by
  intro gx x v
  wp_start as ⟨#Hx, %Hv⟩
  ihave #Hx' := Hx
  iunfold onDiskRO at Hx'
  icases Hx' with ⟨#Hs, #Hq, #Hro, #Hld, #Hll, #Hch, #Htl, #Hvi, %Hp⟩
  obtain ⟨Hn, Hlt, -, -, -⟩ := Hp
  have Hn0 : 0 ≤ sint.Z gx.n' := by omega
  have hnn : sint.nat gx.n' = x.n := by have := sint_nat_cast Hn0; omega
  unfold OnDisk.takes at Hv
  obtain ⟨a, ha, ht, hf⟩ := andM_ok Hv
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_isApp_unfold.method_unfold]
  try wp_auto
  wp_apply wp_isApp gx x a $$ [Hx]
  · iframe Hx; ipureintro; exact ha
  cases a
  · rw [hf rfl]
    try wp_auto
    iapply HΦ; ipureintro; trivial
  have Hr := ht rfl
  obtain ⟨c, hc, ht2, hf2⟩ := andM_ok Hr
  unfold notM at hc
  obtain ⟨bl, hbl, hc⟩ := bind_ok hc
  simp only [pure_ok, Except.ok.injEq] at hc
  subst hc
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_below_unfold.method_unfold]
  try wp_auto
  wp_apply wp_below gx x bl $$ [Hx]
  · iframe Hx; ipureintro; exact hbl
  cases bl
  · have Hr2 := ht2 rfl
    obtain ⟨fm, hfm, Hr2⟩ := bind_ok Hr2
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_fm_unfold.method_unfold]
    try wp_auto
    wp_apply wp_fm gx x fm $$ [Hx] as %u #Hu
    · iframe Hx; ipureintro; exact hfm
    try wp_auto
    wp_apply wp_PrevOk gx.s' x.s gx.n' u fm v $$ [Hs Hu]
    · iframe Hs Hu; ipureintro; exact ⟨Hn0, by omega, by rw [hnn]; exact Hr2⟩
    try wp_auto
    iapply HΦ; ipureintro; trivial
  · rw [hf2 rfl]
    try wp_auto
    iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
