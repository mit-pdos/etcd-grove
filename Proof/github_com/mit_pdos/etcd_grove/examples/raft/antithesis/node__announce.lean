/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/node__announce.lean`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__announce
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__emit
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessPersist
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.SpecsB2
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.below
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessReportB2

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- `emit` records only on a live node, which it leaves alive. -/
theorem emitStep_true {d : Bool} {f : w64} {d1 : Bool} {f1 : w64} (h : emitStep d f = (true, d1, f1)) :
    d1 = false := by
  unfold emitStep at h
  cases d
  · rw [if_neg Bool.false_ne_true] at h
    by_cases hz : uint.Z f > 0
    · rw [if_pos hz] at h
      by_cases h1 : f - W64 1 = W64 0
      · rw [if_pos h1] at h; simp only [Prod.mk.injEq] at h; exact absurd h.1 Bool.false_ne_true
      · rw [if_neg h1] at h; simp only [Prod.mk.injEq] at h; exact h.2.1.symm
    · rw [if_neg hz] at h; simp only [Prod.mk.injEq] at h; exact h.2.1.symm
  · rw [if_pos rfl] at h; simp only [Prod.mk.injEq] at h; exact absurd h.1 Bool.false_ne_true

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem node.announce.wp_proof (wp_emit : node.emit.spec (GF := GF) (hG := hG)) :
    node.announce.spec (GF := GF) (hG := hG) := by
  intro c γ n j p ev Q
  wp_start as ⟨#Hc, #Hn, Hok, Hev, Hrep⟩
  wp_auto
  wp_apply wp_emit c γ n j p ev Q $$ [$Hpkg $Hc $Hn $Hok $Hev $Hrep] as ⟨Hok, HQ⟩
  iunfold emitOk at Hok
  icases Hok with ⟨Hdead, Hfuse⟩
  try wp_auto
  iapply HΦ
  iframe
  iunfold emitOk
  iframe

/-- **`node.announce.specB2`** (#33 parity B2; staged beside B1's `wp_proof`): `emit`, then, recorded
with a fuse of `1` left, a kill when `below(2)` draws `0`. -/
theorem node.announce.wp_proofB2 (wp_emit : node.emit.specB2 (GF := GF) (hG := hG))
    (wp_below : below.spec (GF := GF) (hG := hG)) :
    node.announce.specB2 (GF := GF) (hG := hG) := by
  intro c γ n j p ev Q dead fuse
  wp_start as ⟨#Hc, #Hn, Hk, Hev, Hrep⟩
  wp_auto
  wp_apply wp_emit c γ n j p ev Q dead fuse $$ [$Hpkg $Hc $Hn $Hk $Hev $Hrep] as %b ⟨Hk, %Hb, HQ⟩
  subst Hb
  generalize hes : emitStep dead fuse = es at *
  rcases es with ⟨b1, d1, f1⟩
  cases b1
  · -- not recorded
    wp_auto
    iapply HΦ
    iframe
    ipureintro
    exact ⟨fun h => Bool.noConfusion h, .inl ⟨rfl, rfl, rfl⟩⟩
  · have hd1 : d1 = false := emitStep_true hes
    subst hd1
    iunfold killOwn at Hk
    icases Hk with ⟨Hdead, Hfuse⟩
    wp_auto
    by_cases hf1 : f1 = W64 1
    · rw [decide_eq_true hf1]
      wp_auto
      wp_apply wp_below (W64 2) (by decide) $$ [$Hpkg] as %r %Hr
      by_cases hr : r = W64 0
      · -- killed between the announcement and the write
        rw [hr]
        wp_auto
        iapply HΦ
        iunfold killOwn
        iframe
        ipureintro
        exact ⟨fun h => Bool.noConfusion h, .inr ⟨rfl, .inr ⟨hf1, rfl, rfl⟩⟩⟩
      · rw [decide_eq_false hr]
        wp_auto
        iapply HΦ
        iunfold killOwn
        iframe
        ipureintro
        exact ⟨fun _ => rfl, .inr ⟨rfl, .inl ⟨rfl, rfl⟩⟩⟩
    · rw [decide_eq_false hf1]
      wp_auto
      iapply HΦ
      iunfold killOwn
      iframe
      ipureintro
      exact ⟨fun _ => rfl, .inr ⟨rfl, .inl ⟨rfl, rfl⟩⟩⟩

end proof

end AntHarness
end EtcdGrove
end Perennial
