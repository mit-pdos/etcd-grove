/-
Proof of `checker.fresh`: under `c.mu` (`checkerInv`), the counter `*next` at `a`; at `2^64 - 1` the
loop `for {}` never ends; else the counter goes to `a + 1`, which no issued number reaches
(`IssuedLe`), so the ghost map of the issued numbers takes it (`ghost_map_insert`), and its element
is the caller's `issued γ w (a + 1)`.
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.checker__fresh
public import Perennial.Proof.sync.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvcheck

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.Assumptions]

theorem checker.fresh.wp_proof : checker.fresh.spec (GF := GF) (hG := hG) := by
  intro c γ ls w next L Hnext
  wp_start as ⟨#Hc, Hlaw⟩
  iunfold isChecker at Hc
  icases Hc with ⟨%sl, #Ha, #Hsl, #Hmu⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HL⟩
  iunfold checkerInv at HL
  icases HL with ⟨%a, %b, %lc, %cs, Hop, Hrd, Hlc, Hcs, HMa, HMb⟩
  -- the counter `w` names and its predicate; the other's kept aside
  ihave Hsel : iprop(∃ x : w64, next ↦ x ∗ γ w x ∗
      (∀ x' : w64, next ↦ x' -∗ γ w x' -∗ checkerInv c γ)) $$ [Hop Hrd Hlc Hcs HMa HMb]
  · cases w
    · subst Hnext
      simp only [Bool.false_eq_true, ↓reduceIte]
      iexists a
      iframe Hop HMa
      iintro %x' Hx HM
      iunfold checkerInv
      iexists x', b, lc, cs
      iframe
    · subst Hnext
      simp only [↓reduceIte]
      iexists b
      iframe Hrd HMb
      iintro %x' Hx HM
      iunfold checkerInv
      iexists a, x', lc, cs
      iframe
  icases Hsel with ⟨%x, Hx, HM, Hclose⟩
  wp_auto
  wp_if_destruct
  · -- the counter is spent: unlock, then loop forever
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hx HM Hclose]
    · inext
      iapply Hclose $$ Hx HM
    try wp_auto
    ihave HI : iprop(True) $$ []
    · itrivial
    wp_for HI
    try wp_auto
    wp_for_post
    iframe
  · -- the next number, minted by the caller's law under the lock
    try wp_auto
    have Hx1 : uint.Z x + 1 < 2 ^ 64 := by
      have : x ≠ W64 18446744073709551615 := by assumption
      word
    imod Hlaw $$ %x %Hx1 HM with ⟨HM, HLn⟩
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hx HM Hclose]
    · inext
      iapply Hclose $$ Hx HM
    try wp_auto
    iapply HΦ
    iexact HLn

end proof

end raft_kvcheck
end EtcdGrove
end Perennial
