/-
Proof of `checker.fresh`: under `c.mu` (`checkerInv`), the counter `*next` at `a`; at `2^64 - 1` the
loop `for {}` never ends; else the counter goes to `a + 1`, which no issued number reaches
(`IssuedLe`), so the ghost map of the issued numbers takes it (`ghost_map_insert`), and its element
is the caller's `issued γ w (a + 1)`.
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.checker__fresh
public import Perennial.Proof.sync.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvcheck

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- The counter's next number is not issued, and every issued number stays at most it. -/
theorem issuedLe_step (M : GMap w64 Unit) (a : w64) (h : IssuedLe M a) (ha : a ≠ W64 (2 ^ 64 - 1)) :
    M.lookup (a + W64 1) = none ∧ IssuedLe (M.insert (a + W64 1) ()) (a + W64 1) := by
  have hne : a.toNat ≠ 2 ^ 64 - 1 := fun hn => ha (BitVec.eq_of_toNat_eq (by rw [hn]; rfl))
  have hlt : a.toNat < 2 ^ 64 - 1 := by have := a.isLt; omega
  have hs : (a + W64 1).toNat = a.toNat + 1 := by
    rw [BitVec.toNat_add]
    show (a.toNat + 1) % 2 ^ 64 = a.toNat + 1
    exact Nat.mod_eq_of_lt (by omega)
  have hz : ∀ x : w64, uint.Z x = (x.toNat : Int) := fun _ => rfl
  constructor
  · cases hk : M.lookup (a + W64 1) with
    | none => rfl
    | some u =>
      have := h _ (by rw [hk]; rfl)
      rw [hz, hz, hs] at this
      omega
  · intro k hk
    by_cases e : a + W64 1 = k
    · subst e; exact Int.le_refl _
    · have hk' : (M.lookup k).isSome := by
        simp only [GMap.insert] at hk
        rw [ite_eq_right_iff.mpr (fun h => absurd h e)] at hk
        exact hk
      have := h k hk'
      rw [hz, hz] at this
      rw [hz, hz, hs]
      omega

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.Assumptions]

theorem checker.fresh.wp_proof : checker.fresh.spec (GF := GF) (hG := hG) := by
  intro c γ ls w next Hnext
  wp_start as #Hc
  iunfold isChecker at Hc
  icases Hc with ⟨%sl, #Ha, #Hsl, #Hmu⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HL⟩
  iunfold checkerInv at HL
  icases HL with ⟨%a, %b, %Ma, %Mb, %lc, %cs, Hop, Hrd, Hlc, Hcs, HMa, HMb, %HLe⟩
  -- the counter `w` names, its value and its ghost map; the other's kept aside
  ihave Hsel : iprop(∃ (x : w64) (M : GMap w64 Unit), next ↦ x ∗ ghostMapAuth (issuedName γ w) 1 M ∗
      ⌜IssuedLe M x⌝ ∗
      (∀ (x' : w64) (M' : GMap w64 Unit), next ↦ x' -∗ ghostMapAuth (issuedName γ w) 1 M' -∗
        ⌜IssuedLe M' x'⌝ -∗ checkerInv c γ)) $$ [Hop Hrd Hlc Hcs HMa HMb]
  · cases w
    · subst Hnext
      iexists a, Ma
      simp only [issuedName, Bool.false_eq_true, ↓reduceIte]
      iframe Hop HMa
      isplitr
      · ipureintro; exact HLe.1
      iintro %x' %M' Hx HM %HM
      iunfold checkerInv
      iexists x', b, M', Mb, lc, cs
      iframe
      ipureintro; exact ⟨HM, HLe.2⟩
    · subst Hnext
      iexists b, Mb
      simp only [issuedName, ↓reduceIte]
      iframe Hrd HMb
      isplitr
      · ipureintro; exact HLe.2
      iintro %x' %M' Hx HM %HM
      iunfold checkerInv
      iexists a, x', Ma, M', lc, cs
      iframe
      ipureintro; exact ⟨HLe.1, HM⟩
  icases Hsel with ⟨%x, %M, Hx, HM, %HMx, Hclose⟩
  wp_auto
  wp_if_destruct
  · -- the counter is spent: unlock, then loop forever
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hx HM Hclose]
    · inext
      iapply Hclose $$ Hx HM
      ipureintro; exact HMx
    try wp_auto
    ihave HI : iprop(True) $$ []
    · itrivial
    wp_for HI
    try wp_auto
    wp_for_post
    iframe
  · -- the next number: the counter, then the ghost map, take it
    try wp_auto
    have Hst := issuedLe_step M x HMx Hif
    imod ghost_map_insert (x + W64 1) () Hst.1 $$ HM with ⟨HM, Hn⟩
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hx HM Hclose]
    · inext
      iapply Hclose $$ Hx HM
      ipureintro; exact Hst.2
    try wp_auto
    iapply HΦ
    unfold issued
    iexact Hn

end proof

end raft_kvcheck
end EtcdGrove
end Perennial
