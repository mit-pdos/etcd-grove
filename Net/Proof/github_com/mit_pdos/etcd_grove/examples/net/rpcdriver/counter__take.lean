/- Lean-first (no Rocq counterpart).

# `(*counter).take`'s proof

Under the counter's mutex: the credit spent (`ownTokAuth_delete_S`), the id `start + n` fresh
(`issued_fresh`, `n < ctrBudget < 2 ^ 64`), its token made (`ghost_map_insert`).
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.counter__take
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Perennial.Proof.sync.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [π : NetProtoGS]

theorem counter.take.wp_proof : counter.take.spec (GF := GF) (hG := hG) := by
  intro γid γb c
  wp_start as ⟨#Hc, Hcred⟩
  iunfold isCtr at Hc
  icases Hc with ⟨#Hsync, %start, #Hmu⟩
  try wp_auto
  wp_apply sync.Mutex.wp_Lock _ (ctrInv γid γb start c) $$ [$Hsync $Hmu] as ⟨Hlk, Hinv⟩
  iunfold ctrInv at Hinv
  icases Hinv with ⟨%n, %k, Hnext, Hauth, Htoks, %Hb⟩
  icombine Htoks Hcred gives %Hk
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  imod ownTokAuth_delete_S γb k' $$ Htoks Hcred with Htoks
  have hfresh : (issued start n).lookup (start + W64 n) = none :=
    issued_fresh start n n (Nat.le_refl n) (by unfold ctrBudget at Hb; omega)
  imod ghost_map_insert (start + W64 n) () hfresh $$ Hauth with ⟨Hauth, Htok⟩
  try wp_auto
  wp_apply sync.Mutex.wp_Unlock _ (ctrInv γid γb start c) $$ [$Hsync $Hmu $Hlk Hnext Hauth Htoks]
  · iunfold ctrInv
    iexists n + 1, k'
    have hnx : start + W64 (n : Int) + W64 1 = start + W64 ((n + 1 : Nat) : Int) := by word
    rw [hnx]
    iframe Hnext Htoks
    isplitl [Hauth]
    · simp only [issued]
      iexact Hauth
    ipureintro; omega
  try wp_auto
  iapply HΦ
  unfold idTok
  iexact Htok

end proof

end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver
end Perennial
