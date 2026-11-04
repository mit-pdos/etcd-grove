/-
Lean-first (no Rocq counterpart).

The proof of `(*compactor).UpdateCompactRevision`: `0` changes nothing (its lower bound is
trivial); otherwise, under the mutex, the revision becomes the larger of the two, each recorded and
reached (`recRevOk`), and the counter's authority moves up to it, giving the caller's lower bound.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.compactor__UpdateCompactRevision
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Perennial.Proof.sync.Link
import all Proof.k8s_io.apiserver.pkg.storage.etcd3.CompactorDefs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [sync_sem : sync.Assumptions]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]


/-- The builtin `max` on `int64`. -/
private theorem wp_max_int64 (x y : w64) :
    {{ (True : IProp GF) }}
      (App (App (Val #(functions go.max [go.int64, go.int64])) (Val #x)) (Val #y))
    {{ RET #(if sint.Z y < sint.Z x then x else y); True }} := by
  wp_start
  by_cases h : sint.Z y < sint.Z x
  · rw [decide_eq_true h]; simp only [h, ↓reduceIte]; wp_auto; iapply HΦ; itrivial
  · rw [decide_eq_false h]; simp only [h, ↓reduceIte]; wp_auto; iapply HΦ; itrivial

theorem compactor.UpdateCompactRevision.wp_proof :
    compactor.UpdateCompactRevision.spec (GF := GF) (hG := hG) := by
  intro c cl γk recorded γc rev
  wp_start as ⟨#Hc, Hrev⟩
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold compactorCore at Hc
  icases Hc with ⟨%Hpers, #Hcl, #Hiv, #Hck, #Honc, #Hmu, #Hstop⟩
  haveI := Hpers
  (try wp_auto)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  imod monoNatLbOwn_0 (GF := GF) γc.lb with #H0
  wp_if_destruct
  · (try wp_auto)
    iapply HΦ
    unfold compactRevLb
    simp
    iexact H0
  (try wp_auto)
  wp_apply (sync.Mutex.wp_Lock _ (compactorLockInv c γk recorded γc)) $$ [] as ⟨Hlocked, HR⟩
  · iframe #
  iunfold compactorLockInv at HR
  icases HR with ⟨%r, Hr, Hauth, #Hok⟩
  (try wp_auto)
  wp_apply wp_max_int64 r rev
  (try wp_auto)
  have hle1 : (sint.Z r).toNat ≤ (sint.Z (if sint.Z rev < sint.Z r then r else rev)).toNat := by
    split <;> omega
  have hle2 : (sint.Z rev).toNat ≤ (sint.Z (if sint.Z rev < sint.Z r then r else rev)).toNat := by
    split <;> omega
  imod mono_nat_own_update _ hle1 $$ Hauth with ⟨Hauth, #Hlb⟩
  ihave #Hlb2 := monoNatLbOwn_le _ hle2 $$ Hlb
  wp_apply (sync.Mutex.wp_Unlock _ (compactorLockInv c γk recorded γc)) $$ [Hlocked Hr Hauth Hrev]
  · iframe #
    iframe Hlocked
    inext
    iunfold compactorLockInv
    iexists (if sint.Z rev < sint.Z r then r else rev)
    iframe
    split
    · iframe #
    · iframe
  (try wp_auto)
  iapply HΦ
  unfold compactRevLb
  iframe #

end proof

end k8s
end EtcdGrove
end Perennial
