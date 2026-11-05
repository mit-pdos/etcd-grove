/-
Lean-first (no Rocq counterpart).

The proof of `(*compactor).CompactRevision`: under the mutex, the lock invariant's revision is
recorded and reached (`recRevOk`), and its counter's authority gives the lower bound and its order
with the caller's.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.compactor__CompactRevision
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
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [sync_sem : sync.Assumptions]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem compactor.CompactRevision.wp_proof :
    compactor.CompactRevision.spec (GF := GF) (hG := hG) := by
  intro c cl γk recorded γc r0
  wp_start as ⟨#Hc, Hlb⟩
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold compactRevLb at Hlb
  iunfold isCompactor at Hc
  icases Hc with ⟨#Hc, -⟩
  iunfold compactorCore at Hc
  icases Hc with ⟨%Hpers, #Hcl, #Hiv, #Hck, #Honc, #Hmu, #Hstop⟩
  (try wp_auto)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (sync.Mutex.wp_Lock _ (compactorLockInv c γk recorded γc)) $$ [] as ⟨Hlocked, HR⟩
  · iframe #
  haveI := Hpers
  iunfold compactorLockInv at HR
  icases HR with ⟨%r, Hr, Hauth, #Hok⟩
  (try wp_auto)
  ihave %Hle := monoNatLbOwn_valid γc.lb 1 _ _ $$ Hauth Hlb
  ihave #Hlb' := monoNatLbOwn_get γc.lb 1 _ $$ Hauth
  wp_apply (sync.Mutex.wp_Unlock _ (compactorLockInv c γk recorded γc)) $$ [Hlocked Hr Hauth]
  · iframe #
    iframe Hlocked
    inext
    iunfold compactorLockInv
    iexists r
    iframe
    iframe #
  (try wp_auto)
  iapply HΦ
  unfold compactRevLb
  iframe #
  ipureintro
  exact Hle.2

end proof

end k8s
end EtcdGrove
end Perennial
