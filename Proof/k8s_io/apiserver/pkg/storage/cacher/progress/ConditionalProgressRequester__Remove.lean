/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/cacher/progress/ConditionalProgressRequester__Remove.lean`:
under the mutex, the counter decremented. Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.cacher.progress.ConditionalProgressRequester__Remove

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cacher

open Iris Iris.BI Iris.ProofMode k8s_io.apiserver.pkg.storage.cacher.progress

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.cacher.progress.Assumptions]

theorem ConditionalProgressRequester.Remove.wp_proof :
    ConditionalProgressRequester.Remove.spec (GF := GF) (hG := hG) := by
  intro pr
  wp_start as #Hpr
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  unfold isPR
  icases Hpr with ⟨%c, #Hc, #Hcond, #Hmu⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (sync.Mutex.wp_Lock (structFieldRef ConditionalProgressRequester go!"mux" pr)
    (prLockInv pr)) $$ [] as ⟨Hown, Hinv⟩
  · iframe #
  iunfold prLockInv at Hinv
  icases Hinv with ⟨%n, %b, Hn, Hb⟩
  (try wp_auto)
  wp_apply (sync.Mutex.wp_Unlock (structFieldRef ConditionalProgressRequester go!"mux" pr)
    (prLockInv pr)) $$ [Hown Hn Hb]
  · iframe #
    iframe Hown
    inext
    iunfold prLockInv
    iexists _, b
    iframe
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end cacher
end EtcdGrove
end Perennial
