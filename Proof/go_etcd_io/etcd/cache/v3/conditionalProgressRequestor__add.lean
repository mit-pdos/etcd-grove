/-
Proof of `Spec/conditionalProgressRequestor__add.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.conditionalProgressRequestor__add

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem conditionalProgressRequestor.add.wp_proof :
    conditionalProgressRequestor.add.spec (GF := GF) (hG := hG) := by
  intro p
  wp_start as #Hp
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  unfold isProgressRequestor
  icases Hp with ⟨%cp, #Hcp, #Hcond, #Hmu⟩
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  unfold prLockInv
  icases Hinv with ⟨%w, %b, Hw, Hb⟩
  wp_auto
  wp_apply sync.Cond.wp_Signal $$ [$Hcond]
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hw Hb]
  · inext; iexists _, b; iframe
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
