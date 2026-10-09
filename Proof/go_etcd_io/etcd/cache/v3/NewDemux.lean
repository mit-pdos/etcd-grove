/-
Proof of `Spec/go_etcd_io/etcd/cache/v3/NewDemux.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.NewDemux
public import Spec.go_etcd_io.etcd.cache.v3.newDemux
public import Spec.go_etcd_io.etcd.cache.v3.demux__resyncLoop

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem actualMaxReaders_ge_2 : 2 ≤ Int.toNat sync.rwmutex.actualMaxReaders := by
  rw [sync.rwmutex.actualMaxReaders_unseal]; decide

/-- One element out of a replicated separating conjunction. -/
theorem bigSepL_replicate_pop (P : IProp GF) (n m : Nat) (h : n = m + 1) :
    ([∗list] _x ∈ List.replicate n (), P) ⊢ P ∗ [∗list] _x ∈ List.replicate m (), P := by
  subst h
  rw [List.replicate_succ]
  exact BigSepL.bigSepL_cons.1

theorem NewDemux.wp_proof (wp_newDemux : newDemux.spec (GF := GF) (hG := hG))
    (wp_resyncLoop : demux.resyncLoop.spec (GF := GF) (hG := hG)) :
    NewDemux.spec (GF := GF) (hG := hG) := fun C ctx s wg Pslot Prun Pret h ri => by
  wp_start as ⟨#Hctx, #Hh, #Hwgp, Hslot⟩
  wp_auto
  wp_apply wp_newDemux C h ri $$ [$Hpkg $Hh] as %d %γd %γn ⟨#Hd, Hw, Hhs, #Hlb, Hrhs⟩
  have h2 := actualMaxReaders_ge_2
  have e1 : Int.toNat sync.rwmutex.actualMaxReaders - 1 =
      (Int.toNat sync.rwmutex.actualMaxReaders - 2) + 1 := by omega
  have e2 : Int.toNat sync.rwmutex.actualMaxReaders =
      (Int.toNat sync.rwmutex.actualMaxReaders - 1) + 1 := by omega
  icases bigSepL_replicate_pop _ _ _ e1 $$ Hhs with ⟨Hh1, Hhs⟩
  icases bigSepL_replicate_pop _ _ _ e2 $$ Hrhs with ⟨Hrh1, Hrhs⟩
  try wp_auto
  wp_apply wp_wgSlot_Add wg Pslot Prun Pret $$ [$Hwgp $Hslot] as ⟨Hrun, Hret⟩
  ipersist ctx
  ipersist d
  ipersist wg
  wp_apply wp_fork $$ [Hrun Hh1 Hrh1]
  · wp_apply wp_with_defer as %defer defer
    try wp_auto
    wp_apply wp_resyncLoop d γd (sint.nat h) C γn ctx s $$ [$Hpkg $Hd $Hh1 $Hrh1 $Hctx] as -
    wp_apply wp_wgSlot_Done wg Pslot Prun Pret $$ [$Hwgp $Hrun]
    itrivial
  try wp_auto
  iapply HΦ
  iframe
  iframe #

end proof

end EtcdGrove
end Perennial
