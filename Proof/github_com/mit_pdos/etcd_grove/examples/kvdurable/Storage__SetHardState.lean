/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/Storage__SetHardState.lean`.
Lean-first (no Rocq counterpart): the image's hard state field set, then the `MemoryStorage`'s.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Storage__SetHardState
public import Spec.go_etcd_io.raft.v3.MemoryStorage__SetHardState

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

theorem Storage.SetHardState.wp_proof
    (wp_SetHardState : MemoryStorage.SetHardState.spec (GF := GF) (hG := hG)) :
    Storage.SetHardState.spec (GF := GF) (hG := hG) := by
  intro s ms γs hs ip I p hs'
  wp_start as ⟨#Hrec, Hmeta, #Himg, HI, #Hhs'⟩
  iunfold kdStorRec at Hrec
  icases Hrec with ⟨#Hmsf, -⟩
  iunfold ownImage at HI
  icases HI with ⟨%hsp, %sp, %es, HI⟩
  iNamed HI
  wp_auto
  wp_apply wp_SetHardState ms γs hs p hs' $$ [$Hmeta $Hhs'] as Hmeta
  iapply HΦ
  iframe
  iunfold ownImage
  iexists p, sp, es
  simp only [imgSetHardState]
  iframe # ∗
  ipureintro; exact Hwf

end proof

end kvdurable
end EtcdGrove
end Perennial
