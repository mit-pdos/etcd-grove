/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/InmemStore__FirstIndex.lean (241f27e).
-/
/-
The proof of `raft.(*InmemStore).FirstIndex`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.InmemStore__FirstIndex

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft proto

theorem github_com.hashicorp.raft.InmemStore.FirstIndex.wp_proof :
    github_com.hashicorp.raft.InmemStore.FirstIndex.spec (GF := GF) (hG := hG) :=
  fun γs i tid => by
  wp_start as ⟨#His, Htok⟩
  iNamed His
  unfold inmemPool
  icases Hpool with ⟨%γp, #Hpool⟩
  iapply wp_fupd
  wp_auto
  wp_apply (lc := 2) wp_with_defer as %defer Hdefer
  imod qpool.borrow_lc inmemPoolN γp _ ⊤ (by solve_ndisj) tid $$ [$Hlc1 $Hpool $Htok]
    with ⟨Hown, Hloan⟩
  wp_apply (sync.RWMutex.wp_RLock (i.[InmemStore, go!"l"]) (storeInv γs i)) $$ [$Hown]
    with ⟨Hrlocked, HP⟩
  imod lc_fupd_elim_later (E := ⊤) $$ Hlc2 HP with HP
  icases (storeInv_unfold γs i _).mp $$ HP with
    ⟨%c, Hgc, Hlow, Hhigh, Hlogsf, Hlogs, Hkvf, Hkv, Hkvintf, Hkvint, Hgl, Hgk, %Hok, #Hpers⟩
  wp_auto
  wp_apply (sync.RWMutex.wp_RUnlock (i.[InmemStore, go!"l"]) (storeInv γs i))
    $$ [$Hrlocked Hgc Hlow Hhigh Hlogsf Hlogs Hkvf Hkv Hkvintf Hkvint Hgl Hgk] with Hown
  · inext
    iapply (storeInv_unfold γs i _).mpr
    iexists c
    iframe
    iframe #
    ipureintro; exact Hok
  imod qpool.giveBack inmemPoolN γp _ ⊤ (by solve_ndisj) tid $$ [$Hpool $Hloan $Hown]
    with Htok
  imodintro
  iapply HΦ $$ Htok

end proof

end Perennial
