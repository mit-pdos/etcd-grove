/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/InmemStore__GetUint64.lean (241f27e).
-/
/-
The proof of `raft.(*InmemStore).GetUint64`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.InmemStore__GetUint64
public import Perennial.Proof.errors.NewVar

@[expose] public section

set_option linter.deprecated false

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

theorem github_com.hashicorp.raft.InmemStore.GetUint64.wp_proof :
    github_com.hashicorp.raft.InmemStore.GetUint64.spec (GF := GF) (hG := hG) :=
  fun γs i key kb tid => by
  wp_start as ⟨#His, #Hkey, Htok⟩
  iNamed His
  unfold inmemPool
  icases Hpool with ⟨%γp, #Hpool⟩
  iapply wp_fupd
  wp_auto
  wp_apply (lc := 3) wp_with_defer as %defer Hdefer
  imod qpool.borrow_lc inmemPoolN γp _ ⊤ (by solve_ndisj) tid $$ [$Hlc1 $Hpool $Htok]
    with ⟨Hown, Hloan⟩
  wp_apply (sync.RWMutex.wp_RLock (i.[InmemStore, go!"l"]) (storeInv γs i)) $$ [$Hown]
    with ⟨Hrlocked, HP⟩
  imod lc_fupd_elim_later (E := ⊤) $$ Hlc2 HP with HP
  icases (storeInv_unfold γs i _).mp $$ HP with
    ⟨%c, Hgc, Hlow, Hhigh, Hlogsf, Hlogs, Hkvf, Hkv, Hkvintf, Hkvint, Hgl, Hgk, %Hok, #Hpers⟩
  iapply wp_ncfupd _ _ rfl
  iintro Hnc
  imod HΦ $$ Hnc with ⟨Hnc, HAU⟩
  imod lc_fupd_elim_later (E := ∅) $$ Hlc3 HAU with ⟨%st, Hkvw, Hclose⟩
  ihave %Hst := kvView_agree γs _ st c.st $$ Hkvw Hgk
  subst Hst
  imod Hclose $$ Hkvw with HΦ
  imodintro
  iframe Hnc
  wp_apply (wp_bytes_to_string key kb DFrac.discard) $$ [$Hkey] with -
  wp_apply (wp_map_lookup1 go.string go.uint64 c.mint c.st.ints kb (DFrac.own sync.rfrac))
    $$ [$Hkvint] with Hkvint
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
  simp only [show (Perennial.zero_val w64 : w64) = W64 0 from rfl]
  iapply HΦ $$ Htok

end proof

end Perennial
