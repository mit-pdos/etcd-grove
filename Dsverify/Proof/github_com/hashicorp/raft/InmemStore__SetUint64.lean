/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/InmemStore__SetUint64.lean (241f27e).
-/
/-
The proof of `raft.(*InmemStore).SetUint64`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.InmemStore__SetUint64
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

theorem github_com.hashicorp.raft.InmemStore.SetUint64.wp_proof :
    github_com.hashicorp.raft.InmemStore.SetUint64.spec (GF := GF) (hG := hG) :=
  fun γs i key kb v => by
  wp_start as ⟨#His, #Hkey⟩
  iNamed His
  wp_auto
  wp_apply (lc := 2) wp_with_defer as %defer Hdefer
  wp_apply (sync.RWMutex.wp_Lock_guard (i.[InmemStore, go!"l"]) (storeInv γs i)) $$ [$Hguard]
    with ⟨Hlocked, HP⟩
  imod lc_fupd_elim_later (E := ⊤) $$ Hlc1 HP with HP
  icases (storeInv_unfold γs i 1).mp $$ HP with
    ⟨%c, Hgc, Hlow, Hhigh, Hlogsf, Hlogs, Hkvf, Hkv, Hkvintf, Hkvint, Hgl, Hgk, %Hok, #Hpers⟩
  wp_apply (wp_bytes_to_string key kb DFrac.discard) $$ [$Hkey] with -
  wp_apply (wp_mapInsert go.string c.mint c.st.ints kb v) $$ [$Hkvint] with Hkvint
  iapply wp_ncfupd _ _ rfl
  iintro Hnc
  imod (fupd_mask_subseteq (PROP := IProp GF) (E1 := ⊤) (E2 := ⊤ \ ↑storeN) (by solve_ndisj)) with Hmask
  imod HΦ $$ Hnc with ⟨Hnc, HAU⟩
  imod lc_fupd_elim_later (E := ∅) $$ Hlc2 HAU with ⟨%st, Hkvw, Hclose⟩
  ihave %Hst := kvView_agree γs _ st c.st $$ Hkvw Hgk
  subst Hst
  imod kvView_update γs c.st c.st { c.st with ints := c.st.ints.insert kb v } $$ Hkvw Hgk
    with ⟨Hkvw, Hgk⟩
  imod Hclose $$ Hkvw with HΦ
  imod Hmask with -
  imodintro
  iframe Hnc
  imod conc_update γs c { c with st := { c.st with ints := c.st.ints.insert kb v } } $$ Hgc
    with Hgc
  wp_apply (sync.RWMutex.wp_Unlock_guard (i.[InmemStore, go!"l"]) (storeInv γs i))
    $$ [$Hlocked Hgc Hlow Hhigh Hlogsf Hlogs Hkvf Hkv Hkvintf Hkvint Hgl Hgk]
  · inext
    iapply (storeInv_unfold γs i 1).mpr
    iexists { c with st := { c.st with ints := c.st.ints.insert kb v } }
    iframe
    isplit
    · ipureintro; exact Hok
    · unfold concPers; dsimp only; iexact Hpers
  iapply HΦ

end proof

end Perennial
