/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/InmemStore__Set.lean (241f27e).
-/
/-
The proof of `raft.(*InmemStore).Set`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.InmemStore__Set
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

theorem github_com.hashicorp.raft.InmemStore.Set.wp_proof :
    github_com.hashicorp.raft.InmemStore.Set.spec (GF := GF) (hG := hG) :=
  fun γs i key vs kb vb => by
  wp_start as ⟨#His, #Hkey, #Hvs⟩
  iNamed His
  wp_auto
  wp_apply (lc := 2) wp_with_defer as %defer Hdefer
  wp_apply (sync.RWMutex.wp_Lock_guard (i.[InmemStore, go!"l"]) (storeInv γs i)) $$ [$Hguard]
    with ⟨Hlocked, HP⟩
  imod lc_fupd_elim_later (E := ⊤) $$ Hlc1 HP with HP
  icases (storeInv_unfold γs i 1).mp $$ HP with
    ⟨%c, Hgc, Hlow, Hhigh, Hlogsf, Hlogs, Hkvf, Hkv, Hkvintf, Hkvint, Hgl, Hgk, %Hok, #Hpers⟩
  wp_apply (wp_bytes_to_string key kb DFrac.discard) $$ [$Hkey] with -
  wp_apply (wp_mapInsert go.string c.mkv c.kvm kb vs) $$ [$Hkv] with Hkv
  iapply wp_ncfupd _ _ rfl
  iintro Hnc
  imod HΦ $$ Hnc with ⟨Hnc, HAU⟩
  imod lc_fupd_elim_later (E := ∅) $$ Hlc2 HAU with ⟨%st, Hkvw, Hclose⟩
  ihave %Hst := kvView_agree γs _ st c.st $$ Hkvw Hgk
  subst Hst
  imod kvView_update γs c.st c.st { c.st with bytes := c.st.bytes.insert kb vb } $$ Hkvw Hgk
    with ⟨Hkvw, Hgk⟩
  imod Hclose $$ Hkvw with HΦ
  imodintro
  iframe Hnc
  imod conc_update γs c { c with st := { c.st with bytes := c.st.bytes.insert kb vb }, kvm := c.kvm.insert kb vs } $$ Hgc with Hgc
  ihave #Hpers' : (concPers (GF := GF) { c with st := { c.st with bytes := c.st.bytes.insert kb vb }, kvm := c.kvm.insert kb vs }) $$ [Hpers]
  · unfold concPers
    iNamed Hpers
    isplitl
    · iexact Hplogs
    · imodintro
      iintro %k %s %Hs
      dsimp only at Hs ⊢
      by_cases hk : k = kb
      · subst hk
        rw [GMap.lookup_insert] at Hs
        cases Hs
        iexists vb
        iframe #
        ipureintro; rw [GMap.lookup_insert]
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk)] at Hs
        icases Hpkv $$ %k %s %Hs with ⟨%vb', %Hvb', Hs'⟩
        iexists vb'
        isplit
        · ipureintro; rw [GMap.lookup_insert_ne _ _ (Ne.symm hk)]; exact Hvb'
        · iexact Hs'
  wp_apply (sync.RWMutex.wp_Unlock_guard (i.[InmemStore, go!"l"]) (storeInv γs i))
    $$ [$Hlocked Hgc Hlow Hhigh Hlogsf Hlogs Hkvf Hkv Hkvintf Hkvint Hgl Hgk]
  · inext
    iapply (storeInv_unfold γs i 1).mpr
    iexists { c with st := { c.st with bytes := c.st.bytes.insert kb vb }, kvm := c.kvm.insert kb vs }
    iframe
    iframe #
    ipureintro
    refine ⟨Hok.1, Hok.2.1, ?_⟩
    intro k
    dsimp only
    by_cases hk : k = kb
    · subst hk; rw [GMap.lookup_insert, GMap.lookup_insert]; rfl
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk), GMap.lookup_insert_ne _ _ (Ne.symm hk)]
      exact Hok.2.2 k
  iapply HΦ

end proof

end Perennial
