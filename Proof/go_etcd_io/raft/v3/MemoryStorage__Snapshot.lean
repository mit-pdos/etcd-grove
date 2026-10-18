/-
Port of election_proof/proof_MemoryStorage__Snapshot.v. D17d (2026-10-18): the snapshot under the
lock (`memSnapInv`), taken out with the lock's key and the owner's (raft's triple) or the
application's (the application's triple).
-/
module

public import Spec.go_etcd_io.raft.v3.MemoryStorage__Snapshot
public import Spec.go_etcd_io.raft.v3.raftpb.EnsureSnapshot
public import Spec.google_golang_org.protobuf.proto.CloneSnapshot

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem MemoryStorage.Snapshot.wp_proof
    (wp_EnsureSnapshot : raftpb.EnsureSnapshot.spec (GF := GF) (hG := hG))
    (wp_CloneSnapshot : proto.CloneSnapshot.spec (GF := GF) (hG := hG)) :
    MemoryStorage.Snapshot.spec (GF := GF) (hG := hG) := by
  have HN : ↑memSnapN ⊆ (⊤ : CoPset) := CoPset.subseteq_top
  constructor
  · -- raft's: the lock's key and the owner's
    intro ms γs σ esu n
    wp_start as ⟨Hms, #Hesu, #Hn⟩
    iunfold ownMemoryStorage at Hms
    icases Hms with ⟨#Hinit, #Hmu, Hview, Hsn, %Hbounded⟩
    iunfold memSnapShare at Hsn
    icases Hsn with ⟨#Hsinv, Hok⟩
    wp_apply wp_with_defer as %defer defer
    ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
    · iPkgInit
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
    iunfold memstorageInv at Hinv
    icases Hinv with ⟨%σ0, %c, Hinv⟩
    iNamedSuffix Hinv "_inv"
    -- (D19i part 1) the contents, the cut, the snapshot as the lock relates them
    icases memCut_view γs σ σ0 c $$ Hview Hgs_inv Hcut_inv
      with ⟨%Hvc, -, Hview, Hgs_inv, Hcut_inv⟩
    obtain ⟨Hvw, -, -⟩ := Hvc
    icases memView_pend γs σ $$ Hview with ⟨%Hpend, Hview⟩
    iunfold memCutInv at Hcut_inv
    iNamed Hcut_inv
    ihave %Hnc : ⌜n ≤ 0 ∨ n ≤ uint.Z c.index'⌝ $$ [Hbd]
    · icases Hn with (%Hn | #Hn)
      · ipureintro; left; exact Hn
      · iunfold memStorCut at Hn
        icases monoNatLbOwn_valid _ _ _ _ $$ Hbd Hn with %H
        obtain ⟨-, H⟩ := H
        have := (word.unsigned_range c.index').1
        ipureintro
        by_cases hn : n ≤ 0
        · left; exact hn
        · right; omega
    ihave %Hrel : ⌜(S.ss = σ0.ss ∧ S.scs = σ0.scs ∧ S.sal = σ0.sal) ∨
        (uint.Z σ0.ss.index' < uint.Z S.ss.index' ∧ uint.Z σ0.prev.index' ≤ uint.Z S.ss.index' ∧
          termAt σ0.prev σ0.ents S.ss.index' = some S.ss.term' ∧
          uint.Z S.ss.index' ≤ uint.Z σ.fl)⌝ $$ [Hview]
    · icases Hsrel with (%Hs | ⟨%Hs, #Hfl⟩)
      · ipureintro; left; exact Hs
      · icases memFlLb_view γs σ S.ss.index' $$ Hview Hfl with ⟨%H, -⟩
        ipureintro; right; exact ⟨Hs.1, Hs.2.1, Hs.2.2, H⟩
    icases memInvGhost_key $$ Hgs_inv with ⟨Hlk, Hgs_back⟩
    imod memSnap_take ms γs 1 ⊤ HN $$ Hsinv [Hlk Hok] with ⟨Hhome, Hrcpt⟩
    · iunfold memSnapKeys; ileft; iframe; ipureintro; rfl
    iunfold memstorageFields at Hfields_inv
    icases Hfields_inv with ⟨%hp, %es, %dummy, %nfi, %nli, %nen, %nte, %nsn, Hfields_inv⟩
    iNamed Hfields_inv
    wp_auto
    iunfold memSnapHome at Hhome
    icases Hhome with ⟨%σp, Hown, Hsnh⟩
    icases ghostVar_agree γs.sn _ _ _ _ $$ Hsq Hsnh with %Hag
    obtain ⟨Hs1, Hs2, Hs3⟩ := snapPart_inj Hag
    iunfold memSnapOwn at Hown
    icases Hown with ⟨%sp, %sv, Hsnapshot, Hsnap, %Hsnap_id⟩
    wp_auto
    wp_apply wp_EnsureSnapshot sp (some sv) $$ [Hsnap] as %r ⟨Hr, -⟩
    · simp only [snapOpt]; iexact Hsnap
    ihave Hr := ownSnapW_E $$ Hr
    ihave Hr := ownSnapE_weaken $$ Hr
    simp only [Option.getD_some]
    wp_apply wp_CloneSnapshot.1 r (DFrac.own 1) sv $$ [Hr] as %p' ⟨Hr, Hp'⟩
    · iframe Hr
    imod memSnap_put ms γs 1 σp ⊤ HN $$ Hsinv Hrcpt [Hsnapshot Hr] Hsnh with Hk
    · iunfold memSnapOwn
      iexists r, sv
      iframe
      ipureintro; exact Hsnap_id
    iunfold memSnapKeys at Hk
    icases Hk with (⟨-, Hlk, Hok⟩ | ⟨%Hk, -⟩ | ⟨%Hk, -⟩)
    rotate_left
    · exact absurd Hk (by decide)
    · exact absurd Hk (by decide)
    ihave Hgs_inv := Hgs_back $$ Hlk
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hgs_inv HhardState Hents_f Hents Hents_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot Hcb Hbd Hsq]
    · inext
      unfold memstorageInv memstorageFields
      iexists σ0, c
      iframe Hgs_inv
      isplitl [HhardState Hents_f Hents Hents_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot]
      · iexists hp, es, dummy, _, _, _, _, _
        iframe # ∗
        ipureintro; exact Hdummy
      isplitr
      · ipureintro; exact Hpb_inv
      iunfold memCutInv
      iexists S
      iframe Hcb Hbd Hcfl Hsq Hsrel
      ipureintro; exact Hcok
    iapply HΦ
    isplitl [Hview Hok]
    · unfold ownMemoryStorage memSnapShare
      simp only [named]
      iframe # ∗
      ipureintro; exact Hbounded
    iright
    isplitr
    · ipureintro; rfl
    iexists sv
    iframe Hp'
    ipureintro
    have Hsid : snapId sv = S.ss := Hsnap_id.1.trans Hs1.symm
    have Hidx : sv.Metadata'.Index' = S.ss.index' := by rw [← Hsid]; rfl
    have Htm : sv.Metadata'.Term' = S.ss.term' := by rw [← Hsid]; rfl
    obtain ⟨Hvp, ⟨Hvs1, Hvs2, Hvs3⟩, Hve, Hvi⟩ := Hvw
    have := (word.unsigned_range σ.prev.index').1
    have Hcp := Hcok.1.1
    have HcS := Hcok.2
    refine ⟨fun h => ?_, ?_⟩
    · rw [Hidx]
      rcases h with h | h
      · rw [Hvp] at Hcp
        have : uint.Z σ.prev.index' ≠ 0 := fun hz => h (by word)
        intro hz; rw [hz] at HcS; have : uint.Z (W64 0) = 0 := rfl; omega
      · intro hz; rw [hz] at HcS; have : uint.Z (W64 0) = 0 := rfl; omega
    rcases Hrel with ⟨Hr1, Hr2, Hr3⟩ | ⟨Hr1, Hr2, Hr3, Hr4⟩
    · left
      refine ⟨Hsid.trans (Hr1.trans Hvs1), ?_, ?_⟩
      · rw [Hsnap_id.2.2, ← Hs3, Hr3, Hvs3]
      · rw [Hsnap_id.2.1, ← Hs2, Hr2, Hvs2]
    · right
      rw [Hidx, Htm, ← Hvs1, ← Hvp]
      refine ⟨Hr1, Hr2, Hr4, ?_⟩
      rw [Hvp]
      exact memView_termAt_below σ σ0 ⟨Hvp, ⟨Hvs1, Hvs2, Hvs3⟩, Hve, Hvi⟩
        Hpend.1 Hpend.2 _ _ Hr3 Hr4 (by rw [← Hvp]; exact Hr2)
  · -- the application's: the lock's key and the application's
    intro ms γs σ
    wp_start as Htok
    iunfold memSnapTok at Htok
    icases Htok with ⟨#Hinit, #Hmu, #Hsinv, Hak, Hsv, Hcbt⟩
    wp_apply wp_with_defer as %defer defer
    ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
    · iPkgInit
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
    iunfold memstorageInv at Hinv
    icases Hinv with ⟨%σ0, %c, Hinv⟩
    iNamedSuffix Hinv "_inv"
    icases memInvGhost_key $$ Hgs_inv with ⟨Hlk, Hgs_back⟩
    imod memSnap_take ms γs 2 ⊤ HN $$ Hsinv [Hlk Hak] with ⟨Hhome, Hrcpt⟩
    · iunfold memSnapKeys; iright; ileft; iframe; ipureintro; rfl
    iunfold memstorageFields at Hfields_inv
    icases Hfields_inv with ⟨%hp, %es, %dummy, %nfi, %nli, %nen, %nte, %nsn, Hfields_inv⟩
    iNamed Hfields_inv
    wp_auto
    iunfold memSnapHome at Hhome
    icases Hhome with ⟨%σp, Hown, Hsnh⟩
    icases ghostVar_agree γs.sn _ _ _ _ $$ Hsv Hsnh with %Hag
    obtain ⟨Hs1, Hs2, Hs3⟩ := snapPart_inj Hag
    iunfold memSnapOwn at Hown
    icases Hown with ⟨%sp, %sv, Hsnapshot, Hsnap, %Hsnap_id⟩
    wp_auto
    wp_apply wp_EnsureSnapshot sp (some sv) $$ [Hsnap] as %r ⟨Hr, -⟩
    · simp only [snapOpt]; iexact Hsnap
    simp only [Option.getD_some]
    wp_apply wp_CloneSnapshot.2.2 r (DFrac.own 1) sv $$ [Hr] as %p' ⟨Hr, Hp'⟩
    · iframe Hr
    ihave Hr := ownSnapW_E $$ Hr
    ihave Hr := ownSnapE_weaken $$ Hr
    imod memSnap_put ms γs 2 σp ⊤ HN $$ Hsinv Hrcpt [Hsnapshot Hr] Hsnh with Hk
    · iunfold memSnapOwn
      iexists r, sv
      iframe
      ipureintro; exact Hsnap_id
    iunfold memSnapKeys at Hk
    icases Hk with (⟨%Hk, -⟩ | ⟨-, Hlk, Hak⟩ | ⟨%Hk, -⟩)
    · exact absurd Hk (by decide)
    rotate_left
    · exact absurd Hk (by decide)
    ihave Hgs_inv := Hgs_back $$ Hlk
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hgs_inv HhardState Hents_f Hents Hents_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot Hcut_inv]
    · inext
      unfold memstorageInv memstorageFields
      iexists σ0, c
      iframe Hgs_inv Hcut_inv
      isplitl
      · iexists hp, es, dummy, _, _, _, _, _
        iframe # ∗
        ipureintro; exact Hdummy
      ipureintro; exact Hpb_inv
    iapply HΦ
    isplitl [Hak Hsv Hcbt]
    · unfold memSnapTok
      simp only [named]
      iframe # ∗
    iexists sv
    iframe Hp'
    ipureintro
    exact ⟨Hsnap_id.1.trans Hs1.symm, Hsnap_id.2.2.trans Hs3.symm, Hsnap_id.2.1.trans Hs2.symm⟩

end proof

end EtcdGrove
end Perennial
