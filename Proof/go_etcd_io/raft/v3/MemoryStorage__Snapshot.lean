/-
`MemoryStorage.Snapshot` (`storage.go:207`; U8 v2 step 3): under the lock, the snapshot taken out of
its home with the lock's key (`memSnap_take`), ensured, cloned, and put back (`memSnap_put`). The
clone's index is at or past `c`: `memCompacted` is below the lock's compaction point, which `MemOk`
puts at or below the stored snapshot's index (the home's quarter agrees with the lock's).
-/
module

public import Spec.go_etcd_io.raft.v3.MemoryStorage__Snapshot
public import Spec.go_etcd_io.raft.v3.raftpb.EnsureSnapshot
public import Spec.google_golang_org.protobuf.proto.CloneSnapshot
public import Proof.go_etcd_io.raft.v3.InvMemstorageAt

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem MemoryStorage.Snapshot.wp_proof
    (wp_EnsureSnapshot : raftpb.EnsureSnapshot.spec (GF := GF) (hG := hG))
    (wp_CloneSnapshot : proto.CloneSnapshot.spec (GF := GF) (hG := hG)) :
    MemoryStorage.Snapshot.spec (GF := GF) (hG := hG) := by
  have HN : ↑memStorN ⊆ (⊤ : CoPset) := CoPset.subseteq_top
  intro ms γs J o c bb esu
  wp_start as ⟨Hat, #Hc, Hnone, #Hesu⟩
  icases memStorAt_split ms γs J o emp $$ Hat with ⟨#Hlock, Hjc, Hho⟩
  iunfold memStorLock at Hlock
  icases Hlock with ⟨#Hinit, #Hmu⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold memstorageInv at Hinv
  icases Hinv with ⟨%p, %ents, %M, %sv, Hinv⟩
  iNamedSuffix Hinv "_inv"
  -- `c` is at most the compaction point
  ihave %Hcp : ⌜c ≤ uint.nat p.index'⌝ $$ [Hcp_inv]
  · iunfold memCompacted at Hc
    icases Hc with (%H | ⟨#Hlb, -⟩)
    · ipureintro; omega
    icases monoNatLbOwn_valid _ _ _ _ $$ Hcp_inv Hlb with %H
    ipureintro; exact H.2
  imod memSnap_take_at ms γs J o emp ⊤ HN $$ Hjc Hho Hlk_inv with ⟨Hjc, Hlko, Hhome⟩
  iunfold memstorageFields at Hfields_inv
  icases Hfields_inv with ⟨%hp, %es, %dummy, %nfi, %nli, %nen, %nte, %nsn, Hfields_inv⟩
  iNamed Hfields_inv
  wp_auto
  iunfold memSnapHomeAt at Hhome
  icases Hhome with ⟨Hhk, %sp, %sv', Hsnapshot, Hsnap, Hsxh, #Hval⟩
  icases ghostVar_agree γs.sx _ _ _ _ $$ Hsx_inv Hsxh with %Hag
  subst Hag
  icases memSnapNone_empty γs bb sv $$ [$Hnone $Hsn_inv] with ⟨Hnone, %Hbe⟩
  wp_auto
  wp_apply wp_EnsureSnapshot.1 sp (some sv) $$ [Hsnap] as %r ⟨Hr, -⟩
  · simp only [snapOpt]; iexact Hsnap
  ihave Hr := ownSnapS_W _ _ _ $$ Hr
  simp only [Option.getD_some]
  wp_apply wp_CloneSnapshot.2.2.1 r (DFrac.own 1) sv $$ [Hr] as %p' ⟨Hr, Hp'⟩
  · iframe Hr
  ihave Hr := ownSnapW_E $$ Hr
  ihave Hr := ownSnapE_weaken $$ Hr
  imod memSnap_put_at ms γs J o emp ⊤ HN sv r $$ Hjc Hlko Hhk Hsnapshot Hr Hsxh [] with
    ⟨Hjc, Hlk, Hho⟩
  · iapply memValAt_new $$ Hval
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HhardState Hents_f Hents Hents_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot Hlog_inv Hen_inv Hcp_inv Hsx_inv Hsl_inv Hlk]
  · unfold memstorageInv
    iexists p, ents, M, sv
    simp only [named]
    iframe # ∗
    isplitl
    · unfold memstorageFields
      iexists hp, es, dummy, _, _, _, _, _
      simp only [named]
      iframe
      ipureintro; exact Hdummy
    ipureintro; exact Hok_inv
  iapply HΦ
  iframe Hnone
  isplitr
  · ipureintro; rfl
  iexists sv
  iframe Hp'
  isplitr
  · ipureintro
    have := Hok_inv.2.2.2.1
    exact ⟨by omega, Hbe⟩
  cases o with
  | none =>
    simp only [memValAt]
    iexact Hval
  | some p =>
    obtain ⟨c0, sv0⟩ := p
    simp only [memValAt]
    icases Hval with %Hsv
    subst Hsv
    isplitr
    · ipureintro; rfl
    iapply memStorFresh_of_at ms γs J emp c0 sv c0 sv
    simp only [memSetAt, Option.map_some] at *
    iframe Hjc Hho

end proof

end EtcdGrove
end Perennial
