/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/InmemStore__GetLog.lean (241f27e).
-/
/-
The proof of `raft.(*InmemStore).GetLog`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.InmemStore__GetLog
public import Dsverify.Proof.github_com.hashicorp.raft.core.Laws

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

theorem github_com.hashicorp.raft.InmemStore.GetLog.wp_proof :
    github_com.hashicorp.raft.InmemStore.GetLog.spec (GF := GF) (hG := hG) :=
  fun γs i idx ptr lv0 tid => by
  wp_start as ⟨#His, Hptr, Htok⟩
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
  -- the linearization point: the contents are `c.L` while the read lock is held
  iapply wp_ncfupd _ _ rfl
  iintro Hnc
  imod HΦ $$ Hnc with ⟨Hnc, HAU⟩
  imod lc_fupd_elim_later (E := ∅) $$ Hlc3 HAU with ⟨%L, HL, Hclose⟩
  ihave %HLeq := inmemLogs_agree γs _ L c.L $$ HL Hgl
  subst HLeq
  imod Hclose $$ HL with HΦ
  imodintro
  iframe Hnc
  wp_auto
  wp_apply (wp_map_lookup2 go.uint64 (go.GoType.PointerType Log.ty) c.mlog c.lm idx
    (DFrac.own sync.rfrac)) $$ [$Hlogs] with Hlogs
  wp_if_destruct
  · -- found
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp Hif
    rw [hp, Option.getD_some]
    ihave Hp2 := Hpers
    iNamed Hp2
    icases Hplogs $$ %idx %p %hp with ⟨%e, %He, Hl⟩
    unfold logPtr
    icases Hl with ⟨%lv, #Hlv, #Hlogis⟩
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
    iapply HΦ $$ [Hptr] [$Htok]
    unfold getLogPost
    rw [He]
    isplit
    · ipureintro; rfl
    · iexists lv; iframe; iframe #
  · -- not found
    unfold errLogNotFoundOk
    icases Herr with ⟨%v, #Hv, %Hvnn⟩
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
    iapply HΦ $$ [Hptr] [$Htok]
    unfold getLogPost
    have hnone : c.L.m.lookup (uint.nat idx) = none := by
      have h := Hok.2.1 idx
      cases hl : c.L.m.lookup (uint.nat idx) with
      | none => rfl
      | some e => exfalso; rw [hl] at h; exact Hif (h.mpr rfl)
    rw [hnone]
    -- the error is `ErrLogNotFound`'s value
    ihave ⟨%e0, #He0⟩ := isRaftErr_of_init (GF := GF) .logNotFound $$ Hinit
    ihave #Hg0 : (globalAddr ErrLogNotFound ↦□ e0 : IProp GF) $$ []
    · have h := isRaftErr_global (GF := GF) .logNotFound e0
      rw [show RaftErr.logNotFound.var = ErrLogNotFound from rfl] at h
      iapply h $$ He0
    icombine Hg0 Hv gives %Hev
    isplitr
    · ipureintro; exact Hvnn
    isplitr
    · iexists .logNotFound; rw [← Hev]; iexact He0
    · iexists lv0; iframe

end proof

end Perennial
