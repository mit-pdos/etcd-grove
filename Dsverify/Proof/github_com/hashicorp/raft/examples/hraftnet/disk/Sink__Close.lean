/-
(hraft_robust R3) The proof of `disk.(*Sink).Close` (`snap.go`), as `examples/snapstore`'s.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Sink__Close
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Snaps__persist
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]
variable [dur_sem : github_com.mit_pdos.etcd_grove.examples.lib.durable.Assumptions]

open github_com.hashicorp.raft proto github_com.hashicorp.raft.examples.hraftnet.disk EtcdGrove

set_option goose.wp.extras true

theorem github_com.hashicorp.raft.examples.hraftnet.disk.Sink.Close.wp_proof
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_persist : github_com.hashicorp.raft.examples.hraftnet.disk.Snaps.persist.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.disk.Sink.Close.spec (GF := GF) (hG := hG) :=
  fun k s g Qc Wf id ver idx term cfgIdx cfg o R hQc => by
  wp_start as ⟨#Hcore, Hst, Hc⟩
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  cases o with
  | none =>
    simp only [sinkSt]
    wp_auto
    wp_end
  | some bs =>
    simp only [sinkSt]
    icases Hst with ⟨%sdsl, Hdata, Hsl, Hcap, Hclosed, Hsize⟩
    icases Hc with ⟨HQc, HCm⟩
    iunfold sinkCore at Hcore
    icases Hcore with ⟨#Hst, #Hsn, #Hver, #Hid, #Hidx, #Hterm, #Hpeers, #Hcfg, #HcfgIdx, %Hmnn⟩
    wp_auto
    ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
    have Hsz : sdsl.len = W64 (bs.length : Int) := by word
    have hb : bs.length < 2 ^ 63 := by have := Hlen.1; have := Hlen.2; word
    rw [Hsz]
    ipersist Hsize
    ihave #Hmeta : (k.[Sink, go!"meta"] ↦□ sinkMeta ver idx term cfgIdx cfg id bs) $$ []
    · iapply typedPointsto_combine _ _ _ Hmnn
      simp only [TypedPointsto.typedPointstoDef, sinkMeta]
      iframe #
    ihave #Hsn2 := Hsn
    iunfold isSnaps at Hsn2
    icases Hsn2 with ⟨%mu, #Hpkg, #Hmu, #Hisl, #Hfile, #Hinv, #Hdinv, #Hos, #Hsh, %Hf⟩
    wp_auto
    wp_apply (lc := 2) wp_Lock $$ [$Hisl] as ⟨Hlocked, HR⟩
    iunfold snapsLockInv at HR
    icases HR with ⟨%lat, %lt, %nid, %has, %mv, %dt, %qc, Hmem, %Hmv, #Hr, Hrec, Hdh, Hcp⟩
    icases snapMem_view s nid lt has mv dt lat Hmv $$ [$Hmem $Hr] with ⟨Hmem, #Hcell⟩
    icases snapsMemAt_open s nid lt has mv dt $$ Hmem with ⟨Hhas, Hsmeta, Hsdata, Hnid, Hm⟩
    ihave %HcP := latCell_pure lat has mv dt $$ Hcell
    wp_auto
    wp_bind (If (If (Val _) (Val #true) _) (Val #true) _)
    iapply (wp_wand_r (Φ := fun v => iprop(⌜v = #(closeNewer has mv.Term' mv.Index' term idx)⌝ ∗
        s.[Snaps, go!"has"] ↦ has ∗ s.[Snaps, go!"meta"] ↦ mv ∗ k_ptr ↦ k ∗ s_ptr ↦ s)))
    isplitl [Hhas Hsmeta k s]
    · cases has
      · wp_auto
        iframe; ipureintro; simp [closeNewer]
      · wp_auto
        wp_if_destruct
        · iframe; ipureintro; simp [closeNewer, Hif]
        · wp_if_destruct
          · try wp_auto
            iframe; ipureintro; simp [closeNewer]
          · iframe; ipureintro; simp [closeNewer, *]
    iintro %v ⟨%Hv, Hhas, Hsmeta, k, s⟩
    subst Hv
    cases hc : closeNewer has mv.Term' mv.Index' term idx
    · -- an older snapshot: the commit runs at once
      have hkeep : newerSnap lat (sinkMeta ver idx term cfgIdx cfg id bs) bs = lat :=
        closeNewer_keepSnap lat has mv _ bs HcP hc
      wp_auto
      iapply wp_ncfupd _ _ rfl
      iintro Hnc
      iunfold snapCommitAU at HCm
      imod (snapCommitKeep g Qc Wf lat lt (sinkMeta ver idx term cfgIdx cfg id bs) bs R hkeep)
        $$ Hinv Hrec Hlc1 Hlc2 HQc HCm Hnc with ⟨Hnc, Hrec, HR⟩
      imodintro
      iframe Hnc
      wp_apply wp_Unlock $$ [$Hisl $Hlocked Hhas Hsmeta Hsdata Hnid Hm Hrec Hdh Hcp]
      · inext; iunfold snapsLockInv; iexists lat, lt, nid, has, mv, dt, qc
        iframe Hrec Hdh Hcp; iframe #; isplitl [Hhas Hsmeta Hsdata Hnid Hm]
        · iapply snapsMemAt_close; iframe
        ipureintro; exact Hmv
      iapply HΦ; iframe
    · -- newer: the latest, written to the file
      have hnew : newerSnap lat (sinkMeta ver idx term cfgIdx cfg id bs) bs =
          some (sinkMeta ver idx term cfgIdx cfg id bs, bs) :=
        closeNewer_newerSnap lat has mv _ bs HcP hc
      wp_auto
      ihave >#Hsl := ownSlice_persist sdsl _ _ $$ Hsl
      icases hQc _ _ $$ HQc with ⟨⟨%svs, #Hsvs⟩, HQc⟩
      ihave #Hmr := sink_metaRep ver idx term cfgIdx cfg id bs svs $$ Hsvs
      ihave Hmem : snapsMemAt s ⟨nid, some (sinkSMeta ver idx term cfgIdx id svs, bs)⟩ true
          (sinkMeta ver idx term cfgIdx cfg id bs) sdsl $$ [Hhas Hsmeta Hsdata Hnid]
      · iapply snapsMemAt_close; iframe; simp only [snapTail]; iframe #
      wp_bind (App (Val #(methods (go.GoType.PointerType Snaps.ty) go!"persist" #s)) (Val #()))
      iapply (wp_persist g s ⟨nid, some (sinkSMeta ver idx term cfgIdx id svs, bs)⟩ true
        (sinkMeta ver idx term cfgIdx cfg id bs) sdsl qc) $$ Hpkg Hfile [] Hos Hsh Hdinv Hmem Hdh Hcp
      · ipureintro; exact Hf
      iapply (snapWriteAU g Qc Wf lat lt (sinkMeta ver idx term cfgIdx cfg id bs) bs
        (sinkSMeta ver idx term cfgIdx id svs) nid _ hnew hb) $$ Hinv Hrec Hmr HQc
      iintro Hrec Hdh Hcp Hmem
      wp_auto
      iapply wp_ncfupd _ _ rfl
      iintro Hnc
      iunfold snapCommitAU at HCm
      imod (snapCommit g Qc Wf lat lt (sinkMeta ver idx term cfgIdx cfg id bs) bs
        (sinkSMeta ver idx term cfgIdx id svs) nid R) $$ Hinv Hrec Hlc1 Hlc2 HCm Hnc with ⟨Hnc, Hrec, HR⟩
      imodintro
      iframe Hnc
      wp_apply wp_Unlock $$ [$Hisl $Hlocked Hmem Hrec Hdh Hcp]
      · inext; iunfold snapsLockInv
        iexists some (sinkMeta ver idx term cfgIdx cfg id bs, bs), some (sinkSMeta ver idx term cfgIdx id svs, bs),
          nid, true, sinkMeta ver idx term cfgIdx cfg id bs, sdsl, qc
        iframe Hmem Hrec Hdh Hcp
        simp only [latRep, latMv]
        iframe #
      iapply HΦ; iframe


end proof

end Perennial
