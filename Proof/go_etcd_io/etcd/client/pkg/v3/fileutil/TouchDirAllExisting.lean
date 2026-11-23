/-
`fileutil.TouchDirAll` of an existing directory: the proof of
`Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/TouchDirAllExisting.lean` (claim #34, 2026-11-23), over its
callees' specs (`Exist`, `CheckDirPermission`, `zap.Error`, `Logger.Warn`, `filepath`'s `Clean`/`Dir`,
`syncDir` and its above-root form, `os.Stat` above the roots, `IsDirWriteable`) and `os.MkdirAll` of an
existing directory (`os.MkdirAll.wp_spineS`, over `os`'s model). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.TouchDirAllExisting
public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.CheckDirPermission
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Warn
public import Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.TouchDirAllLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Fs WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
variable [os_sem : os.Assumptions] [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions]

theorem fileutil.TouchDirAll.wp_proofExisting
    (wp_Exist : go_etcd_io.etcd.client.pkg.v3.fileutil.Exist.spec (GF := GF) (hG := hG))
    (wp_Clean : filepath.Clean.spec (GF := GF) (hG := hG))
    (wp_Dir : filepath.Dir.spec (GF := GF) (hG := hG))
    (wp_CheckDirPermission : go_etcd_io.etcd.client.pkg.v3.fileutil.CheckDirPermission.spec (GF := GF)
      (hG := hG))
    (wp_ZError : zap.Error.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (wp_IsDirWriteable : go_etcd_io.etcd.client.pkg.v3.fileutil.IsDirWriteable.spec (GF := GF) (hG := hG))
    (hSync : go_etcd_io.etcd.client.pkg.v3.fileutil.syncDir.spec (GF := GF) (hG := hG))
    (hSyncAbove : go_etcd_io.etcd.client.pkg.v3.fileutil.syncDir.specAboveRoot (GF := GF) (hG := hG))
    (hStatAbove : os.Stat.specAboveRoot (GF := GF) (hG := hG)) :
    fileutil.TouchDirAll.specExisting (GF := GF) := by
  intro lg R J d dq qc hJ hlen htouch
  wp_start as ⟨#Hlg, #Hinv, #Hsi, #Hab, Hp, Hperm, Hn⟩
  wp_auto
  ihave %hlgnn := zapLoggerOk_ne_null lg $$ Hlg
  simp only [hlgnn, decide_false, Bool.not_false]
  wp_apply wp_verifyAssert_true as -
  icases osPathS_cleanAbs_keep R d dq J $$ Hp with ⟨Hp, %hclean⟩
  have hEx := wp_Exist d
    iprop(osInv ∗ osSharedInv R ∗ osPathS R d dq J ∗ osCallPerm (callKey R d) qc)
    (fun _ => iprop(osPathS R d dq J ∗ osCallPerm (callKey R d) qc))
    (by
      iintro %Φ' Hpre HΦ'
      wp_apply os.Stat.wp_dirS d R J dq qc $$ Hpre as %fi %err ⟨Hp, Hperm, -⟩
      iapply HΦ'
      iframe)
  wp_apply hEx $$ [Hp Hperm] as %b ⟨%err0, %hb, Hp, Hperm⟩
  · iframe; isplitl [] <;> iassumption
  clear hEx hb
  iunfold osPathS at Hp
  icases Hp with ⟨%r, %j0, %cs, %hpp, Hs⟩
  obtain ⟨hR, hm, hcs, hd⟩ := hpp
  obtain ⟨rcs, hrcs, hrcsok, hr⟩ := (hR.2.2 _ hm).1
  subst hr hd
  have hkey : callKey R (joinPath (joinPath [] rcs) cs) = callKey R (joinPath [] rcs) :=
    callKey_joinPath hR hm cs
  obtain ⟨full, hfull⟩ : ∃ full, full = rcs ++ cs := ⟨_, rfl⟩
  have hfok : ∀ c ∈ full, NameOk c := by
    intro c hc
    subst hfull
    rcases List.mem_append.1 hc with hc | hc
    · exact hrcsok c hc
    · exact hcs c hc
  have hfne : full ≠ [] := by subst hfull; simp [hrcs]
  have hdfull : joinPath (joinPath [] rcs) cs = os.ancPath full := by
    rw [joinPath_joinPath, ancPath_ne hfne, hfull]
  have hcl : path.cleanModel (joinPath (joinPath [] rcs) cs) = joinPath (joinPath [] rcs) cs :=
    filepath.cleanModel_cleanAbs _ hclean
  cases b
  · wp_auto
    wp_apply wp_Clean
    iintro %cl %hcl'
    rw [hcl] at hcl'
    subst hcl'
    rw [hdfull]
    have hkey' : callKey R (os.ancPath full) = callKey R (joinPath [] rcs) := hdfull ▸ hkey
    ihave Hperm := osCallPerm_congr _ hkey' $$ Hperm
    wp_auto
    ihave IH : iprop(∃ (k : Nat) (sl : GoSlice),
        "d" ∷ d_ptr ↦ os.ancPath (full.take k) ∗ "created" ∷ created_ptr ↦ sl ∗
        "Hsl" ∷ sl ↦* touchC full (k + 1) ∗ "Hs" ∷ osSpine j0 cs dq J ∗
        "Hperm" ∷ osCallPerm (callKey R (joinPath [] rcs)) qc ∗
        "%hk" ∷ ⌜k ≤ full.length⌝) $$ [d created Hs Hperm]
    · iexists full.length, slice.nil
      rw [List.take_length, touchC_end]
      iframe
      isplitl []
      · iapply ownSlice_nil
      ipureintro; exact Nat.le_refl _
    wp_join iprop(∃ (j : Nat) (sl : GoSlice), created_ptr ↦ sl ∗ sl ↦* touchC full j ∗
        osSpine j0 cs dq J ∗ osCallPerm (callKey R (joinPath [] rcs)) qc ∗ ⌜j ≤ full.length + 1⌝)
      at (App (App (App (Val doFor) _) _) _) with [IH] as ⟨%j, %sl, created, Hsl, Hs, Hperm, %hj⟩
    · wp_for IH
      subst hfull
      wp_apply wp_Exist _ _ _ (wp_statAnc hStatAbove R rcs cs j0 J dq qc k hR hm hrcs hcs hk)
        $$ [Hs Hperm] as %b ⟨%err, %hb, Hs, Hperm⟩
      · iframe; isplitl [] <;> iassumption
      cases b with
      | true =>
        simp only [Bool.not_true]
        rw [if_neg (by simp only [decide_eq_true_eq]; intro h; exact Bool.false_ne_true (go.intoVal_inj h)),
          if_pos (by simp)]
        isplitr
        · itrivial
        iexists k + 1, sl
        iframe
        ipureintro; omega
      | false =>
        simp only [Bool.not_false]
        rw [if_pos (by simp)]
        wp_auto
        wp_apply wp_slice_literal (V := GoString) [os.ancPath ((rcs ++ cs).take k)]
        isplitr
        · ipureintro; rfl
        iintro %jsl ⟨Hjsl, Hcap⟩
        wp_auto
        wp_apply wp_slice_append _ [os.ancPath ((rcs ++ cs).take k)] sl (touchC (rcs ++ cs) (k + 1))
          (DFrac.own 1) $$ [Hjsl Hcap Hsl] as %s' ⟨Hs', -, -⟩
        · iframe
        rw [List.singleton_append, ← touchC_cons (rcs ++ cs) k hk]
        wp_apply wp_Dir (os.ancPath ((rcs ++ cs).take k))
        iintro %dr %hdr
        rw [dir_take (rcs ++ cs) hfok k hk] at hdr
        subst hdr
        wp_auto
        by_cases hk0 : k = 0
        · subst hk0
          rw [decide_eq_true (by rfl)]
          wp_auto
          iapply wp_for_post_break
          isplitr
          · ipureintro; rfl
          iexists 0, s'
          iframe
          ipureintro; omega
        · have hne := dir_take_ne (rcs ++ cs) hfok k (by omega) hk
          rw [dir_take (rcs ++ cs) hfok k hk] at hne
          rw [decide_eq_false hne]
          wp_auto
          wp_for_post
          wp_apply wp_Dir (os.ancPath ((rcs ++ cs).take k))
          iintro %dr %hdr
          rw [dir_take (rcs ++ cs) hfok k hk] at hdr
          subst hdr
          wp_auto
          iexists k - 1, s'
          rw [show k - 1 + 1 = k by omega]
          iframe
          ipureintro; omega
    rw [← hdfull]
    try wp_auto
    rw [show (os.MkdirAll : GoString) = go!"os.MkdirAll" from rfl]
    wp_apply os.MkdirAll.wp_spineS (joinPath [] rcs) j0 _ R dq qc hR hm cs J hcs $$ [Hs Hperm]
      as %err ⟨Hs, Hperm⟩
    · iframe; isplitl [] <;> iassumption
    cases err with
    | ok e =>
      wp_auto
      iapply HΦ
      ihave Hperm := osCallPerm_congr _ hkey.symm $$ Hperm
      ihave Hp := (os.osPathS_joinPath R (joinPath [] rcs) j0 cs dq J hR hm hcs).2 $$ Hs
      iframe
      isplitl []
      · ileft; ipureintro; exact htouch
      ipureintro; intro hc; cases hc
    | nil =>
    imod osNames_next R J _ _ hJ CoPset.subseteq_top $$ Hsi Hn with ⟨Hn, #Hlb⟩
    ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
    have hCl := touchC_length full j
    wp_auto
    ihave IH : iprop(∃ (i : w64) (dv : GoString),
        "i" ∷ i_ptr ↦ i ∗ "d" ∷ d_ptr ↦ dv ∗ "err" ∷ err_ptr ↦ GoInterface.nil ∗
        "Hs" ∷ osSpine j0 cs dq J ∗ "Hperm" ∷ osCallPerm (callKey R (joinPath [] rcs)) qc ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ (touchC full j).length⌝) $$ [i d err Hs Hperm]
    · iexists W64 0, _
      iframe
      ipureintro
      refine ⟨by decide, ?_⟩
      rw [show sint.nat (W64 0) = 0 from rfl]; omega
    wp_for IH
    obtain ⟨hi0, hil⟩ := Hi
    wp_if_destruct
    · have Hlt : sint.nat i < (touchC full j).length := by rw [Hlen.1]; word
      have Hbnd : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len := ⟨hi0, Hif⟩
      simp only [Hbnd, _root_.and_self, ↓reduceIte]
      have He : (touchC full j)[(sint.Z i).toNat]? = some (os.ancPath (full.take (j + sint.nat i))) := by
        rw [show (sint.Z i).toNat = sint.nat i by word, List.getElem?_eq_getElem Hlt, touchC_get]
      have hji : j + sint.nat i ≤ full.length := by omega
      wp_apply wp_load_slice_index sl (sint.Z i) _ (DFrac.own 1) _ hi0 $$ [Hsl] as Hsl
      · iframe; ipureintro; exact He
      wp_apply wp_Dir (os.ancPath (full.take (j + sint.nat i)))
      iintro %dr %hdr
      rw [dir_take full hfok _ hji] at hdr
      subst hdr
      have hk' : j + sint.nat i - 1 ≤ (rcs ++ cs).length := by subst hfull; omega
      rw [hfull]
      wp_apply wp_syncDirAnc hSync hSyncAbove R rcs cs j0 J dq qc hJ.next (j + sint.nat i - 1)
        hR hm hrcs hcs hk' $$ [Hs Hperm] as %e ⟨Hs, Hperm, -⟩
      · iframe; iframe #
      rw [← hfull]
      cases e with
      | ok e =>
        wp_auto
        wp_for_post
        iapply HΦ
        ihave Hperm := osCallPerm_congr _ hkey.symm $$ Hperm
        ihave Hp := (os.osPathS_joinPath R (joinPath [] rcs) j0 cs dq J hR hm hcs).2 $$ Hs
        iframe
        isplitl []
        · ileft; ipureintro; exact htouch
        ipureintro; intro hc; cases hc
      | nil =>
        wp_auto
        wp_for_post
        iframe
        iexists i + W64 1, _
        iframe
        have hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
        rw [hi1]
        ipureintro
        refine ⟨by word, by omega⟩
    · ihave Hperm := osCallPerm_congr _ hkey.symm $$ Hperm
      ihave Hp := (os.osPathS_joinPath R (joinPath [] rcs) j0 cs dq J hR hm hcs).2 $$ Hs
      try wp_auto
      wp_apply wp_IsDirWriteable _ R J dq hJ qc hlen htouch $$ [Hp Hperm Hn]
      · iframe; isplitl [] <;> iassumption
      iintro %err Hr
      wp_auto
      iapply HΦ $$ Hr
  · wp_auto
    ihave Hp := (os.osPathS_joinPath R (joinPath [] rcs) j0 cs dq J hR hm hcs).2 $$ Hs
    wp_apply wp_CheckDirPermission _ _ R J dq qc $$ [Hp Hperm] as %err1 ⟨Hp, Hperm⟩
    · iframe; isplitl [] <;> iassumption
    try wp_auto
    wp_join at next with [err lg]
    · cases err1 with
      | nil => wp_auto; wp_join_done
      | ok e1 =>
      wp_auto
      wp_apply wp_ZError _ as %f -
      try wp_auto
      wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f]
      isplitr
      · ipureintro; rfl
      iintro %fsl ⟨-, -⟩
      wp_auto
      wp_apply wp_Warn
      · iexact Hlg
      wp_join_done
    wp_apply wp_Clean
    iintro %c %hc
    rw [hc, hcl]
    wp_apply wp_Dir
    iintro %dr %hdr
    rw [hdfull] at hdr
    rw [show os.ancPath full = os.ancPath (full.take full.length) by rw [List.take_length]] at hdr
    rw [dir_take full hfok _ (Nat.le_refl _)] at hdr
    subst hdr
    imod osNames_next R J _ _ hJ CoPset.subseteq_top $$ Hsi Hn with ⟨Hn, #Hlb⟩
    icases (os.osPathS_joinPath R (joinPath [] rcs) j0 cs dq J hR hm hcs).1 $$ Hp with Hs
    ihave Hperm := osCallPerm_congr _ hkey $$ Hperm
    subst hfull
    wp_apply wp_syncDirAnc hSync hSyncAbove R rcs cs j0 J dq qc hJ.next ((rcs ++ cs).length - 1)
      hR hm hrcs hcs (by omega) $$ [Hs Hperm] as %e ⟨Hs, Hperm, -⟩
    · iframe; iframe #
    ihave Hperm := osCallPerm_congr _ hkey.symm $$ Hperm
    ihave Hp := (os.osPathS_joinPath R (joinPath [] rcs) j0 cs dq J hR hm hcs).2 $$ Hs
    cases e with
    | ok e =>
      wp_auto
      iapply HΦ
      iframe
      isplitl []
      · ileft; ipureintro; exact htouch
      ipureintro; intro hc; cases hc
    | nil =>
      wp_auto
      wp_apply wp_IsDirWriteable _ R J dq hJ qc hlen htouch $$ [Hp Hperm Hn]
      · iframe; isplitl [] <;> iassumption
      iintro %err Hr
      wp_auto
      iapply HΦ $$ Hr

end proof

end EtcdGrove
end Perennial
