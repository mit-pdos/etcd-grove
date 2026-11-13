/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/readWALNames.lean`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.readWALNames
public import LinuxFs.Spec.fmt.ErrorfErrs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Fs

/-- The index form of sortedness (`fileutil.ReadDirOut`'s) is `Pairwise`. -/
theorem pairwise_of_idx {R : GoString → GoString → Prop} {l : List GoString}
    (h : ∀ (i j : Nat) (xi xj : GoString), l[i]? = some xi → l[j]? = some xj → i < j → R xi xj) :
    l.Pairwise R := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  exact h i j _ _ (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hj) hij

/-- **`readWALNames`' result** from `ReadDir`'s and `checkWALNames`'. -/
theorem walNamesOut_of {N : NameSet} {h : NamesH} {names rs ws : List GoString}
    (hok : ∀ b ∈ names, NameOk b) (hex : ∀ b, N.Mem b → ((h.cur !! b).isSome ↔ b ∈ names))
    (hcnt : ∀ b, N.Mem b → names.count b ≤ 1) (hout : fileutil.ReadDirOut names (fileutil.optsExt []) rs)
    (hsel : WalNamesSel rs ws) (hne : ws ≠ []) : WalNamesOut N h ws := by
  obtain ⟨srt, hperm, hsrt, hrs⟩ := hout
  have hrs' : rs = srt := by rw [hrs]; simp [fileutil.optsExt]
  subst hrs'
  obtain ⟨hsub, hmay, hall⟩ := hsel
  have hmem : ∀ b ∈ ws, b ∈ names := fun b hb => hperm.mem_iff.2 (hsub.subset hb)
  refine ⟨hne, (pairwise_of_idx hsrt).sublist hsub, fun b hb => ⟨hok b (hmem b hb), hmay b hb⟩,
    fun b hN hb => (hex b hN).2 (hmem b hb), fun b hN hs hp => hall b (hperm.mem_iff.1 ((hex b hN).1 hs)) hp,
    fun b hN => ?_⟩
  exact Nat.le_trans (hsub.count_le b) (by rw [← hperm.count_eq]; exact hcnt b hN)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

theorem go_etcd_io.etcd.server.v3.storage.wal.readWALNames.wp_proof
    (HRead : go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDir.spec (GF := GF) (hG := hG))
    (HCheck : go_etcd_io.etcd.server.v3.storage.wal.checkWALNames.spec (GF := GF) (hG := hG))
    (HErrorf : fmt.ErrorfErrs.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.readWALNames.spec (GF := GF) (hG := hG) := by
  intro lg d R j dq qc N dqn h
  wp_start as ⟨#Hlg, #Hos, #Hsi, Hp, Hperm, Hn⟩
  ihave #Hpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal $$ []
  · iPkgInit
  ihave #Hi : (wal.walInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hi with ⟨-, -, -, -, -, Hfnf, -⟩
  iunfold wal.errVar at Hfnf
  icases Hfnf with ⟨%efnf, #Hfnf, -⟩
  wp_auto
  wp_apply HRead d slice.nil [] [] (DFrac.own 1) R j dq qc N dqn h rfl $$ [Hp Hperm Hn]
    as %r %err ⟨Hp, Hperm, Hn, -, Hr⟩
  · isplitl []
    · iexact Hos
    isplitl []
    · iexact Hsi
    isplitl []
    · iPkgInit
    iframe
    isplitl []
    · iapply ownSlice_nil
    try simp only [BigSepL.bigSepL_nil]
    iempintro
  icases Hr with (⟨%names, %rs, ⟨%herr, %hok, %hex, %hcnt, %hout⟩, Hrs⟩ | ⟨%herr, #Herr⟩)
  · subst herr
    wp_auto
    wp_apply HCheck lg r rs (DFrac.own 1) $$ [Hrs] as %ws ⟨Hrs, %wl, %hsel, Hws⟩
    · iframe; iexact Hlg
    try wp_auto
    ihave %Hwl := ownSlice_len _ _ _ $$ Hws
    wp_if_destruct
    · try wp_auto
      iapply HΦ
      iframe
      iright
      ipureintro; intro h; cases h
    · have hne : wl ≠ [] := by
        intro he; subst he; apply Hif; simp at Hwl; word
      try wp_auto
      iapply HΦ
      iframe
      ileft
      iexists wl
      iframe
      ipureintro
      exact ⟨rfl, walNamesOut_of hok hex hcnt hout hsel hne⟩
  · cases err with
    | nil => exact absurd rfl herr
    | ok ie =>
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨Hasl, -⟩
    wp_apply HErrorf _ _ [GoInterface.ok ie] [ie] (by
          intro ii hii
          right
          simpa using hii) $$ [Hasl] as %err2 #Herr2
    · iframe
      iapply (BigSepL.bigSepL_singleton (Φ := fun _ e => errOk (GF := GF) e)).2
      unfold fmtErrorOkOrNil fmtErrorOk
      icases Herr with ⟨-, H⟩
      unfold errOk
      rw [fmt.stringMethodSpec_unfold]
      iexact H
    try wp_auto
    iapply HΦ
    iframe
    iright
    ipureintro; intro h; cases h

end proof

end EtcdGrove
end Perennial
