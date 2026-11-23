/-
`os.Rename(d/wal.tmp, d/wal)` (walfs-local), `d` the root directory `j`, with the program's half of
the invariant's claims (merged: `wal` and `wal.tmp` one claim) and the whole claim on the new
`seg` of `wal.tmp`'s directory `J`. The model (`TrustedCode/os.lean`) first asks `lstat(2)` whether
`wal` is a directory (it is absent: no), then renames, `EINTR` retried. The rename's step opens the
invariant (`wp_dsRename`); once it took effect, a retry finds `wal.tmp` gone and fails
(`wp_osRenameAbsentS`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.DSRemove
public import Proof.os.RenameS

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_walfs
namespace DS

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section prog
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

set_option hygiene false in
/-- `os.Rename`'s error after a failed attempt `e` (`he : e ≠ 0`): `post` after `iapply HΦ`. -/
local macro "ren_err" " => " post:tacticSeq : tactic => `(tactic| (
  rw [decide_eq_false (show ¬ e = W64 0 from he)]
  wp_auto
  wp_apply wp_errno
  unfold os.model.linkError
  rw [show os.model.LinkError = os.LinkError.ty by unfold os.LinkError.ty; rfl]
  wp_auto
  iapply HΦ
  ($post)))

/-- **`os.Rename(d/wal.tmp, d/wal)`**, `wal` absent, `wal.tmp` the directory `J` whose `seg` is the
key's file `k`: any result. -/
theorem wp_osRenameWal (R : Roots) (dir : GoString) (j J k : Ino) (hrj : (dir, j) ∈ R) (γ : GName)
    (hw hs : NamesH) (hT : hw.cur !! wtB = some (.dir J)) (hA : hw.cur !! walB = none)
    (hseg : hs.cur !! segB = some (.file k)) (hcoh : HistCoh hs J sN) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ dsInv (GF := GF) j γ ∗ osCallPerm (callKey R dir) 1 ∗
        dsHalf (GF := GF) j γ (some k) true hw none ∗ osNames J sN (DFrac.own 1) hs }}
      (App (App (Val (@! os.Rename)) (Val #(child dir wtB))) (Val #(child dir walB)))
    {{ (err : GoInterface), RET #err; osCallPerm (callKey R dir) 1 }} := by
  wp_start as ⟨#Hos, #Hsi, #Hinv, Hperm, Hh, HJ⟩
  imod osPathS_root R dir j (DFrac.own 1) hrj CoPset.subseteq_top $$ Hsi with Hp
  imod osNames_next R J sN _ hs CoPset.subseteq_top $$ Hsi HJ with ⟨HJ, #Hlb⟩
  -- `lstat(wal)`: not a directory
  icases osCallPerm_child R dir walB _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
  wp_apply wp_osCallBeginS R _ 1 hs.next CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs0 Hk Hls
  iclear Hls
  unfold dsHalf
  icases Hh with ⟨Hv, Hw, Hs⟩
  wp_apply wp_osLstatDirS_mem R dir walB j wN (DFrac.own 1) (DFrac.own (1 : Qp).half) hw t s0 1
    walB_ok wN_wal CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi Hp Hw Hk
    as %isDir %e0 %hd Hperm Hp Hw
  have hd1 : isDir ≠ W64 1 := fun h1 => by
    obtain ⟨⟨J', hJ'⟩, -⟩ := hd h1
    rw [hA] at hJ'; cases hJ'
  rw [decide_eq_false hd1]
  wp_auto
  ihave Hh : dsHalf (GF := GF) j γ (some k) true hw none $$ [Hv Hw Hs]
  · unfold dsHalf; iframe
  iclear Hp
  -- the rename loop: before the rename, or after it
  ihave HSt : iprop((dsHalf (GF := GF) j γ (some k) true hw none ∗
        osNames (GF := GF) J sN (DFrac.own 1) hs) ∨
      ∃ hw' hsO, dsHalf (GF := GF) j γ (some k) true hw' hsO ∗ ⌜hw'.cur !! wtB = none⌝)
    $$ [Hh HJ]
  · ileft; iframe
  iloeb as IH generalizing Hperm HSt
  imod osPathS_root R dir j (DFrac.own 1) hrj CoPset.subseteq_top $$ Hsi with Hp
  icases osCallPerm_child R dir wtB _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
  wp_apply wp_osCallBeginS R _ 1 hs.next CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t1 %s1 %hs1 Hk1 Hls1
  iclear Hls1
  icases HSt with (⟨Hh, HJ⟩ | ⟨%hw', %hsO, Hh, %hwt⟩)
  · wp_apply wp_dsRename R dir (DFrac.own 1) j J k γ hw hs t1 s1 hT hA hseg hcoh hs1
      $$ Hos Hsi Hinv Hp Hh HJ Hk1 as %e Hperm - Hr
    unfold dsRenamed
    icases Hr with (⟨%he, Hh, HJ⟩ | ⟨%hw', Hh, %hw2⟩)
    · by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        wp_auto
        iapply IH $$ Hperm [Hh HJ] HΦ
        ileft; iframe
      rw [decide_eq_false he4]
      wp_auto
      ren_err =>
        iexact Hperm
    · by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        wp_auto
        iapply IH $$ Hperm [Hh] HΦ
        iright; iexists hw', some (J, hs); iframe Hh; ipureintro; exact hw2.2
      rw [decide_eq_false he4]
      wp_auto
      by_cases he0 : e = W64 0
      · rw [decide_eq_true he0]
        wp_auto
        iapply HΦ
        iexact Hperm
      have he : e ≠ W64 0 := he0
      ren_err =>
        iexact Hperm
  · unfold dsHalf
    icases Hh with ⟨Hv, Hw, Hs⟩
    imod osPathS_root R dir j (DFrac.own 1) hrj CoPset.subseteq_top $$ Hsi with Hp'
    icases osPathS_sameRoot R dir wtB walB _ j $$ Hp' with ⟨Hp', %hsr⟩
    wp_apply wp_osRenameAbsentS R dir wtB dir walB j j wN (DFrac.own 1) (DFrac.own 1)
      (DFrac.own (1 : Qp).half) hw' t1 s1 1 wtB_ok walB_ok wN_wt hwt hsr CoPset.subseteq_top
      CoPset.subseteq_top $$ Hos Hsi Hp Hp' Hw Hk1 as %e %he Hperm - - Hw
    ihave Hh : dsHalf (GF := GF) j γ (some k) true hw' hsO $$ [Hv Hw Hs]
    · unfold dsHalf; iframe
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      iapply IH $$ Hperm [Hh] HΦ
      iright; iexists hw', hsO
      isplitl [Hh]
      · first | iexact Hh | (unfold dsHalf at *; iexact Hh) | (unfold dsHalf; iexact Hh)
      ipureintro; exact hwt
    rw [decide_eq_false he4]
    wp_auto
    ren_err =>
      iexact Hperm

end prog

end DS
end osfs_walfs
end EtcdGrove
end Perennial

end
