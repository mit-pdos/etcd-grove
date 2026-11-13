/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/IsDirWriteable.lean`, over
`filepath.Join`/`Abs`, `os.WriteFile.specEmptyS` and `os.Remove.specFileS` (with the trivial update).
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.IsDirWriteable
public import LinuxFs.Proof.os.WriteFile
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.PipeLemmas
public import LinuxFs.Spec.path.filepath.Join
public import LinuxFs.Spec.path.filepath.Abs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
variable [os_sem : os.Assumptions] [os.file.FieldAssumptions]

theorem touch_nameOk : NameOk go!".touch" := by decide

/-- `filepath.Abs` of `d/b` for a clean absolute `d` and a name `b`: itself. -/
theorem abs_child {d b : GoString} (hd : filepath.CleanAbs d) (hb : NameOk b) :
    path.cleanModel (child d b) = child d b := by
  rw [← join_child hd hb, filepath.joinModel_name d b hd (cleanSeg_of_nameOk hb)]
  exact filepath.cleanModel_cleanAbs _ (filepath.cleanAbs_append d b hd (cleanSeg_of_nameOk hb))

theorem child_head {d b : GoString} (hd : filepath.CleanAbs d) : (child d b).head? = some (W8 47) := by
  obtain ⟨segs, hne, -, rfl⟩ := hd
  cases segs with
  | nil => exact absurd rfl hne
  | cons s segs => simp [child, path.segsPath]

/-- A spine's path is a clean absolute path; the spine kept. -/
theorem osPathS_cleanAbs_keep (R : Roots) (d : GoString) (dq : DFrac) (j : Ino) :
    osPathS (GF := GF) R d dq j ⊢ osPathS R d dq j ∗ ⌜filepath.CleanAbs d⌝ := by
  unfold osPathS
  iintro ⟨%r, %j0, %cs, %h, Hs⟩
  obtain ⟨hR, hr, hcs, rfl⟩ := h
  isplitl [Hs]
  · iexists r, j0, cs; iframe; ipureintro; exact ⟨hR, hr, hcs, rfl⟩
  · ipureintro; exact cleanAbs_joinPath hR hr hcs

/-- An unlink's outcome on a whole claim, as two halves. -/
theorem os.rmFileOut_join (j : Ino) (b : GoString) (i : Ino) (h : NamesH) (o : Option (Nat × Nat)) :
    rmFileOut (GF := GF) j b i h (DFrac.own (1 : Qp).half) o ∗
      rmFileOut (GF := GF) j b i h (DFrac.own (1 : Qp).half) o ⊢
      ∃ h', osNames (GF := GF) j (.only [b]) (DFrac.own 1) h' ∗
        ⌜o.isSome → h'.cur !! b = none⌝ := by
  unfold rmFileOut
  cases o with
  | none =>
    simp only [claimOut]
    iintro ⟨⟨-, H1⟩, ⟨-, H2⟩⟩
    iexists h
    isplitl [H1 H2]
    · iapply (osNames_join j _ _ _ h (Qp.half_add_half 1)).1 $$ [$H1 $H2]
    ipureintro; intro hc; cases hc
  | some xs =>
    obtain ⟨x, s⟩ := xs
    simp only [claimOut]
    iintro ⟨⟨-, H1⟩, ⟨-, H2⟩⟩
    iexists _
    isplitl [H1 H2]
    · iapply (osNames_join j _ _ _ _ (Qp.half_add_half 1)).1 $$ [$H1 $H2]
    ipureintro; intro _
    simp only [NamesH.log]
    rw [restrictN_lookup _ _ _ (by simp [NameSet.Mem]), GMap.lookup_delete]

theorem go_etcd_io.etcd.client.pkg.v3.fileutil.IsDirWriteable.wp_proof
    (wp_Join : filepath.Join.spec (GF := GF) (hG := hG))
    (wp_Abs : filepath.Abs.spec (GF := GF) (hG := hG))
    (wp_WriteFile : os.WriteFile.specEmptyS (GF := GF) (hG := hG))
    (wp_Remove : os.Remove.specFileS (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.client.pkg.v3.fileutil.IsDirWriteable.spec (GF := GF) (hG := hG) := by
  intro dir R J dq hJ qc hlen hnone
  wp_start as ⟨#Hinv, #Hsi, Hp, Hperm, Hn⟩
  icases osPathS_cleanAbs_keep R dir dq J $$ Hp with ⟨Hp, %hclean⟩
  (try wp_auto)
  wp_apply wp_slice_literal (V := GoString) [dir, go!".touch"]
  isplitr
  · ipureintro; rfl
  iintro %jsl ⟨Hjsl, -⟩
  (try wp_auto)
  wp_apply wp_Join _ [dir, go!".touch"] _ (by simp; omega) $$ [$Hjsl] as %pth ⟨%hpth, -⟩
  rw [join_child hclean touch_nameOk] at hpth
  subst hpth
  (try wp_auto)
  wp_apply wp_Abs (child dir go!".touch") (child_head hclean)
  rw [abs_child hclean touch_nameOk]
  (try wp_auto)
  wp_apply wp_string_to_bytes ([] : GoString) as %sl ⟨Hsl, -⟩
  (try wp_auto)
  wp_apply wp_WriteFile dir go!".touch" sl (DFrac.own 1) _ R J dq hJ qc touch_nameOk hnone
    $$ [Hp Hperm Hn Hsl] as %err ⟨Hp, Hperm, -, %o, %hok, Hout⟩
  · iframe; isplitl [] <;> iassumption
  cases err with
  | ok e =>
    (try wp_auto)
    iapply HΦ
    iframe
    rcases o with _ | ⟨x, s, i⟩
    · dsimp only [crOut]
      iexists hJ
      iframe
      ipureintro; intro hc; cases hc
    · dsimp only [crOut]
      icases Hout with ⟨-, -, Hn⟩
      iexists _
      iframe
      ipureintro; intro hc; cases hc
  | nil =>
    obtain ⟨⟨x, s, i⟩, rfl⟩ := Option.isSome_iff_exists.1 (hok rfl)
    dsimp only [crOut]
    icases Hout with ⟨-, -, Hn⟩
    wp_auto
    generalize hh : hJ.log x (crEnt J go!".touch" i s) (<[go!".touch" := Node.file i]> hJ.cur) = h1
    have hcur : h1.cur !! go!".touch" = some (.file i) := by
      subst hh; simp [NamesH.log]
    icases (osNames_join J _ _ _ _ (Qp.half_add_half 1)).2 $$ Hn with ⟨Hq, Hr⟩
    ihave Hau := os.osAU_triv (A := Option (Nat × Nat))
      (osNames J (.only [go!".touch"]) (DFrac.own (1 : Qp).half) h1)
      (rmFileOut J go!".touch" i h1 (DFrac.own (1 : Qp).half)) $$ Hr
    wp_apply wp_Remove dir go!".touch" J i R dq h1 (1 : Qp).half (1 : Qp).half qc
        (rmFileOut J go!".touch" i h1 (DFrac.own (1 : Qp).half)) touch_nameOk hcur
        (Qp.half_add_half 1) $$ [Hp Hperm Hq Hau]
      as %e ⟨Hp, Hperm, %o', %hok', HQ, Hout⟩
    · iframe; isplitl [] <;> iassumption
    icases os.rmFileOut_join J _ i h1 o' $$ [HQ Hout] with ⟨%h', Hn, %hc⟩
    · iframe
    (try wp_auto)
    iapply HΦ
    iframe
    ipureintro; intro he; exact hc (hok' he)

end proof

end EtcdGrove
end Perennial
