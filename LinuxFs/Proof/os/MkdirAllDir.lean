/-
The proof of `Spec/os/MkdirAllDir.lean` (`os.MkdirAll.specDirS`), as `os.MkdirAll.wp_proofS`
(`Proof/os/MkdirAll.lean`) but for a name holding a directory: `Stat` of it (`os.Stat.wp_childDirS`, a
spine to it made of fractions of the spine to `d` and of the caller's claim), `IsDir` on success; after
an error, `MkdirAll(d)` (`wp_spineS`), `Mkdir(d/b)` of a taken name (`os.Mkdir.wp_takenS`: an error, no
effect), `Lstat(d/b)`. Lean-first.
-/
module

public import LinuxFs.Spec.os.MkdirAllDir
public import LinuxFs.Proof.os.MkdirAll

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions] [os.fileStat.FieldAssumptions]

/-- `os.Stat(d/b)` of the directory `J` at `b` (fractions of the spine to `d` and of the claim on `b`):
a `fileStat`, or an error; nothing changes. -/
theorem os.Stat.wp_childDirS (d b : GoString) (R : Roots) (j J : Ino) (qd qn : Qp) (h : NamesH)
    (qc : Qp) (hb : NameOk b) (hJ : h.cur !! b = some (.dir J)) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d (DFrac.own qd) j ∗
        osNames j (.only [b]) (DFrac.own qn) h ∗ osCallPerm qc }}
      (App (Val (@! os.Stat)) (Val #(child d b)))
    {{ (fi : GoInterface) (err : GoInterface), RET (PairV #fi #err); osPathS R d (DFrac.own qd) j ∗
        osNames j (.only [b]) (DFrac.own qn) h ∗ osCallPerm qc ∗
        ((∃ (fs : Loc) (sz : w64), ⌜err = interface.nil ∧
            fi = interface.mkOk (go.GoType.PointerType os.fileStat.ty) #fs⌝ ∗
            os.ownFileStat fs sz) ∨
         ⌜err ≠ interface.nil⌝) }} := by
  iintro %Φ ⟨#Hos, #Hsi, Hp, Hn, Hperm⟩ HΦ
  obtain ⟨ε, a', b', hqd, hqq⟩ := os.qp_common qd qn
  subst hqd hqq
  icases (osPathS_frac R d ε a' j).1 $$ Hp with ⟨Hpe, Hpa⟩
  icases (osNames_frac j (.only [b]) ε b' h).1 $$ Hn with ⟨Hne, Hnb⟩
  ihave Hpc := osPathS_child R d b (DFrac.own ε) j J h hb hJ $$ Hpe Hne
  wp_apply os.Stat.wp_dirS (child d b) R J (DFrac.own ε) qc $$ [Hpc Hperm]
    as %fi %err ⟨Hpc, Hperm, Hres⟩
  · iframe; iframe #
  icases os.osPathS_unchild R d b j J ε a' hb $$ [Hpc Hpa] with ⟨%h'', Hp, Hne, %-⟩
  · iframe
  icases osNames_agree j (.only [b]) _ _ h'' h $$ Hne Hnb with %he
  subst he
  ihave Hn := (osNames_frac j (.only [b]) ε b' h'').2 $$ [Hne Hnb]
  · iframe
  iapply HΦ
  iframe

/-- `os.Lstat(d/b)` of the directory `J` at `b`, as `os.Stat.wp_childDirS`. -/
theorem os.Lstat.wp_childDirS (d b : GoString) (R : Roots) (j J : Ino) (qd qn : Qp) (h : NamesH)
    (qc : Qp) (hb : NameOk b) (hJ : h.cur !! b = some (.dir J)) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d (DFrac.own qd) j ∗
        osNames j (.only [b]) (DFrac.own qn) h ∗ osCallPerm qc }}
      (App (Val (@! os.Lstat)) (Val #(child d b)))
    {{ (fi : GoInterface) (err : GoInterface), RET (PairV #fi #err); osPathS R d (DFrac.own qd) j ∗
        osNames j (.only [b]) (DFrac.own qn) h ∗ osCallPerm qc ∗
        ((∃ (fs : Loc) (sz : w64), ⌜err = interface.nil ∧
            fi = interface.mkOk (go.GoType.PointerType os.fileStat.ty) #fs⌝ ∗
            os.ownFileStat fs sz) ∨
         ⌜err ≠ interface.nil⌝) }} := by
  iintro %Φ ⟨#Hos, #Hsi, Hp, Hn, Hperm⟩ HΦ
  obtain ⟨ε, a', b', hqd, hqq⟩ := os.qp_common qd qn
  subst hqd hqq
  icases (osPathS_frac R d ε a' j).1 $$ Hp with ⟨Hpe, Hpa⟩
  icases (osNames_frac j (.only [b]) ε b' h).1 $$ Hn with ⟨Hne, Hnb⟩
  ihave Hpc := osPathS_child R d b (DFrac.own ε) j J h hb hJ $$ Hpe Hne
  wp_apply os.Lstat.wp_dirS (child d b) R J (DFrac.own ε) qc $$ [Hpc Hperm]
    as %fi %err ⟨Hpc, Hperm, Hres⟩
  · iframe; iframe #
  icases os.osPathS_unchild R d b j J ε a' hb $$ [Hpc Hpa] with ⟨%h'', Hp, Hne, %-⟩
  · iframe
  icases osNames_agree j (.only [b]) _ _ h'' h $$ Hne Hnb with %he
  subst he
  ihave Hn := (osNames_frac j (.only [b]) ε b' h'').2 $$ [Hne Hnb]
  · iframe
  iapply HΦ
  iframe

set_option hygiene false in
/-- `IsDir` through the `FileInfo` of a `*fileStat` (`os.ownFileStat` in `H`): some boolean. -/
local macro "fileStat_isDir" H:ident : tactic => `(tactic| (
  unfold os.ownFileStat
  icases $H:ident with ⟨#Hsz, ⟨%mode, #Hmode⟩, -⟩
  wp_method_call
  wp_call
  try wp_auto
  wp_method_call
  wp_call
  try wp_auto
  haveI : go.NotInterface go.uint32 := ⟨trivial⟩
  try wp_auto
  wp_method_call
  wp_call
  try wp_auto
  iclear Hsz Hmode))

theorem os.MkdirAll.wp_proofDirS : os.MkdirAll.specDirS (GF := GF) (hG := hG) := by
  intro d b perm R j J qd qn h qc hb hJ
  have hbN : (NameSet.only [b]).Mem b := by simp [NameSet.Mem]
  wp_start as ⟨#Hos, #Hsi, Hp, Hperm, Hn⟩
  icases (os.osPathS_unfold R d _ j).1 $$ Hp with ⟨%r0, %j0, %cs, %hp, Hs⟩
  obtain ⟨hR, hm, hcs, rfl⟩ := hp
  have hcsb : ∀ x ∈ cs ++ [b], NameOk x := by
    intro x hx; simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hcs x hx
    · exact hb
  have hpin : PathIn R (child (joinPath r0 cs) b) := ⟨r0, j0, cs ++ [b], hm, hcsb, (joinPath_snoc _ _ _).symm⟩
  have htn : RootsTreeName R (child (joinPath r0 cs) b) := by
    rw [← joinPath_snoc]; exact os.treeName_snoc hm hcsb
  try wp_auto
  wp_apply wp_osPathKindS R _ hpin CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi as %k %hk
  obtain ⟨-, rfl⟩ := hk.resolve_right (fun h => h.1 htn)
  wp_auto
  rw [show (go!"os.Stat" : GoString) = os.Stat from rfl]
  ihave Hp := (os.osPathS_joinPath R r0 j0 cs _ j hR hm hcs).2 $$ Hs
  wp_apply os.Stat.wp_childDirS (joinPath r0 cs) b R j J qd qn h qc hb hJ $$ [Hp Hn Hperm]
    as %fi %err ⟨Hp, Hn, Hperm, Hres⟩
  · iframe; iframe #
  icases Hres with (⟨%fs, %sz, %hfe, Hfs⟩ | %herr)
  · -- `Stat` found it: `nil` if `IsDir`, else `ENOTDIR`
    obtain ⟨rfl, rfl⟩ := hfe
    wp_auto
    fileStat_isDir Hfs
    wp_if_destruct
    all_goals
      try (unfold os.model.pathError; wp_apply wp_errno)
      try wp_auto
      iapply HΦ
      iframe
  cases err with
  | nil => exact absurd rfl herr
  | ok ie =>
  wp_auto
  wp_apply os.model.wp_mkdirAllParent
  rw [os.parentModel_child _ b hb]
  have hrne : 0 < r0.length := by
    obtain ⟨rc, hne, -, hrf⟩ := (hR.2.2 (r0, j0) hm).1
    rcases rc with _ | ⟨x, rc⟩
    · exact absurd rfl hne
    · simp only at hrf; rw [hrf]; simp [joinPath]
  have hplen : 0 < (joinPath r0 cs).length := by
    simp only [joinPath, List.length_append]; omega
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %hlen
  rw [decide_eq_true (show sint.Z (W64 0) < sint.Z (W64 ((joinPath r0 cs).length : Int)) by word)]
  wp_auto
  ihave Hs := (os.osPathS_joinPath R r0 j0 cs _ j hR hm hcs).1 $$ Hp
  wp_apply os.MkdirAll.wp_spineS r0 j0 perm R _ qc hR hm cs j hcs $$ [Hs Hperm] as %e ⟨Hs, Hperm⟩
  · iframe; iframe #
  ihave Hp := (os.osPathS_joinPath R r0 j0 cs _ j hR hm hcs).2 $$ Hs
  cases e with
  | ok ie2 =>
    -- the parent's `MkdirAll` failed
    wp_auto
    iapply HΦ
    iframe
  | nil =>
  wp_auto
  rw [show (go!"os.Mkdir" : GoString) = os.Mkdir from rfl]
  wp_apply os.Mkdir.wp_takenS (joinPath r0 cs) b perm R j (.only [b]) _ (DFrac.own qn) h qc hb hbN
      (by rw [hJ]; rfl) $$ [Hp Hn Hperm] as %e ⟨Hp, Hn, Hperm, %he⟩
  · iframe; iframe #
  cases e with
  | nil => exact absurd rfl he
  | ok ie3 =>
  wp_auto
  rw [show (go!"os.Lstat" : GoString) = os.Lstat from rfl]
  wp_apply os.Lstat.wp_childDirS (joinPath r0 cs) b R j J qd qn h qc hb hJ $$ [Hp Hn Hperm]
    as %fi %err ⟨Hp, Hn, Hperm, Hres⟩
  · iframe; iframe #
  icases Hres with (⟨%fs, %sz, %hfe, Hfs⟩ | %herr2)
  · obtain ⟨rfl, rfl⟩ := hfe
    wp_auto
    fileStat_isDir Hfs
    wp_if_destruct
    all_goals
      iapply HΦ
      iframe
  · cases err with
    | nil => exact absurd rfl herr2
    | ok ie4 =>
    wp_auto
    iapply HΦ
    iframe

end proof

end EtcdGrove
end Perennial
