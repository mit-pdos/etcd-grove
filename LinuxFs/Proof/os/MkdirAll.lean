/-
The proof of `Spec/os/MkdirAll.lean`, over the pieces of `Proof/os/MkdirAllParts.lean` and
`os.Mkdir.specS`: `PathKind` (below a root), `Stat` of the absent name (an error), `MkdirAll` of the
existing parent (`os.MkdirAll.wp_spineS`: nothing changes); if that failed, the atomic update is
committed with `none` by a fancy update (no step); else `os.Mkdir.specS` with the same update, and
after a failed `Mkdir` the `Lstat` of `d/b`: of an absent name if nothing was logged, else through a
spine to the new directory made of fractions of the spine to `d` and of the caller's claim.
-/
module

public import LinuxFs.Spec.os.MkdirAll
public import LinuxFs.Proof.os.Mkdir
public import LinuxFs.Proof.os.MkdirAllParts

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

/-- An atomic update whose outcome `none` holds of its precondition commits with `none`, no step. -/
theorem os.osAU_commit_none {A : Type} (α : IProp GF) (β Q : Option A → IProp GF)
    (hβ : α ⊢ β none) : osAU α β Q ⊢ |={⊤}=> Q none := by
  iintro Hau
  unfold osAU
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  ihave Hacc := fupd_open_au _ $$ Hacc
  imod Hacc with Hacc
  isimp only [texist_nil] at Hacc
  icases Hacc with ⟨Hα, Hcl⟩
  icases Hcl with ⟨-, Hco⟩
  isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hco
  iapply fupd_close_au
  iapply Hco
  iapply hβ
  irevert Hα
  dsimp only [Std.Tele.app]
  iintro Hα
  iexact Hα

theorem os.osPathS_unfold (R : Roots) (p : GoString) (dq : DFrac) (j : Ino) :
    osPathS (GF := GF) R p dq j ⊣⊢ ∃ (r : GoString) (j0 : Ino) (cs : List GoString),
      ⌜RootsOk R ∧ (r, j0) ∈ R ∧ (∀ c ∈ cs, NameOk c) ∧ p = joinPath r cs⌝ ∗ osSpine j0 cs dq j := by
  unfold osPathS; exact .rfl

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

theorem os.MkdirAll.wp_proofS : os.MkdirAll.specS (GF := GF) (hG := hG) := by
  intro d b perm R j qd h q r Q hb hn hq
  have hbN : (NameSet.only [b]).Mem b := by simp [NameSet.Mem]
  wp_start as ⟨#Hos, #Hsi, Hp, Hperm, Hn, Hau⟩
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
  wp_apply os.Stat.wp_absentS (joinPath r0 cs) b R j (.only [b]) _ (DFrac.own q) h 1 hb hbN hn
    $$ [Hp Hn Hperm] as %fi %err ⟨Hp, Hn, Hperm, %herr⟩
  · iframe; iframe #
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
  wp_apply os.MkdirAll.wp_spineS r0 j0 perm R _ 1 hR hm cs j hcs $$ [Hs Hperm] as %e ⟨Hs, Hperm⟩
  · iframe; iframe #
  ihave Hp := (os.osPathS_joinPath R r0 j0 cs _ j hR hm hcs).2 $$ Hs
  cases e with
  | ok ie2 =>
    -- the parent's `MkdirAll` failed: no `Mkdir`, the update commits with `none`
    imod os.osAU_commit_none _ _ Q (by dsimp only [mkOut]; exact .rfl) $$ Hau with HQ
    wp_auto
    iapply HΦ
    iframe
    dsimp only [mkOut, mkNew]
    iframe
    ipureintro; intro hc; cases hc
  | nil =>
  wp_auto
  rw [show (go!"os.Mkdir" : GoString) = os.Mkdir from rfl]
  wp_apply os.Mkdir.wp_proofS (joinPath r0 cs) b perm R j (DFrac.own qd) h q r Q hb hn hq
    $$ [Hp Hperm Hn Hau] as %e ⟨Hp, Hperm, %o, %ho, HQ, Hout, Hnew⟩
  · iframe; iframe #
  cases e with
  | nil =>
    wp_auto
    iapply HΦ
    iframe
    ipureintro; exact ho
  | ok ie3 =>
  wp_auto
  rw [show (go!"os.Lstat" : GoString) = os.Lstat from rfl]
  cases o with
  | none =>
    -- nothing logged: `d/b` is still absent
    isimp only [mkOut] at Hout
    wp_apply os.Lstat.wp_absentS (joinPath r0 cs) b R j (.only [b]) _ (DFrac.own q) h 1 hb hbN hn
      $$ [Hp Hout Hperm] as %fi %err ⟨Hp, Hout, Hperm, %herr2⟩
    · iframe; iframe #
    cases err with
    | nil => exact absurd rfl herr2
    | ok ie4 =>
    wp_auto
    iapply HΦ
    iframe
    dsimp only [mkOut]
    iframe
    ipureintro; intro hc; cases hc
  | some xs =>
  obtain ⟨x, s0, J⟩ := xs
  isimp only [mkOut] at Hout
  icases Hout with ⟨Hlog, Hn⟩
  have hJ : ((h.log x (mkEnt j b J s0) (<[b := .dir J]> h.cur)).cur !! b) = some (.dir J) := by
    simp only [NamesH.log]; rw [GMap.lookup_insert]
  generalize hh : h.log x (mkEnt j b J s0) (<[b := .dir J]> h.cur) = h' at hJ ⊢
  -- a spine to the new directory, from fractions of the spine and of the caller's claim
  obtain ⟨ε, a', b', hqd, hqq⟩ := os.qp_common qd q
  subst hqd hqq
  icases (osPathS_frac R (joinPath r0 cs) ε a' j).1 $$ Hp with ⟨Hpe, Hpa⟩
  icases (osNames_frac j (.only [b]) ε b' h').1 $$ Hn with ⟨Hne, Hnb⟩
  ihave Hpc := osPathS_child R _ b (DFrac.own ε) j J h' hb hJ $$ Hpe Hne
  wp_apply os.Lstat.wp_dirS (child (joinPath r0 cs) b) R J (DFrac.own ε) 1 $$ [Hpc Hperm]
    as %fi %err ⟨Hpc, Hperm, Hres⟩
  · iframe; iframe #
  icases os.osPathS_unchild R (joinPath r0 cs) b j J ε a' hb $$ [Hpc Hpa] with ⟨%h'', Hp, Hne, %-⟩
  · iframe
  icases osNames_agree j (.only [b]) _ _ h'' h' $$ Hne Hnb with %he
  subst he
  ihave Hn := (osNames_frac j (.only [b]) ε b' h'').2 $$ [Hne Hnb]
  · iframe
  icases Hres with (⟨%fs, %sz, %hfe, Hfs⟩ | %herr2)
  · obtain ⟨rfl, rfl⟩ := hfe
    wp_auto
    fileStat_isDir Hfs
    subst hh
    wp_if_destruct
    all_goals
      iapply HΦ
      iframe
      isimp only [mkOut]
      iframe
      ipureintro; intro _; rfl
  · cases err with
    | nil => exact absurd rfl herr2
    | ok ie4 =>
    wp_auto
    subst hh
    iapply HΦ
    iframe
    isimp only [mkOut]
    iframe
    ipureintro; intro _; rfl

end proof

end EtcdGrove
end Perennial
