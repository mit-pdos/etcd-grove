/-
The proofs of `examples/osfs/walfs`'s `seglog.go` (one generation), part 1, over the file extension's
shared view. `seglog` needs no crash invariant: its result asks nothing of the tree a crash leaves.
The program holds the whole claim on `seg.log` of its root `dir` with the root's call permission
(`logRes`) and, if `seg.log` names a directory, that directory's whole claim (`DS.subRes`), all from
what a generation starts with (`log_start`). Here: that start, and `os.OpenFile(dir/seg.log,
O_RDWR|O_CREATE)` of the absent name (`wp_openLog`, over `specCreateS`, a hypothesis, with the trivial update), which also
gives the `*File`'s offset (`os.ownOff`). The removal is `DS.wp_rmAny`, the opens of the existing file
`os.OpenFile.wp_fileS`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.DSRemove
public import Spec.os.OpenFileS
public import Proof.os.WriteFileLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_walfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs DSBase

def logB : GoString := go!"seg.log"

theorem logB_ok : NameOk logB := by decide

/-- The claim on `seg.log`. -/
abbrev lN : NameSet := .only [logB]

theorem lN_log : lN.Mem logB := by simp [NameSet.Mem]

theorem createL_flag :
    OpenFlagsOk (W64 66 ||| W64 0x80000).toNat ∧ (W64 66 ||| W64 0x80000).toNat / O_CREAT % 2 = 1 ∧
      (W64 66 ||| W64 0x80000).toNat / O_TRUNC % 2 = 0 := by
  unfold OpenFlagsOk O_CREAT O_TRUNC O_CLOEXEC
  decide

theorem createL_openFd (i : Ino) : openFd i (W64 66 ||| W64 0x80000) = ⟨i, true, true, none, none⟩ := rfl

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- **What the program holds**: the root's call permission and the whole claim on `seg.log`. -/
def logRes (R : Roots) (dir : GoString) (j : Ino) (h : NamesH) : IProp GF :=
  iprop(osCallPerm (L := L) (callKey R dir) 1 ∗ osNames (L := L) j lN (DFrac.own 1) h)

/-- **A generation's start**: from the tree's resources (`osShared`, nothing logged) on a well-formed
tree, what the program holds. -/
theorem log_start (R : Roots) (hR : RootsOk R) (r : GoString) (j : Ino) (hr : (r, j) ∈ R) (m : Tree)
    (hwf : TreeWf R m) (E : CoPset) (hE : ↑osShN ⊆ E) :
    ⊢ osShared (L := L) R (m, []) ={E}=∗ osSharedInv (L := L) R ∗
      logRes (L := L) R r j (NamesH.init m j lN) ∗ DS.subRes (L := L) logB (NamesH.init m j lN) := by
  have hj : j ∈ m := hwf.1 j (.root r j hr)
  have hnow : Hist.now ((m, []) : Hist) = m := by simp [Hist.now, Hist.ops, replay]
  have mem : ∀ J, J ∈ m → J ∈ dirsOf (m, []) := fun J h => by
    show J ∈ (GMap.toList (Hist.now ((m, []) : Hist))).map (·.1)
    rw [hnow]
    cases he : m !! J with
    | none => have := (GMap.mem_iff _ _).1 h; rw [he] at this; cases this
    | some d => exact List.mem_map.2 ⟨(J, d), (GMap.mem_toList _ _ _).2 he, rfl⟩
  have hL : ∀ J, DS.dirOf m j logB = some J → J ∈ m ∧ J ≠ j := fun J hJ => by
    have he := DS.dirOf_some hJ
    exact ⟨(hwf.2.2.1 j logB _ he).2 J (by simp [Node.dirIno]),
      fun h => hwf.2.2.2.1 j logB J he r (h ▸ hr)⟩
  have hc : (NamesH.init m j lN).cur !! logB = m.entry j logB := by
    show restrictN lN (entsOf m j) !! logB = _
    rw [restrictN_lookup _ _ _ lN_log, entsOf_lookup]
  unfold osShared
  iintro ⟨#Hsh, -, Hperm, -, Hall⟩
  icases osCallPerms_root R r j hR hr $$ Hperm with ⟨Hperm, -⟩
  icases (BigSepL.bigSepL_perm (List.perm_cons_erase (mem j hj))).1 $$ Hall with Hall
  icases BigSepL.bigSepL_cons.1 $$ Hall with ⟨Hj, Hall⟩
  ihave Hall := DS.bigSepL_take_opt (L := L) (m, []) _ (DS.dirOf m j logB) (fun J hJ =>
    (List.mem_erase_of_ne (hL J hJ).2).2 (mem J (hL J hJ).1)) $$ Hall
  icases Hall with ⟨HL, -⟩
  imod DS.osNames_take1 (L := L) R (m, []) j [] logB (by simp) hE $$ Hsh Hj with ⟨Hl, -⟩
  rw [DS.namesOf_nil]
  imodintro
  iframe Hsh
  isplitl [Hperm Hl]
  · unfold logRes; iframe
  unfold DS.subRes DS.optClaim
  rw [hc]
  cases hd : DS.dirOf m j logB with
  | none =>
    iclear HL
    have : ∀ J, m.entry j logB ≠ some (.dir J) := fun J h => by
      unfold DS.dirOf at hd; rw [h] at hd; cases hd
    cases he : m.entry j logB with
    | none => iempintro
    | some n =>
      cases n with
      | file i => iempintro
      | dir J => exact absurd he (this J)
  | some J =>
    rw [DS.dirOf_some hd]
    iexists _; iexact HL

end res

/-! ## `os.OpenFile` of the absent `seg.log`, with `O_CREAT` -/

section oscalls
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [go.BasicIntoValInj]
variable [sem : go.Semantics] [os.Assumptions] [os.file.FieldAssumptions]

/-- **`os.OpenFile(dir/seg.log, O_RDWR|O_CREATE, perm)`**, `dir` the root of inode `j`, `seg.log`
absent: on success a new file of a fresh inode `i`, `seg.log` names it. -/
theorem wp_openLog (wp_CreateS : os.OpenFile.specCreateS (GF := GF) (hG := hG)) (R : Roots) (dir : GoString) (j : Ino) (hrj : (dir, j) ∈ R) (h : NamesH)
    (hn : h.cur !! logB = none) (perm : w32) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ logRes (GF := GF) R dir j h }}
      (App (App (App (Val (@! os.OpenFile)) (Val #(child dir logB))) (Val #(W64 66))) (Val #perm))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err);
        ((∃ (fd : w64) (i : Ino) (h' : NamesH), ⌜err = interface.nil ∧ 0 ≤ fd.toInt ∧
              h'.cur !! logB = some (.file i)⌝ ∗
            os.ownFile f fd (child dir logB) (DFrac.own 1) ∗ os.ownOff f (W64 0) ∗
            osFd fd (DFrac.own 1) ⟨i, true, true, none, none⟩ ∗ osMeta i (DFrac.own 1) newMeta ∗
            logRes (GF := GF) R dir j h') ∨
         (⌜err ≠ interface.nil⌝ ∗ ∃ h', logRes (GF := GF) R dir j h')) }} := by
  iintro %Φ ⟨#Hos, #Hsi, Hh⟩ HΦ
  unfold logRes
  icases Hh with ⟨Hperm, Hn⟩
  imod osPathS_root R dir j (DFrac.own 1) hrj CoPset.subseteq_top $$ Hsi with Hp
  obtain ⟨hfl, hcr, htr⟩ := createL_flag
  icases (osNames_join j _ _ _ h (Qp.half_add_half 1)).2 $$ Hn with ⟨Hn, Hnr⟩
  ihave Hau := os.osAU_triv (A := Option (Nat × Nat × Ino))
    (osNames (GF := GF) j (.only [logB]) (DFrac.own (1 : Qp).half) h)
    (crOut j logB h (DFrac.own (1 : Qp).half)) $$ Hnr
  wp_apply wp_CreateS dir logB (W64 66) perm R j _ h
    (1 : Qp).half (1 : Qp).half 1 (crOut j logB h (DFrac.own (1 : Qp).half)) hfl hcr htr logB_ok
    (fun J h' => by rw [hn] at h'; cases h') (Qp.half_add_half 1)
    $$ [$Hos $Hsi $Hp $Hperm $Hn $Hau]
    as %f %err ⟨-, Hperm, %oc, Ho1, Ho2, Hm, Hr⟩
  ihave Ho := os.crOut_join j logB h oc $$ [$Ho1 $Ho2]
  rcases oc with _ | ⟨x, s0, i⟩
  · -- no effect: an error (the name was empty)
    icases Hr with (⟨%fd, %i, %hres, -, -, -⟩ | ⟨%herr, -⟩)
    · obtain ⟨-, -, hi⟩ := hres
      simp only [crIno] at hi
      rw [hn] at hi; cases hi
    iapply HΦ
    iright
    isplitr
    · ipureintro; exact herr.1
    iexists h
    iframe Hperm
    unfold crOut; iexact Ho
  unfold crOut crMeta
  icases Ho with ⟨%hcr0, -, Hn⟩
  icases Hr with (⟨%fd, %i', %hres, Hf, Hoff, Hfd⟩ | ⟨%herr, -⟩)
  · obtain ⟨rfl, hfd0, hi⟩ := hres
    simp only [crIno] at hi
    subst hi
    rw [createL_openFd] at *
    iapply HΦ
    ileft
    iexists fd, i', (h.log x (crEnt j logB i' s0) (<[logB := .file i']> h.cur))
    iframe Hf Hoff Hfd Hm
    isplitr
    · ipureintro; exact ⟨rfl, hfd0, GMap.lookup_insert _ _ _⟩
    iframe Hperm Hn
  · iapply HΦ
    iright
    isplitr
    · ipureintro; exact herr.1
    iexists _
    iframe Hperm Hn

end oscalls

end osfs_walfs
end EtcdGrove
end Perennial

end
