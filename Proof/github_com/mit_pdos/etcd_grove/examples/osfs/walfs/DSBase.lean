/-
What the proofs of `examples/osfs/walfs`'s `seglog.go` and `dirswap.go` share (over the file
extension's shared view): the data (`DSClaims.lean`), paths in a root directory, and the specs of
`readNames` (exact on the names of a claim the caller shows a fraction of) and `newData`.
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.DSClaims
public import Proof.os.NsS
public import Proof.os.Off
public import Proof.os.CrashWrite

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_walfs
namespace DSBase

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs
  github_com.mit_pdos.etcd_grove.examples.osfs.walfs

/-! ## The data and lists -/

theorem not_mem_take_of_nodup {α : Type} {l : List α} (h : l.Nodup) {i : Nat} {b : α}
    (hb : l[i]? = some b) : b ∉ l.take i := by
  intro hm
  obtain ⟨j, hj, hjb⟩ := List.getElem_of_mem hm
  have hji : j < i := by simp at hj; omega
  have hil : i < l.length := (List.getElem?_eq_some_iff.1 hb).1
  have hjl : j < l.length := by omega
  have e1 : l[j] = b := by rw [← hjb, List.getElem_take]
  have e2 : l[i] = b := (List.getElem?_eq_some_iff.1 hb).2
  exact List.pairwise_iff_getElem.1 h j i hjl hil hji (e1.trans e2.symm)

/-- The fractions of a metadata step: the caller's quarter and the invariant's half, and the call's
quarter. -/
theorem q_meta : ((1 : Qp).half.half + (1 : Qp).half) + (1 : Qp).half.half = 1 := by
  rw [Qp.ext_iff]; simp; grind

/-! ## Paths in a root -/

/-- A root names its directory. -/
theorem lookupH_root {R : Roots} (hR : RootsOk R) {r : GoString} {j : Ino} (hrj : (r, j) ∈ R)
    (V : Hist) : lookupH R V r = some (.dir j) := by
  have h := lookup_joinPath (st := Hist.st R V) hR hrj (cs := []) (by simp)
  simpa [joinPath, walk, lookupH] using h

/-- A name in a root: the root's directory's entry. -/
theorem lookupH_child_root {R : Roots} (hR : RootsOk R) {r : GoString} {j : Ino}
    (hrj : (r, j) ∈ R) (V : Hist) {b : GoString} (hb : NameOk b) :
    lookupH R V (child r b) = V.now.entry j b := by
  have h := lookup_child (st := Hist.st R V) hR (lookupH_root hR hrj V) hb
  rw [histSt_tree] at h
  exact h

/-- A name in a directory `J`: `J`'s entry. -/
theorem lookupH_child_dir {R : Roots} (hR : RootsOk R) {V : Hist} {d : GoString} {J : Ino}
    (hd : lookupH R V d = some (.dir J)) {b : GoString} (hb : NameOk b) :
    lookupH R V (child d b) = V.now.entry J b := by
  have h := lookup_child (st := Hist.st R V) hR hd hb
  rw [histSt_tree] at h
  exact h

/-! ## Bytes -/

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable [go.BasicIntoValInj]

theorem osBytes_take_drop' (i : Ino) (off n : Nat) (dq : DFrac) (bs : List ByteG)
    (hn : n ≤ bs.length) :
    osBytes (L := L) i off dq bs ⊣⊢
      osBytes (L := L) i off dq (bs.take n) ∗ osBytes (L := L) i (off + n) dq (bs.drop n) := by
  have A := bytesG_append (gooseOsGS (L := L)) i dq off (bs.take n) (bs.drop n)
  rw [List.take_append_drop, List.length_take, show min n bs.length = n by omega] at A
  exact A

end res

/-! ## `readNames` and `newData` -/

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.walfs.Assumptions]
variable [os.Assumptions] [go.BasicIntoValInj]

/-- `readNames(d)`, `d` the directory `j` (a spine to it), with a fraction of the call permission
and of a claim on names `N` of `j`: every name returned is valid, a name of `N` is returned iff it is
there, at most once; or `ok = false`. -/
theorem wp_readNamesS (d : GoString) (R : Roots) (j : Ino) (dq : DFrac) (qc : Qp) (N : NameSet)
    (dqn : DFrac) (h : NamesH) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osCallPerm (callKey R d) qc ∗
        osNames j N dqn h }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.readNames)) (Val #d))
    {{ (sl : GoSlice) (ok : Bool), RET (PairV #sl #ok); osPathS R d dq j ∗
        osCallPerm (callKey R d) qc ∗ osNames j N dqn h ∗
        (⌜ok = false⌝ ∨ ∃ names : List GoString, ⌜ok = true ∧ (∀ b ∈ names, NameOk b) ∧
          (∀ b, N.Mem b → ((h.cur !! b).isSome ↔ b ∈ names)) ∧
          (∀ b, N.Mem b → names.count b ≤ 1)⌝ ∗ sl ↦* names) }} := by
  wp_start as ⟨#Hinv, #Hsi, Hp, Hperm, Hn⟩
  (try wp_auto)
  wp_apply os.Open.wp_dirS d R j dq qc $$ [Hinv Hsi Hp Hperm] as %f %err ⟨Hp, Hperm, Hr⟩
  · iframe; isplitl [] <;> iassumption
  icases Hr with (⟨%fd, %herr, Hf, Hfd⟩ | %herr)
  rotate_left
  · obtain ⟨herr, rfl⟩ := herr
    cases err with
    | nil => exact absurd rfl herr
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    iframe
    ileft; ipureintro; rfl
  subst herr
  (try wp_auto)
  wp_apply os.File.Readdirnames.wp_dirS f fd d (DFrac.own 1) R j N dqn h _ (by decide)
    $$ [Hinv Hsi Hf Hfd Hn] as %sl %err ⟨Hf, Hn, Hr⟩
  · iframe; isplitl [] <;> iassumption
  icases Hr with (⟨%names, %hn, Hsl, Hfd⟩ | ⟨⟨%e, %he, Hpe⟩, %r0, %rs, Hfd⟩)
  · obtain ⟨rfl, hok, hmem, hcnt, -⟩ := hn
    (try wp_auto)
    wp_apply os.File.Close.wp_dirS f fd d j _ $$ [Hinv Hf Hfd] as %e -
    · iframe; iexact Hinv
    (try wp_auto)
    iapply HΦ
    iframe
    iright
    iexists names
    iframe
    ipureintro
    exact ⟨rfl, hok, hmem, hcnt⟩
  · (try wp_auto)
    wp_apply os.File.Close.wp_dirS f fd d j _ $$ [Hinv Hf Hfd] as %e' -
    · iframe; iexact Hinv
    icases os.errnoPathErr_ne err e $$ Hpe with %herr
    cases err with
    | nil => exact absurd rfl herr
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    iframe
    ileft; ipureintro; rfl

theorem wp_newData :
    {{ (True : IProp GF) }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.newData)) (Val #()))
    {{ (sl : GoSlice), RET #sl; sl ↦* dataC }} := by
  wp_start as -
  wp_auto
  wp_apply wp_slice_literal (V := w8) (l := dataC)
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hs, -⟩
  simp only [go.arrayLiteralSize, List.foldl, Int.reduceAdd]
  (try wp_auto)
  iapply HΦ
  iexact Hs

end proof

end DSBase
end osfs_walfs
end EtcdGrove
end Perennial

end
