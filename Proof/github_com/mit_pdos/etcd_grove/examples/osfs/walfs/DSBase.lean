/-
What the proofs of `examples/osfs/walfs`'s `seglog.go` and `dirswap.go` share (over the file
extension v2): the data, paths in a root directory, the history's fractions, and the specs of
`readNames` and `newData`.
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs
public import Proof.os.Ns
public import Proof.os.Off
public import Proof.os.CrashFile
public import GooseLang.Ext.Fs.TreeSpecsMeta

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

/-- The data of a committed segment (`newData`). -/
def dataC : List w8 := [W8 0xde, W8 0xad, W8 0xbe, W8 0xef, W8 0x01, W8 0x23, W8 0x45, W8 0x67]

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

/-! ## The history's fractions -/

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt fsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable [go.BasicIntoValInj]

theorem tree_agree (dq1 dq2 : DFrac) (R R' : Roots) (V V' : Hist) :
    ⊢ osTree (L := L) dq1 R V -∗ osTree (L := L) dq2 R' V' -∗ ⌜R = R' ∧ V = V'⌝ := by
  unfold osTree; iintro A B
  icases gElem_valid_2 _ _ _ _ _ _ _ $$ A B with %hv
  ipureintro
  simp only [Prod.mk.injEq] at hv
  exact hv.2

theorem tree_halves (q : Qp) (R : Roots) (V : Hist) :
    osTree (L := L) (DFrac.own q) R V ⊣⊢
      osTree (L := L) (DFrac.own q.half) R V ∗ osTree (L := L) (DFrac.own q.half) R V := by
  have h := osTree_split (L := L) q.half q.half R V
  rw [Qp.half_add_half] at h
  exact h

theorem tree_combine (q1 q2 : Qp) (R R' : Roots) (V V' : Hist) :
    ⊢ osTree (L := L) (DFrac.own q1) R V -∗ osTree (L := L) (DFrac.own q2) R' V' -∗
      ⌜R = R' ∧ V = V'⌝ ∗ osTree (L := L) (DFrac.own (q1 + q2)) R V := by
  iintro A B
  icases tree_agree _ _ R R' V V' $$ A B with %h
  obtain ⟨rfl, rfl⟩ := h
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  ihave H := (osTree_split (L := L) q1 q2 R V).2 $$ [A B]
  · iframe
  iexact H

theorem tree_unhalf (q : Qp) (R : Roots) (V : Hist) :
    osTree (L := L) (DFrac.own (q.half + q.half)) R V ⊢ osTree (L := L) (DFrac.own q) R V := by
  rw [Qp.half_add_half]

theorem tree_half (q : Qp) (R : Roots) (V : Hist) :
    osTree (L := L) (DFrac.own q) R V ⊢ osTree (L := L) (DFrac.own (q.half + q.half)) R V := by
  rw [Qp.half_add_half]

theorem osBytes_take_drop' (i : Ino) (off n : Nat) (dq : DFrac) (bs : List (w8 × Bool))
    (hn : n ≤ bs.length) :
    osBytes (L := L) i off dq bs ⊣⊢
      osBytes (L := L) i off dq (bs.take n) ∗ osBytes (L := L) i (off + n) dq (bs.drop n) := by
  have A := bytesG_append (gooseOsGS (L := L)) i dq off (bs.take n) (bs.drop n)
  rw [List.take_append_drop, List.length_take, show min n bs.length = n by omega] at A
  exact A

/-- A directory's view given back (`rdBack`), with the rest of the history: the history. -/
theorem tree_back (q1 q2 : Qp) (R : Roots) (V : Hist) (x : Ino × DirPh) (hq : x.2.q = q2) :
    ⊢ osTree (L := L) (DFrac.own q1) R V -∗ rdBack (L := L) x -∗
      osTree (L := L) (DFrac.own (q1 + q2)) R V := by
  subst hq
  iintro A B
  unfold rdBack osDir
  icases B with ⟨%R', %V', B, -⟩
  icases tree_combine q1 x.2.q R R' V V' $$ A B with ⟨-, H⟩
  iexact H

end res

/-! ## `readNames` and `newData` -/

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.walfs.Assumptions]
variable [os.Assumptions] [os.file.FieldAssumptions] [go.BasicIntoValInj]

/-- `readNames(d)`, `d` the directory `j`, with a fraction of the history: the names of `j` now,
each once, or `ok = false`. -/
theorem wp_readNamesT (d : GoString) (q : Qp) (R : Roots) (V : Hist) (j : Ino)
    (hl : lookupH R V d = some (.dir j)) :
    {{ osInv (GF := GF) ∗ osTree (GF := GF) (DFrac.own q) R V }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.readNames)) (Val #d))
    {{ (sl : GoSlice) (ok : Bool), RET (PairV #sl #ok); osTree (DFrac.own q) R V ∗
        (⌜ok = false⌝ ∨ ∃ names : List GoString, ⌜ok = true ∧ names.Nodup ∧
          ∀ b, b ∈ names ↔ (V.now.entry j b).isSome⌝ ∗ sl ↦* names) }} := by
  wp_start as ⟨#Hinv, Hh⟩
  ihave Hh := tree_half (L := hG.goose_localGS) q R V $$ Hh
  (try wp_auto)
  wp_apply os.Open.wp_dir d q.half q.half R V j hl $$ [Hinv Hh] as %f %err Hr
  · iframe; iexact Hinv
  icases Hr with (⟨%fd, %herr, Hf, Hh, Hfd⟩ | ⟨%herr, Hh⟩)
  rotate_left
  · obtain ⟨herr, rfl⟩ := herr
    cases err with
    | nil => exact absurd rfl herr
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    isplitl [Hh]
    · iapply tree_unhalf; iexact Hh
    ileft; ipureintro; rfl
  subst herr
  (try wp_auto)
  wp_apply os.File.Readdirnames.wp_dir f fd d (DFrac.own 1) j q.half (dview V j) _ (by decide)
    $$ [Hinv Hf Hfd] as %sl %err ⟨Hf, Hr⟩
  · iframe; iexact Hinv
  icases Hr with (⟨%names, %hn, Hsl, Hfd⟩ | ⟨%herr, %rs, Hfd⟩)
  · obtain ⟨rfl, hnd, hmem⟩ := hn
    (try wp_auto)
    wp_apply os.File.Close.wp_dir f fd d (j, .done (dview V j) q.half) $$ [Hinv Hf Hfd] as %e Hb
    · iframe; iexact Hinv
    ihave Hh := tree_back (L := hG.goose_localGS) q.half q.half R V _ rfl $$ Hh Hb
    (try wp_auto)
    iapply HΦ
    isplitl [Hh]
    · iapply tree_unhalf; iexact Hh
    iright
    iexists names
    iframe
    ipureintro
    refine ⟨rfl, hnd, fun b => ?_⟩
    rw [hmem, dview_now, entsOf_lookup]
  · (try wp_auto)
    wp_apply os.File.Close.wp_dir f fd d (j, .reading rs (dview V j) q.half) $$ [Hinv Hf Hfd]
      as %e Hb
    · iframe; iexact Hinv
    ihave Hh := tree_back (L := hG.goose_localGS) q.half q.half R V _ rfl $$ Hh Hb
    cases err with
    | nil => exact absurd rfl herr
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    isplitl [Hh]
    · iapply tree_unhalf; iexact Hh
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
