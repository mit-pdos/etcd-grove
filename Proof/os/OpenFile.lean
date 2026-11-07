/-
The proof of `Spec/os/OpenFile.lean`: the model's `EINTR` loop, by Löb induction, each attempt a
`CallBegin` (half of the caller's fraction of the history to the call) and the extension's `Open`
(`wp_osOpenFile`, `wp_osOpenCreate`); the `file` it allocates needs `file.FieldAssumptions`
(`TrustedCode/os.lean`). A create that failed with its effect leaves the file named, so the next
attempt opens it (`lookupH_create`).
-/
module

public import Spec.os.OpenFile

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

/-- A walk that succeeds never took the entry `b` of `j`, which is absent: adding it changes
nothing. -/
theorem walk_upd_insert {m : Tree} {j : Ino} {b : GoString} {v : Node} (hn : m.entry j b = none) :
    ∀ (cs : List GoString) (n x : Node), walk m n cs = some x →
      walk (m.upd j (fun d => <[b := v]> d)) n cs = some x
  | [], n, x, h => h
  | c :: cs, n, x, h => by
    cases n with
    | file _ => simp [walk] at h
    | dir j' =>
      simp only [walk] at h ⊢
      have he : (m.upd j (fun d => <[b := v]> d)).entry j' c = m.entry j' c := by
        rw [entry_upd]
        split
        · rename_i hj
          subst hj
          by_cases hc : b = c
          · subst hc; rw [hn] at h; cases h
          · rw [GMap.lookup_insert_ne _ _ hc, getD_lookup]; rfl
        · rfl
      rw [he]
      cases hm : m.entry j' c with
      | none => rw [hm] at h; cases h
      | some n' =>
        rw [hm] at h
        exact walk_upd_insert hn cs n' x h

/-- After a create of `b` in the directory `j` that `d` names (nothing at `d/b` before), `d/b`
names the new file. -/
theorem lookupH_create {R : Roots} {V : Hist} {d b : GoString} {j i : Ino} (s : Nat)
    (hr : RootsOk R) (hd : lookupH R V d = some (.dir j)) (hb : NameOk b)
    (hn : lookupH R V (child d b) = none) :
    lookupH R (V.push ⟨.create j b i, s⟩) (child d b) = some (.file i) := by
  have ht : (Hist.st R (V.push ⟨.create j b i, s⟩)).tree =
      (Hist.st R V).tree.upd j (fun dd => <[b := Node.file i]> dd) := by
    show (V.push _).now = _
    rw [Hist.push_now]; rfl
  have hen : (Hist.st R V).tree.entry j b = none := by
    rw [← lookup_child (st := Hist.st R V) hr hd hb]; exact hn
  have hd' : lookupH R (V.push ⟨.create j b i, s⟩) d = some (.dir j) := by
    obtain ⟨r, j0, cs, hrj, hcs, hp, hw⟩ := lookup_some (st := Hist.st R V) hd
    unfold lookupH
    rw [hp, lookup_joinPath (st := Hist.st R (V.push _)) hr hrj hcs, ht]
    exact walk_upd_insert hen cs _ _ hw
  unfold lookupH
  rw [lookup_child (st := Hist.st R (V.push _)) hr hd' hb, ht, entry_upd, if_pos rfl]
  exact GMap.lookup_insert _ _ _

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions] [os.file.FieldAssumptions]

theorem openFd_rw (i : Ino) : openFd i (W64 0x80042) = ⟨i, true, true⟩ := by
  simp [openFd, O_WRONLY, O_RDONLY]

theorem osTree_halves (q : Qp) (R : Roots) (V : Hist) :
    osTree (GF := GF) (DFrac.own q) R V ⊣⊢ osTree (DFrac.own (q.half + q.half)) R V := by
  rw [Qp.half_add_half]; exact BIBase.BiEntails.rfl

/-- One attempt on an existing file: a `CallBegin`, then `Open`. -/
theorem os.OpenFile.wp_proof : os.OpenFile.spec (GF := GF) (hG := hG) := by
  intro path perm q R V i hl
  wp_start as ⟨#Hinv, Hh⟩
  iloeb as IH generalizing Hh HΦ
  ihave Hh := (osTree_halves q R V).1 $$ Hh
  wp_apply wp_osCallBegin R V q.half q.half CoPset.subseteq_top $$ Hinv Hh as %t Hh Hk
  rw [os.file_ty_eq, os.File_ty_eq,
    show (W64 66 ||| W64 524288) = W64 0x80042 from by decide]
  (try wp_auto)
  wp_apply wp_osOpenFile path (W64 0x80042) R V q.half q.half t _ i
    (by simp only [OpenFlagsOk, O_CREAT, O_TRUNC, O_CLOEXEC]; decide) (by decide) hl
    CoPset.subseteq_top $$ Hinv Hh Hk as %fd %e %hres Hh Hfd
  ihave Hh := (osTree_halves q R V).2 $$ Hh
  by_cases he0 : e = W64 0
  · subst he0
    rw [decide_eq_true rfl]
    ihave Hfd := (show (if W64 0 = (0 : w64) then osFd (GF := GF) fd (DFrac.own 1)
        (openFd i (W64 0x80042)) else emp) ⊢ osFd fd (DFrac.own 1) ⟨i, true, true⟩
      by rw [openFd_rw]; split
         · iintro H; iexact H
         · exact absurd rfl ‹_›) $$ Hfd
    wp_auto
    iStructNamed inner
    iapply wp_fupd
    wp_auto
    ipersist name
    ipersist f
    imodintro
    have hfd0 : 0 ≤ fd.toInt := by rcases hres with ⟨-, h⟩ | ⟨h, -⟩; exact h; exact absurd rfl h
    iapply HΦ
    iframe Hh
    ileft
    iexists fd
    iframe
    isplitr
    · ipureintro; exact ⟨rfl, hfd0⟩
    unfold os.ownFile
    iexists inner_ptr
    iframe
    isplitl [] <;> iassumption
  · rw [decide_eq_false he0]
    iclear Hfd
    wp_auto
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      try rw [os.file_ty_eq]
      try rw [os.File_ty_eq]
      iapply IH $$ Hh HΦ
    · rw [decide_eq_false he4]
      wp_auto
      unfold os.model.pathError
      wp_apply wp_errno
      iapply HΦ
      iframe Hh
      iright
      ipureintro; exact ⟨(fun h => by cases h), rfl⟩

/-- What a retried create sees: nothing at `d/b`, or the file it made (whose `OsMeta` the
caller holds). -/
def crSt (R : Roots) (V : Hist) (j : Ino) (b : GoString) : Option Ino → IProp GF
  | none => osTree (GF := GF) (DFrac.own 1) R V
  | some i => iprop(⌜RootsOk R⌝ ∗
      osTree (GF := GF) (DFrac.own 1) R (V.push ⟨.create j b i, V.2.length⟩) ∗
      osMeta (GF := GF) i (DFrac.own 1) newMeta)

theorem os.OpenFile.wp_proofCreate : os.OpenFile.specCreate (GF := GF) (hG := hG) := by
  intro d b perm R V j hb hd hn
  wp_start as ⟨#Hinv, Hh⟩
  obtain ⟨o, ho⟩ : ∃ o : Option Ino, o = none := ⟨none, rfl⟩
  ihave Hh := (show osTree (GF := GF) (DFrac.own 1) R V ⊢ crSt R V j b o by
    rw [ho]; exact .rfl) $$ Hh
  clear ho
  iloeb as IH generalizing %o Hh HΦ
  cases o with
  | none =>
    unfold crSt
    ihave Hh := (osTree_halves 1 R V).1 $$ Hh
    wp_apply wp_osCallBegin R V (1 : Qp).half (1 : Qp).half CoPset.subseteq_top $$ Hinv Hh as %t Hh Hk
    rw [os.file_ty_eq, os.File_ty_eq,
      show (W64 66 ||| W64 524288) = flCreat from by decide]
    (try wp_auto)
    wp_apply wp_osOpenCreate d b R V (1 : Qp).half (1 : Qp).half t _ j hb hd hn
      (Qp.half_add_half 1) CoPset.subseteq_top $$ Hinv Hh Hk as %fd %e %hr Hres
    icases Hres with (⟨%he, %i, Hh, Hm, Hfd⟩ | ⟨%he, Hst⟩)
    · obtain ⟨rfl, hfd0⟩ := he
      rw [decide_eq_true (show (0 : w64) = W64 0 from rfl)]
      wp_auto
      iStructNamed inner
      iapply wp_fupd
      wp_auto
      ipersist name
      ipersist f
      imodintro
      iapply HΦ
      ileft
      iexists fd, i
      iframe
      isplitr
      · ipureintro; exact ⟨rfl, hfd0⟩
      unfold os.ownFile
      iexists inner_ptr
      iframe
      isplitl [] <;> iassumption
    · obtain ⟨he0, rfl⟩ := he
      rw [decide_eq_false (show e ≠ W64 0 from he0)]
      wp_auto
      by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        wp_auto
        try rw [os.file_ty_eq]
        try rw [os.File_ty_eq]
        icases Hst with (Hh | ⟨%i, Hh, Hm⟩)
        · iapply IH $$ %none Hh HΦ
        · iapply IH $$ %(some i) [Hh Hm] HΦ
          simp only; isplitr
          · ipureintro; exact hr
          isplitl [Hh] <;> iassumption
      · rw [decide_eq_false he4]
        wp_auto
        unfold os.model.pathError
        wp_apply wp_errno
        iapply HΦ
        iright
        iframe Hst
        ipureintro; exact ⟨(fun h => by cases h), rfl⟩
  | some i =>
    unfold crSt
    icases Hh with ⟨%hr, Hh, Hm⟩
    have hl := lookupH_create (i := i) V.2.length hr hd hb hn
    ihave Hh := (osTree_halves 1 R _).1 $$ Hh
    wp_apply wp_osCallBegin R _ (1 : Qp).half (1 : Qp).half CoPset.subseteq_top $$ Hinv Hh
      as %t Hh Hk
    rw [os.file_ty_eq, os.File_ty_eq,
      show (W64 66 ||| W64 524288) = W64 0x80042 from by decide]
    (try wp_auto)
    wp_apply wp_osOpenFile (child d b) (W64 0x80042) R _ (1 : Qp).half (1 : Qp).half t _ i
      (by simp only [OpenFlagsOk, O_CREAT, O_TRUNC, O_CLOEXEC]; decide) (by decide) hl
      CoPset.subseteq_top $$ Hinv Hh Hk as %fd %e %hres Hh Hfd
    ihave Hh := (osTree_halves 1 R _).2 $$ Hh
    by_cases he0 : e = W64 0
    · subst he0
      rw [decide_eq_true rfl]
      ihave Hfd := (show (if W64 0 = (0 : w64) then osFd (GF := GF) fd (DFrac.own 1)
          (openFd i (W64 0x80042)) else emp) ⊢ osFd fd (DFrac.own 1) ⟨i, true, true⟩
        by rw [openFd_rw]; split
           · iintro H; iexact H
           · exact absurd rfl ‹_›) $$ Hfd
      wp_auto
      iStructNamed inner
      iapply wp_fupd
      wp_auto
      ipersist name
      ipersist f
      imodintro
      have hfd0 : 0 ≤ fd.toInt := by rcases hres with ⟨-, h⟩ | ⟨h, -⟩; exact h; exact absurd rfl h
      iapply HΦ
      ileft
      iexists fd, i
      iframe
      isplitr
      · ipureintro; exact ⟨rfl, hfd0⟩
      unfold os.ownFile
      iexists inner_ptr
      iframe
      isplitl [] <;> iassumption
    · rw [decide_eq_false he0]
      iclear Hfd
      wp_auto
      by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        wp_auto
        try rw [os.file_ty_eq]
        try rw [os.File_ty_eq]
        iapply IH $$ %(some i) [Hh Hm] HΦ
        simp only; isplitr
        · ipureintro; exact hr
        isplitl [Hh] <;> iassumption
      · rw [decide_eq_false he4]
        wp_auto
        unfold os.model.pathError
        wp_apply wp_errno
        iapply HΦ
        iright
        isplitr
        · ipureintro; exact ⟨(fun h => by cases h), rfl⟩
        iright
        iexists i
        iframe

end proof

end EtcdGrove
end Perennial
