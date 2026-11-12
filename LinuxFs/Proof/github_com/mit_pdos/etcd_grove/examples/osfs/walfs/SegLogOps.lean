/-
The proofs of `examples/osfs/walfs`'s `seglog.go` (one generation), part 1, over the file extension
v2: the crash invariant (half of the tree's history, for the crash: no condition on it is needed,
since a removal of `seg.log` leaves nothing there whatever it was), the calls that change the tree
with it opened, and the `os` calls on `dir/seg.log` (`dir` a root): `Remove`, and `OpenFile` (new,
existing, read-only), which also give the `*File`'s offset (`os.ownOff`).
-/
module

public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.DSBase

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

theorem q_open : (1 : Qp).half.half + (1 : Qp).half.half = (1 : Qp).half := Qp.half_add_half _

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

def logN : Namespace := nroot .@ "seglog"

theorem logN_disj : ↑osN ⊆ (⊤ : CoPset) \ ↑logN := mask_ndot_ne' nroot "osfs" "seglog" (by decide)

/-- **The crash invariant** of `seglog`: half of the tree's history. -/
def logInv (R : Roots) : IProp GF :=
  inv logN iprop(∃ V : Hist, osTree (L := L) (DFrac.own (1 : Qp).half) R V)

instance logInv_persistent (R : Roots) : Persistent (logInv (L := L) R) := by
  unfold logInv; infer_instance

end res

/-! ## The calls that change the tree, with the invariant -/

section steps
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [go.BasicIntoValInj]

/-- `unlink(2)` of `dir/seg.log` (`dir` the root of inode `j`) by the call `k`, the invariant opened
around it. -/
theorem wp_logUnlink (R : Roots) (hR : RootsOk R) (dir : GoString) (j : Ino) (hrj : (dir, j) ∈ R)
    (V : Hist) (k s : Nat) (Φ : val → IProp GF) :
    ⊢ osInv (GF := GF) -∗ logInv (GF := GF) R -∗
      osTree (GF := GF) (DFrac.own (1 : Qp).half.half) R V -∗
      osCall (GF := GF) k s (1 : Qp).half.half -∗
      (∀ (e : w64) (V' : Hist), ⌜UnlinkPost R V dir logB j e V'⌝ -∗
        osTree (GF := GF) (DFrac.own (1 : Qp).half) R V' -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Unlink" (Val (PairV (osTokV k) (#(child dir logB))))) {{ Φ }} := by
  iintro #Hos #Hinv Hh Hk HΦ
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑logN))
  unfold logInv
  imod inv_acc (E := ⊤) (show ↑logN ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
    with ⟨Hi, Hclose⟩
  icases Hi with ⟨%V1, >Hh1⟩
  icases tree_combine _ _ R R V V1 $$ Hh Hh1 with ⟨-, Hh⟩
  imodintro
  iapply wp_osUnlinkG dir logB j logB_ok R V _ _ k s q_meta (lookupH_root hR hrj V) logN_disj
    $$ Hos Hh Hk
  iintro %e %V' %hp Hh
  icases (tree_halves 1 R V').1 $$ Hh with ⟨Hh, Hh1⟩
  imod Hclose $$ [Hh1] with -
  · inext; iexists V'; iexact Hh1
  imodintro
  iapply HΦ $$ %e %V' %hp Hh

/-- `rmdir(2)` of `dir/seg.log` by the call `k`, the invariant opened around it. -/
theorem wp_logRmdir (R : Roots) (hR : RootsOk R) (dir : GoString) (j : Ino) (hrj : (dir, j) ∈ R)
    (V : Hist) (k s : Nat) (Φ : val → IProp GF) :
    ⊢ osInv (GF := GF) -∗ logInv (GF := GF) R -∗
      osTree (GF := GF) (DFrac.own (1 : Qp).half.half) R V -∗
      osCall (GF := GF) k s (1 : Qp).half.half -∗
      (∀ (e : w64) (V' : Hist), ⌜RmdirPost R V dir logB j e V'⌝ -∗
        osTree (GF := GF) (DFrac.own (1 : Qp).half) R V' -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Rmdir" (Val (PairV (osTokV k) (#(child dir logB))))) {{ Φ }} := by
  iintro #Hos #Hinv Hh Hk HΦ
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑logN))
  unfold logInv
  imod inv_acc (E := ⊤) (show ↑logN ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
    with ⟨Hi, Hclose⟩
  icases Hi with ⟨%V1, >Hh1⟩
  icases tree_combine _ _ R R V V1 $$ Hh Hh1 with ⟨-, Hh⟩
  imodintro
  iapply wp_osRmdirG dir logB j logB_ok R V _ _ k s q_meta (lookupH_root hR hrj V) logN_disj
    $$ Hos Hh Hk
  iintro %e %V' %hp Hh
  icases (tree_halves 1 R V').1 $$ Hh with ⟨Hh, Hh1⟩
  imod Hclose $$ [Hh1] with -
  · inext; iexists V'; iexact Hh1
  imodintro
  iapply HΦ $$ %e %V' %hp Hh

/-- `open(2)` with `O_RDWR | O_CREAT` of `dir/seg.log`, absent, by the call `k`, the invariant
opened around it. -/
theorem wp_logCreate (R : Roots) (hR : RootsOk R) (dir : GoString) (j : Ino) (hrj : (dir, j) ∈ R)
    (V : Hist) (hn : V.now.entry j logB = none) (k s : Nat) (Φ : val → IProp GF) :
    ⊢ osInv (GF := GF) -∗ logInv (GF := GF) R -∗
      osTree (GF := GF) (DFrac.own (1 : Qp).half.half) R V -∗
      osCall (GF := GF) k s (1 : Qp).half.half -∗
      (∀ fd : w64, ∀ e : w64,
        ((⌜e = 0 ∧ 0 ≤ fd.toInt⌝ ∗ ∃ i,
            osTree (GF := GF) (DFrac.own (1 : Qp).half) R (V.push ⟨.create j logB i, V.2.length⟩) ∗
            osMeta (GF := GF) i (DFrac.own 1) newMeta ∗ osFd (GF := GF) fd (DFrac.own 1) ⟨i, true, true⟩) ∨
         (⌜e ≠ 0 ∧ fd = -1⌝ ∗ (osTree (GF := GF) (DFrac.own (1 : Qp).half) R V ∨ ∃ i,
            osTree (GF := GF) (DFrac.own (1 : Qp).half) R (V.push ⟨.create j logB i, V.2.length⟩) ∗
            osMeta (GF := GF) i (DFrac.own 1) newMeta))) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp fsExt.name "Open"
        (Val (PairV (osTokV k) (PairV (#(child dir logB)) (#flCreat))))) {{ Φ }} := by
  iintro #Hos #Hinv Hh Hk HΦ
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑logN))
  unfold logInv
  imod inv_acc (E := ⊤) (show ↑logN ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
    with ⟨Hi, Hclose⟩
  icases Hi with ⟨%V1, >Hh1⟩
  icases tree_combine _ _ R R V V1 $$ Hh Hh1 with ⟨-, Hh⟩
  imodintro
  have hn' : lookupH R V (child dir logB) = none := by
    rw [lookupH_child_root hR hrj V logB_ok]; exact hn
  iapply wp_osOpenCreate dir logB R V _ _ k s j logB_ok (lookupH_root hR hrj V) hn' q_meta logN_disj
    $$ Hos Hh Hk
  iintro %fd %e %-  Hr
  icases Hr with (⟨%he, %i, Hh, Hm, Hfd⟩ | ⟨%he, (Hh | ⟨%i, Hh, Hm⟩)⟩)
  · icases (tree_halves 1 R _).1 $$ Hh with ⟨Hh, Hh1⟩
    imod Hclose $$ [Hh1] with -
    · inext; iexists _; iexact Hh1
    imodintro
    iapply HΦ
    ileft
    isplitr
    · ipureintro; exact he
    iexists i
    iframe
  · icases (tree_halves 1 R _).1 $$ Hh with ⟨Hh, Hh1⟩
    imod Hclose $$ [Hh1] with -
    · inext; iexists _; iexact Hh1
    imodintro
    iapply HΦ
    iright
    isplitr
    · ipureintro; exact he
    ileft; iexact Hh
  · icases (tree_halves 1 R _).1 $$ Hh with ⟨Hh, Hh1⟩
    imod Hclose $$ [Hh1] with -
    · inext; iexists _; iexact Hh1
    imodintro
    iapply HΦ
    iright
    isplitr
    · ipureintro; exact he
    iright
    iexists i
    iframe

end steps

/-! ## `os` calls on `seg.log` -/

section oscalls
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [go.BasicIntoValInj]
variable [sem : go.Semantics] [os.Assumptions] [os.file.FieldAssumptions]

theorem entry_push_remove (V : Hist) (j : Ino) (b : GoString) (n : Node) (s : Nat) :
    (V.push ⟨.remove j b n, s⟩).now.entry j b = none := by
  rw [Hist.push_now]
  simp only [MetaOp.apply]
  rw [entry_upd, if_pos rfl]
  simp

theorem entry_push_create (V : Hist) (j : Ino) (b : GoString) (i : Ino) (s : Nat) :
    (V.push ⟨.create j b i, s⟩).now.entry j b = some (.file i) := by
  rw [Hist.push_now]
  simp only [MetaOp.apply]
  rw [entry_upd, if_pos rfl]
  simp

/-- `os.Remove(dir/seg.log)`, `dir` the root of inode `j`: on success nothing is there. -/
theorem wp_removeLog (R : Roots) (hR : RootsOk R) (dir : GoString) (j : Ino) (hrj : (dir, j) ∈ R)
    (V : Hist) :
    {{ osInv (GF := GF) ∗ logInv (GF := GF) R ∗ osTree (GF := GF) (DFrac.own (1 : Qp).half) R V }}
      (App (Val (@! os.Remove)) (Val #(child dir logB)))
    {{ (err : GoInterface), RET #err; ∃ V', osTree (DFrac.own (1 : Qp).half) R V' ∗
        ⌜err = interface.nil → V'.now.entry j logB = none⌝ }} := by
  wp_start as ⟨#Hos, #Hinv, Hh⟩
  iloeb as IH generalizing %V Hh
  ihave Hh := tree_half (L := hG.goose_localGS) _ R V $$ Hh
  wp_apply wp_osCallBegin R V _ _ CoPset.subseteq_top $$ Hos Hh as %t Hh Hk
  (try wp_auto)
  wp_apply wp_logUnlink R hR dir j hrj V t _ $$ Hos Hinv Hh Hk as %e %V' %hres Hh
  by_cases he4 : e = W64 4
  · rw [decide_eq_true he4]
    wp_auto
    iapply IH $$ %V' Hh HΦ
  rw [decide_eq_false he4]
  wp_auto
  by_cases he0 : e = W64 0
  · rw [decide_eq_true he0]
    wp_auto
    iapply HΦ
    iexists V'
    iframe Hh
    ipureintro; intro _
    rcases hres with ⟨i, -, ⟨-, rfl⟩ | ⟨h, -⟩⟩ | ⟨h, -⟩
    · exact entry_push_remove _ _ _ _ _
    · exact absurd he0 h
    · exact absurd he0 h
  rw [decide_eq_false he0]
  wp_auto
  clear hres
  iloeb as IH2 generalizing %V' Hh
  ihave Hh := tree_half (L := hG.goose_localGS) _ R V' $$ Hh
  wp_apply wp_osCallBegin R V' _ _ CoPset.subseteq_top $$ Hos Hh as %t1 Hh Hk
  (try wp_auto)
  wp_apply wp_logRmdir R hR dir j hrj V' t1 _ $$ Hos Hinv Hh Hk as %e1 %V2 %hres1 Hh
  by_cases he14 : e1 = W64 4
  · rw [decide_eq_true he14]
    wp_auto
    iapply IH2 $$ %V2 Hh HΦ
  rw [decide_eq_false he14]
  wp_auto
  by_cases he10 : e1 = W64 0
  · rw [decide_eq_true he10]
    wp_auto
    iapply HΦ
    iexists V2
    iframe Hh
    ipureintro; intro _
    rcases hres1 with ⟨J, -, -, ⟨-, rfl⟩ | ⟨h, -⟩⟩ | ⟨h, -⟩
    · exact entry_push_remove _ _ _ _ _
    · exact absurd he10 h
    · exact absurd he10 h
  rw [decide_eq_false he10]
  wp_auto
  unfold os.model.pathError
  by_cases h20 : e1 = W64 20
  · rw [decide_eq_true h20]
    wp_auto
    wp_apply wp_errno
    iapply HΦ
    iexists V2
    iframe Hh
    ipureintro; intro h; cases h
  · rw [decide_eq_false h20]
    wp_auto
    wp_apply wp_errno
    iapply HΦ
    iexists V2
    iframe Hh
    ipureintro; intro h; cases h

/-- What a retried `open(2)` with `O_CREAT` of `seg.log` sees: nothing there, or the file it made
(whose `OsMeta` the caller holds). -/
def crStateL (R : Roots) (V : Hist) (j : Ino) : Option Ino → IProp GF
  | none => osTree (GF := GF) (DFrac.own (1 : Qp).half) R V
  | some i => iprop(osTree (GF := GF) (DFrac.own (1 : Qp).half) R
      (V.push ⟨.create j logB i, V.2.length⟩) ∗ osMeta (GF := GF) i (DFrac.own 1) newMeta)

/-- `os.OpenFile(dir/seg.log, O_RDWR|O_CREATE, perm)`, `seg.log` absent: on success a new file of a
fresh inode `i`, `seg.log` names it. -/
theorem wp_openLog (R : Roots) (hR : RootsOk R) (dir : GoString) (j : Ino) (hrj : (dir, j) ∈ R)
    (V : Hist) (hn : V.now.entry j logB = none) (perm : w32) :
    {{ osInv (GF := GF) ∗ logInv (GF := GF) R ∗ osTree (GF := GF) (DFrac.own (1 : Qp).half) R V }}
      (App (App (App (Val (@! os.OpenFile)) (Val #(child dir logB))) (Val #(W64 66))) (Val #perm))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err);
        ((∃ (fd : w64) (i : Ino) (V' : Hist), ⌜err = interface.nil ∧ 0 ≤ fd.toInt ∧
              V'.now.entry j logB = some (.file i)⌝ ∗
            os.ownFile f fd (child dir logB) (DFrac.own 1) ∗ os.ownOff f (W64 0) ∗
            osFd fd (DFrac.own 1) ⟨i, true, true⟩ ∗ osMeta i (DFrac.own 1) newMeta ∗
            osTree (DFrac.own (1 : Qp).half) R V') ∨
         (⌜err ≠ interface.nil⌝ ∗ ∃ V', osTree (DFrac.own (1 : Qp).half) R V')) }} := by
  wp_start as ⟨#Hos, #Hinv, Hh⟩
  obtain ⟨ko, hko⟩ : ∃ ko : Option Ino, ko = none := ⟨_, rfl⟩
  ihave Hs : crStateL R V j ko $$ [Hh]
  · subst hko; unfold crStateL; iexact Hh
  clear hko
  iloeb as IH generalizing %ko Hs
  rw [os.file_ty_eq, os.File_ty_eq]
  cases ko with
  | none =>
    unfold crStateL
    ihave Hh := tree_half (L := hG.goose_localGS) _ R V $$ Hs
    wp_apply wp_osCallBegin R V _ _ CoPset.subseteq_top $$ Hos Hh as %t Hh Hk
    rw [show (W64 66 ||| W64 524288) = flCreat from by decide]
    (try wp_auto)
    wp_apply wp_logCreate R hR dir j hrj V hn t _ $$ Hos Hinv Hh Hk as %fd %e Hr
    icases Hr with (⟨%he, %i, Hh, Hm, Hfd⟩ | ⟨%he, Hst⟩)
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
      iexists fd, i, _
      iframe Hfd Hm Hh
      isplitr
      · ipureintro; exact ⟨rfl, hfd0, entry_push_create _ _ _ _ _⟩
      unfold os.ownFile os.ownOff
      isplitr [off]
      · iexists inner_ptr
        iframe
        isplitl [] <;> iassumption
      · iexists inner_ptr
        iframe
        iassumption
    · obtain ⟨he0, rfl⟩ := he
      rw [decide_eq_false (show ¬ e = W64 0 from he0)]
      wp_auto
      by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        wp_auto
        try rw [os.file_ty_eq]
        try rw [os.File_ty_eq]
        icases Hst with (Hh | ⟨%i, Hh, Hm⟩)
        · iapply IH $$ %none Hh HΦ
        · iapply IH $$ %(some i) [Hh Hm] HΦ
          simp only [crStateL]; iframe
      · rw [decide_eq_false he4]
        wp_auto
        unfold os.model.pathError
        wp_apply wp_errno
        iapply HΦ
        iright
        isplitr
        · ipureintro; intro h; cases h
        icases Hst with (Hh | ⟨%i, Hh, -⟩)
        · iexists _; iexact Hh
        · iexists _; iexact Hh
  | some i =>
    unfold crStateL
    icases Hs with ⟨Hh, Hm⟩
    ihave Hh := tree_half (L := hG.goose_localGS) _ R _ $$ Hh
    wp_apply wp_osCallBegin R _ _ _ CoPset.subseteq_top $$ Hos Hh as %t Hh Hk
    rw [show (W64 66 ||| W64 524288) = W64 0x80042 from by decide]
    (try wp_auto)
    have hl : lookupH R (V.push ⟨.create j logB i, V.2.length⟩) (child dir logB) =
        some (.file i) := by
      rw [lookupH_child_root hR hrj _ logB_ok]; exact entry_push_create _ _ _ _ _
    wp_apply wp_osOpenFile (child dir logB) (W64 0x80042) R _ _ _ t _ i
      (by simp only [OpenFlagsOk, O_CREAT, O_TRUNC, O_CLOEXEC]; decide) (by decide) hl
      CoPset.subseteq_top $$ Hos Hh Hk as %fd %e %hres Hh Hfd
    ihave Hh := tree_unhalf (L := hG.goose_localGS) _ R _ $$ Hh
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
      iexists fd, i, _
      iframe Hfd Hm Hh
      isplitr
      · ipureintro; exact ⟨rfl, hfd0, entry_push_create _ _ _ _ _⟩
      unfold os.ownFile os.ownOff
      isplitr [off]
      · iexists inner_ptr
        iframe
        isplitl [] <;> iassumption
      · iexists inner_ptr
        iframe
        iassumption
    · rw [decide_eq_false he0]
      iclear Hfd
      wp_auto
      by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        wp_auto
        try rw [os.file_ty_eq]
        try rw [os.File_ty_eq]
        iapply IH $$ %(some i) [Hh Hm] HΦ
        simp only [crStateL]; iframe
      · rw [decide_eq_false he4]
        wp_auto
        unfold os.model.pathError
        wp_apply wp_errno
        iapply HΦ
        iright
        isplitr
        · ipureintro; intro h; cases h
        iexists _; iexact Hh

/-- `os.OpenFile(p, flags, perm)` (no `O_TRUNC`) of the existing file `i`, with a fraction of the
history, the fd's mode `openFd i flags`: an fd, with the offset 0, or an error; the history back. -/
theorem wp_openExisting (p : GoString) (fl : w64) (hfl : OpenFlagsOk (fl ||| W64 524288).toNat)
    (htr : (fl ||| W64 524288).toNat / O_TRUNC % 2 = 0) (q : Qp) (R : Roots) (V : Hist) (i : Ino)
    (hl : lookupH R V p = some (.file i)) (perm : w32) :
    {{ osInv (GF := GF) ∗ osTree (GF := GF) (DFrac.own q) R V }}
      (App (App (App (Val (@! os.OpenFile)) (Val #p)) (Val #fl)) (Val #perm))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osTree (DFrac.own q) R V ∗
        ((∃ fd : w64, ⌜err = interface.nil ∧ 0 ≤ fd.toInt⌝ ∗ os.ownFile f fd p (DFrac.own 1) ∗
            os.ownOff f (W64 0) ∗ osFd fd (DFrac.own 1) (openFd i (fl ||| W64 524288))) ∨
         ⌜err ≠ interface.nil⌝) }} := by
  wp_start as ⟨#Hos, Hh⟩
  iloeb as IH generalizing Hh HΦ
  ihave Hh := tree_half (L := hG.goose_localGS) q R V $$ Hh
  wp_apply wp_osCallBegin R V q.half q.half CoPset.subseteq_top $$ Hos Hh as %t Hh Hk
  rw [os.file_ty_eq, os.File_ty_eq]
  (try wp_auto)
  wp_apply wp_osOpenFile p (fl ||| W64 524288) R V q.half q.half t _ i hfl htr hl
    CoPset.subseteq_top $$ Hos Hh Hk as %fd %e %hres Hh Hfd
  ihave Hh := tree_unhalf (L := hG.goose_localGS) q R V $$ Hh
  by_cases he0 : e = W64 0
  · subst he0
    rw [decide_eq_true rfl]
    ihave Hfd := (show (if W64 0 = (0 : w64) then osFd (GF := GF) fd (DFrac.own 1)
        (openFd i (fl ||| W64 524288)) else emp) ⊢ osFd fd (DFrac.own 1) (openFd i (fl ||| W64 524288))
      by split
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
    iframe Hfd
    isplitr
    · ipureintro; exact ⟨rfl, hfd0⟩
    unfold os.ownFile os.ownOff
    isplitr [off]
    · iexists inner_ptr
      iframe
      isplitl [] <;> iassumption
    · iexists inner_ptr
      iframe
      iassumption
  · rw [decide_eq_false he0, if_neg (show ¬ e = (0 : w64) from he0)]
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
      ipureintro; intro h; cases h

end oscalls

end osfs_walfs
end EtcdGrove
end Perennial

end
