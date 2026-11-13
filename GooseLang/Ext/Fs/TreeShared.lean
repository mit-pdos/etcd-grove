/-
**The shared mode of the tree: its API** (`notes/wal-fsext-i2-design.md`; its "Review and decisions"
and "Implementation log"). Concurrent metadata calls, each holding a fraction of a call permission
(`osCallPerm`); shared directory fds that hold nothing (`osDirFdS`); region ownership by name claims
(`osNames j N dq h`: the names `N` of the directory `j`, with what is known of them, `NamesH`); the
log's length and entries as persistent facts (`osLogLb`, `osLogEnt`); the mode switch
(`wp_osShare`); the extension-level specs of the shared mode; what a region concludes of a crash
(`crashRest_region`). Untrusted.

The resources (all of the generation's ghost state):
* `osSharedInv R`: the shared mode's invariant, on the roots `R`: the shared history, the claims'
  authority (`NamesCoh`: each claim's history is the history's, the claims of a directory are
  disjoint and cover its names), the log's length and entries. Every shared spec takes it, with
  `↑osShN ⊆ E`.
* `osNames j N dq h`: a claim. Whole, its holder may change those names (with a call that began
  after their last change, `h.next ≤ s`); a fraction keeps them from changing (a spine).
* `osPathS R p dq j`: the path `p` leads to the directory `j`: fractions of the claims on each of
  its components.
* `osCallPerm q`, `osCallS t s q`: a fraction of the call permission; the call `t` in flight, begun
  at the log's length `s`, holding `q` of the permission. A directory operation (`mkdir`, `rmdir`,
  a directory's rename) needs a call holding all of it (`DirOpExcl`).
* `osLogLb n`, `osLogEnt x e`: the log has at least `n` entries; its entry `x` is `e` (persistent).
* `osDirFdS fd j ph`: the shared directory fd `fd`, on the directory `j`, its read at `ph`.

Statements only for now: every proof is `sorry` (filled in `TreeShared*.lean` as they come).
-/
module

public import GooseLang.Ext.Fs.TreeCrashCommit
public import GooseLang.Ext.Fs.TreeSpecsOpen
public import GooseLang.Ext.Fs.TreeSpecsMeta
public import GooseLang.Ext.Fs.TreeCutProof
public import GooseLang.Ext.Fs.TreeSharedSwitch
public import GooseLang.Ext.Fs.TreeSharedCrash

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode


/-! ## The laws of the resources (fancy updates in the shared invariant) -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

theorem osCallPerm_split (q1 q2 : Qp) :
    osCallPerm (L := L) (q1 + q2) ⊣⊢ osCallPerm (L := L) q1 ∗ osCallPerm (L := L) q2 := by
  unfold osCallPerm; exact gElem_split _ _ _ q1 q2 ()

theorem osCallPerm_valid (q : Qp) : osCallPerm (L := L) q ⊢ ⌜q ≤ 1⌝ := by
  sorry

theorem osNames_frac (j : Ino) (N : NameSet) (q1 q2 : Qp) (h : NamesH) :
    osNames (L := L) j N (DFrac.own (q1 + q2)) h ⊣⊢
      osNames (L := L) j N (DFrac.own q1) h ∗ osNames (L := L) j N (DFrac.own q2) h := by
  unfold osNames; exact gElem_split _ _ _ q1 q2 h

theorem osNames_agree (j : Ino) (N : NameSet) (dq1 dq2 : DFrac) (h1 h2 : NamesH) :
    osNames (L := L) j N dq1 h1 -∗ osNames (L := L) j N dq2 h2 -∗ ⌜h1 = h2⌝ := by
  unfold osNames
  iintro H1 H2
  icases gElem_valid_2 _ _ _ _ _ _ _ $$ H1 H2 with %hv
  ipureintro; exact hv.2

/-- Splitting a claim along a finite set of names `M`. -/
theorem osNames_split (R : Roots) (j : Ino) (N : NameSet) (M : List GoString) (h : NamesH)
    (hE : ↑osShN ⊆ E) :
    osSharedInv (L := L) R -∗ osNames (L := L) j N (DFrac.own 1) h ={E}=∗
      osNames (L := L) j (N.inter M) (DFrac.own 1) (h.restrict j (N.inter M)) ∗
      osNames (L := L) j (N.diff M) (DFrac.own 1) (h.restrict j (N.diff M)) := by
  sorry

/-- Two claims of a directory merged, as a set with their names (`N''`). -/
theorem osNames_merge (R : Roots) (j : Ino) (N N' N'' : NameSet) (h h' : NamesH)
    (hN : ∀ b, N''.Mem b ↔ N.Mem b ∨ N'.Mem b) (hE : ↑osShN ⊆ E) :
    osSharedInv (L := L) R -∗ osNames (L := L) j N (DFrac.own 1) h -∗
      osNames (L := L) j N' (DFrac.own 1) h' ={E}=∗
      ∃ h'', osNames (L := L) j N'' (DFrac.own 1) h'' ∗
        ⌜h''.restrict j N = h.restrict j N ∧ h''.restrict j N' = h'.restrict j N' ∧
          h''.next = max h.next h'.next⌝ := by
  sorry

/-- A claim under another key of the same names. -/
theorem osNames_rekey (R : Roots) (j : Ino) (N N' : NameSet) (h : NamesH) (hN : N.Same N')
    (hE : ↑osShN ⊆ E) :
    osSharedInv (L := L) R -∗ osNames (L := L) j N (DFrac.own 1) h ={E}=∗
      osNames (L := L) j N' (DFrac.own 1) h := by
  sorry

/-- The log is at least as long as a claim knows. -/
theorem osNames_next (R : Roots) (j : Ino) (N : NameSet) (dq : DFrac) (h : NamesH)
    (hE : ↑osShN ⊆ E) :
    osSharedInv (L := L) R -∗ osNames (L := L) j N dq h ={E}=∗
      osNames (L := L) j N dq h ∗ osLogLb (L := L) h.next := by
  sorry

theorem osLogLb_le {n : Nat} (n' : Nat) (h : n' ≤ n) :
    osLogLb (L := L) n ⊢ osLogLb (L := L) n' := by
  unfold osLogLb
  letI := (gooseOsGS (L := L)).osAllG
  iintro H
  iapply monoNatLbOwn_le n' h $$ H

/-- A spine's claims split. -/
theorem osPathS_frac (R : Roots) (p : GoString) (q1 q2 : Qp) (j : Ino) :
    osPathS (L := L) R p (DFrac.own (q1 + q2)) j ⊣⊢
      osPathS (L := L) R p (DFrac.own q1) j ∗ osPathS (L := L) R p (DFrac.own q2) j := by
  sorry

/-- A spine extended by a claim's fraction on a name holding a directory. -/
theorem osPathS_child (R : Roots) (d b : GoString) (dq : DFrac) (j J : Ino) (h : NamesH)
    (hb : NameOk b) (hJ : h.cur !! b = some (.dir J)) :
    osPathS (L := L) R d dq j -∗ osNames (L := L) j (.only [b]) dq h -∗
      osPathS (L := L) R (child d b) dq J := by
  sorry

end laws

/-! ## The mode switch and `CallBegin` -/

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- **The mode switch**, at any step of the extension: the whole legacy history `V` (no legacy call
or directory fd) for the shared mode's resources: its invariant, the whole call permission, the
log's length, a claim on all names of every directory of the tree. Irreversible. -/
theorem wp_osShare (R : Roots) (V : Hist) (op : String) (v : val) (hv : v.isPanic = false)
    (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osTree (L := L) (DFrac.own 1) R V -∗
      (osSharedInv (L := L) R -∗ osCallPerm (L := L) 1 -∗ osLogLb (L := L) V.2.length -∗
        ([∗list] j ∈ (GMap.toList V.now).map (·.1),
          osNames (L := L) j (.except []) (DFrac.own 1) (namesOf V j (.except []))) -∗
        WP (ExternalOp fsExt.name op (Val v)) @ s; E {{ Φ }}) -∗
      WP (ExternalOp fsExt.name op (Val v)) @ s; E {{ Φ }} :=
  wp_osShare' R V op v hE Φ

/-- **`CallBegin()`** in the shared mode, with a fraction `q` of the call permission: a call in
flight holding it, begun at a log length `s0` at least any the caller knew. -/
theorem wp_osCallBeginS (R : Roots) (q : Qp) (n : Nat) (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osCallPerm (L := L) q -∗ osLogLb (L := L) n -∗
      (∀ (t s0 : Nat), ⌜n ≤ s0⌝ -∗ osCallS (L := L) t s0 q -∗ osLogLb (L := L) s0 -∗
        Φ (osTokV t)) -∗
      WP (ExternalOp fsExt.name "CallBegin" (Val (#()))) @ s; E {{ Φ }} :=
  wp_osCallBeginS' R q n hE hE' Φ

/-! ## Metadata steps. Each ends its call (`osCallPerm q` back); a claim written whole, with
`h.next ≤ s0`. -/

/-- **`unlink(2)`** of `d/b` (the file `i`), `d` the directory `j`. -/
theorem wp_osUnlinkS (R : Roots) (d b : GoString) (j i : Ino) (dq : DFrac) (h : NamesH)
    (k s0 : Nat) (q : Qp) (hb : NameOk b) (hi : h.cur !! b = some (.file i)) (hs : h.next ≤ s0)
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j (.only [b]) (DFrac.own 1) h -∗ osCallS (L := L) k s0 q -∗
      (∀ e : w64, osCallPerm (L := L) q -∗ osPathS (L := L) R d dq j -∗
        osNamesAfter (L := L) j (.only [b]) h ⟨.remove j b (.file i), s0⟩ (GMap.delete b h.cur)
          (e ≠ 0) -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Unlink" (Val (PairV (osTokV k) (#(child d b))))) @ s; E {{ Φ }} := by
  sorry

/-- **`unlink(2)`** of a name holding nothing or a directory: an errno, no effect. -/
theorem wp_osUnlinkS_none (R : Roots) (d b : GoString) (j : Ino) (dq dqn : DFrac) (h : NamesH)
    (k s0 : Nat) (q : Qp) (hb : NameOk b) (hi : ∀ i, h.cur !! b ≠ some (.file i))
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j (.only [b]) dqn h -∗ osCallS (L := L) k s0 q -∗
      (∀ e : w64, ⌜e ≠ 0⌝ -∗ osCallPerm (L := L) q -∗ osPathS (L := L) R d dq j -∗
        osNames (L := L) j (.only [b]) dqn h -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Unlink" (Val (PairV (osTokV k) (#(child d b))))) @ s; E {{ Φ }} := by
  sorry

/-- **`rename(2)`** of the file `d/bs` (inode `i`) onto `d'/bt` (a file or nothing), the names in
two claims (of `j` and `j'`; distinct keys). -/
theorem wp_osRenameFileS (R : Roots) (d bs d' bt : GoString) (j j' i : Ino) (N N' : NameSet)
    (dq dq' : DFrac) (h h' : NamesH) (k s0 : Nat) (q : Qp) (hbs : NameOk bs) (hbt : NameOk bt)
    (hN : N.Mem bs) (hN' : N'.Mem bt) (hkey : (j, N) ≠ (j', N'))
    (hsrc : h.cur !! bs = some (.file i)) (htgt : ∀ J, h'.cur !! bt ≠ some (.dir J))
    (hs : h.next ≤ s0) (hs' : h'.next ≤ s0) (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osPathS (L := L) R d' dq' j' -∗
      osNames (L := L) j N (DFrac.own 1) h -∗ osNames (L := L) j' N' (DFrac.own 1) h' -∗
      osCallS (L := L) k s0 q -∗
      (∀ e : w64, osCallPerm (L := L) q -∗ osPathS (L := L) R d dq j -∗
        osPathS (L := L) R d' dq' j' -∗
                ((⌜e ≠ 0⌝ ∗ osNames (L := L) j N (DFrac.own 1) h ∗ osNames (L := L) j' N' (DFrac.own 1) h') ∨
         ∃ x, osLogged (L := L) x (⟨.rename j bs j' bt (.file i) (h'.cur !! bt), s0⟩ : LogEntry) ∗
           osNames (L := L) j N (DFrac.own 1) (h.log x (⟨.rename j bs j' bt (.file i) (h'.cur !! bt), s0⟩ : LogEntry) (GMap.delete bs h.cur)) ∗
           osNames (L := L) j' N' (DFrac.own 1) (h'.log x (⟨.rename j bs j' bt (.file i) (h'.cur !! bt), s0⟩ : LogEntry) (<[bt := .file i]> h'.cur))) -∗
        Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Rename" (Val (PairV (osTokV k)
        (PairV (#(child d bs)) (#(child d' bt)))))) @ s; E {{ Φ }} := by
  sorry

/-- **`rename(2)`** of the file `d/bs` onto `d/bt`, both names in one claim. -/
theorem wp_osRenameFileS1 (R : Roots) (d bs bt : GoString) (j i : Ino) (N : NameSet)
    (dq : DFrac) (h : NamesH) (k s0 : Nat) (q : Qp) (hbs : NameOk bs) (hbt : NameOk bt)
    (hN : N.Mem bs) (hN' : N.Mem bt) (hne : bs ≠ bt)
    (hsrc : h.cur !! bs = some (.file i)) (htgt : ∀ J, h.cur !! bt ≠ some (.dir J))
    (hs : h.next ≤ s0) (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j N (DFrac.own 1) h -∗ osCallS (L := L) k s0 q -∗
      (∀ e : w64, osCallPerm (L := L) q -∗ osPathS (L := L) R d dq j -∗
        osNamesAfter (L := L) j N h ⟨.rename j bs j bt (.file i) (h.cur !! bt), s0⟩
          (<[bt := .file i]> (GMap.delete bs h.cur)) (e ≠ 0) -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Rename" (Val (PairV (osTokV k)
        (PairV (#(child d bs)) (#(child d bt)))))) @ s; E {{ Φ }} := by
  sorry

/-- **`rename(2)`** of the directory `d/bs` (inode `J`) to the free name `d/bt`, by a call holding
the whole call permission (no other call in flight, `DirOpExcl`). -/
theorem wp_osRenameDirS (R : Roots) (d bs bt : GoString) (j J : Ino) (N : NameSet) (dq : DFrac)
    (h : NamesH) (k s0 : Nat) (hbs : NameOk bs) (hbt : NameOk bt) (hN : N.Mem bs) (hN' : N.Mem bt)
    (hne : bs ≠ bt) (hsrc : h.cur !! bs = some (.dir J)) (htgt : h.cur !! bt = none)
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j N (DFrac.own 1) h -∗ osCallS (L := L) k s0 1 -∗
      (∀ e : w64, osCallPerm (L := L) 1 -∗ osPathS (L := L) R d dq j -∗
        osNamesAfter (L := L) j N h ⟨.rename j bs j bt (.dir J) none, s0⟩
          (<[bt := .dir J]> (GMap.delete bs h.cur)) (e ≠ 0) -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Rename" (Val (PairV (osTokV k)
        (PairV (#(child d bs)) (#(child d bt)))))) @ s; E {{ Φ }} := by
  sorry

/-- **`rename(2)`** of a source naming nothing: an errno, no effect. -/
theorem wp_osRenameAbsentS (R : Roots) (d bs d' bt : GoString) (j j' : Ino) (N : NameSet)
    (dq dq' dqn : DFrac) (h : NamesH) (k s0 : Nat) (q : Qp) (hbs : NameOk bs) (hbt : NameOk bt)
    (hN : N.Mem bs) (hsrc : h.cur !! bs = none) (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osPathS (L := L) R d' dq' j' -∗ osNames (L := L) j N dqn h -∗ osCallS (L := L) k s0 q -∗
      (∀ e : w64, ⌜e ≠ 0⌝ -∗ osCallPerm (L := L) q -∗ osPathS (L := L) R d dq j -∗
        osPathS (L := L) R d' dq' j' -∗ osNames (L := L) j N dqn h -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Rename" (Val (PairV (osTokV k)
        (PairV (#(child d bs)) (#(child d' bt)))))) @ s; E {{ Φ }} := by
  sorry

/-- **`mkdir(2)`** of the free name `d/b`, by a call holding the whole call permission: the new
directory `J` comes with a claim on all its names. -/
theorem wp_osMkdirS (R : Roots) (d b : GoString) (j : Ino) (dq : DFrac) (h : NamesH) (k s0 : Nat)
    (hb : NameOk b) (hn : h.cur !! b = none) (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j (.only [b]) (DFrac.own 1) h -∗ osCallS (L := L) k s0 1 -∗
      (∀ e : w64, osCallPerm (L := L) 1 -∗ osPathS (L := L) R d dq j -∗
        ((⌜e ≠ 0⌝ ∗ osNames (L := L) j (.only [b]) (DFrac.own 1) h) ∨
         ∃ x J, osLogged (L := L) x (⟨.mkdir j b J, s0⟩ : LogEntry) ∗
           osNames (L := L) j (.only [b]) (DFrac.own 1) (h.log x (⟨.mkdir j b J, s0⟩ : LogEntry) (<[b := .dir J]> h.cur)) ∗
           osNames (L := L) J (.except []) (DFrac.own 1) ⟨∅, [(x, o, ∅)], ∅⟩) -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Mkdir" (Val (PairV (osTokV k) (#(child d b))))) @ s; E {{ Φ }} := by
  sorry

/-- **`rmdir(2)`** of the directory `d/b` (inode `J`), empty (its whole claim, with no name), by a
call holding the whole call permission. -/
theorem wp_osRmdirS (R : Roots) (d b : GoString) (j J : Ino) (dq : DFrac) (h hJ : NamesH)
    (k s0 : Nat) (hb : NameOk b) (hd : h.cur !! b = some (.dir J)) (he : hJ.cur = ∅)
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j (.only [b]) (DFrac.own 1) h -∗
      osNames (L := L) J (.except []) (DFrac.own 1) hJ -∗ osCallS (L := L) k s0 1 -∗
      (∀ e : w64, osCallPerm (L := L) 1 -∗ osPathS (L := L) R d dq j -∗
        osNames (L := L) J (.except []) (DFrac.own 1) hJ -∗
        osNamesAfter (L := L) j (.only [b]) h ⟨.remove j b (.dir J), s0⟩ (GMap.delete b h.cur)
          (e ≠ 0) -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Rmdir" (Val (PairV (osTokV k) (#(child d b))))) @ s; E {{ Φ }} := by
  sorry

/-- **`rmdir(2)`** of a name holding nothing or a file: an errno, no effect. -/
theorem wp_osRmdirS_none (R : Roots) (d b : GoString) (j : Ino) (dq dqn : DFrac) (h : NamesH)
    (k s0 : Nat) (q : Qp) (hb : NameOk b) (hi : ∀ J, h.cur !! b ≠ some (.dir J))
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j (.only [b]) dqn h -∗ osCallS (L := L) k s0 q -∗
      (∀ e : w64, ⌜e ≠ 0⌝ -∗ osCallPerm (L := L) q -∗ osPathS (L := L) R d dq j -∗
        osNames (L := L) j (.only [b]) dqn h -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Rmdir" (Val (PairV (osTokV k) (#(child d b))))) @ s; E {{ Φ }} := by
  sorry

/-- **`lstat(2)`'s "is it a directory"** of `d/b`, with a fraction of the claim on `b`. -/
theorem wp_osLstatDirS (R : Roots) (d b : GoString) (j : Ino) (dq dqn : DFrac) (h : NamesH)
    (k s0 : Nat) (q : Qp) (hb : NameOk b) (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j (.only [b]) dqn h -∗ osCallS (L := L) k s0 q -∗
      (∀ isDir : w64, ∀ e : w64, ⌜isDir = 1 → (∃ J, h.cur !! b = some (.dir J)) ∧ e ≠ 0⌝ -∗
        osCallPerm (L := L) q -∗ osPathS (L := L) R d dq j -∗
        osNames (L := L) j (.only [b]) dqn h -∗ Φ (PairV (#isDir) (#e))) -∗
      WP (ExternalOp fsExt.name "LstatDir" (Val (PairV (osTokV k) (#(child d b))))) @ s; E
        {{ Φ }} := by
  sorry

/-! ## Opens -/

/-- **`open(2)` with `O_RDWR | O_CREAT`** of `d/b`, a name holding a file or nothing: the file, or
a new one (its `create` logged; on failure perhaps). -/
theorem wp_osOpenCreateS (R : Roots) (d b : GoString) (j : Ino) (dq : DFrac) (h : NamesH)
    (k s0 : Nat) (q : Qp) (hb : NameOk b) (hnd : ∀ J, h.cur !! b ≠ some (.dir J))
    (hs : h.next ≤ s0) (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j (.only [b]) (DFrac.own 1) h -∗ osCallS (L := L) k s0 q -∗
      (∀ fd : w64, ∀ e : w64, osCallPerm (L := L) q -∗ osPathS (L := L) R d dq j -∗
        ((∃ i, ⌜h.cur !! b = some (.file i)⌝ ∗ osNames (L := L) j (.only [b]) (DFrac.own 1) h ∗
            (⌜e ≠ 0 ∧ fd = -1⌝ ∨ ⌜e = 0 ∧ 0 ≤ fd.toInt⌝ ∗ osFd (L := L) fd (DFrac.own 1) ⟨i, true, true⟩)) ∨
         (⌜h.cur !! b = none⌝ ∗ ∃ x i, osLogged (L := L) x (⟨.create j b i, s0⟩ : LogEntry) ∗
            osNames (L := L) j (.only [b]) (DFrac.own 1) (h.log x (⟨.create j b i, s0⟩ : LogEntry) (<[b := .file i]> h.cur)) ∗
            osMeta (L := L) i (DFrac.own 1) newMeta ∗
            (⌜e ≠ 0 ∧ fd = -1⌝ ∨ ⌜e = 0 ∧ 0 ≤ fd.toInt⌝ ∗ osFd (L := L) fd (DFrac.own 1) ⟨i, true, true⟩)) ∨
         (⌜e ≠ 0 ∧ fd = -1⌝ ∗ osNames (L := L) j (.only [b]) (DFrac.own 1) h)) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp fsExt.name "Open" (Val (PairV (osTokV k) (PairV (#(child d b)) (#flCreat)))))
        @ s; E {{ Φ }} := by
  sorry

/-- **`open(2)` of a directory, read-only**: a shared directory fd, holding nothing. -/
theorem wp_osOpenDirS (R : Roots) (p : GoString) (j : Ino) (dq : DFrac) (k s0 : Nat) (q : Qp)
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R p dq j -∗
      osCallS (L := L) k s0 q -∗
      (∀ fd : w64, ∀ e : w64, ⌜(e = 0 ∧ 0 ≤ fd.toInt) ∨ (e ≠ 0 ∧ fd = -1)⌝ -∗ osCallPerm (L := L) q -∗
        osPathS (L := L) R p dq j -∗ (⌜e = 0⌝ -∗ osDirFdS (L := L) fd j .idle) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp fsExt.name "Open" (Val (PairV (osTokV k) (PairV (#p) (#flRO))))) @ s; E
        {{ Φ }} := by
  sorry

/-! ## Shared directory fds -/

/-- **`fsync(2)` of a shared directory fd**: on success, the log's first `n` entries committed. -/
theorem wp_osDirSyncS (R : Roots) (fd : w64) (j : Ino) (ph : DirPhS) (n : Nat) (hE : ↑osN ⊆ E)
    (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osDirFdS (L := L) fd j ph -∗
      osLogLb (L := L) n -∗
      (∀ e : w64, osDirFdS (L := L) fd j ph -∗ (⌜e ≠ 0⌝ ∨ osCommitLb (L := L) n) -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "DirSync" (Val (#fd))) @ s; E {{ Φ }} := by
  sorry

/-- **`close(2)` of a shared directory fd.** -/
theorem wp_osDirCloseS (fd : w64) (j : Ino) (ph : DirPhS) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osDirFdS (L := L) fd j ph -∗ (∀ e : w64, Φ (#e)) -∗
      WP (ExternalOp fsExt.name "DirClose" (Val (#fd))) @ s; E {{ Φ }} := by
  sorry

/-- **`FdKind` of a shared directory fd**: a directory's. -/
theorem wp_osFdKindDirS (fd : w64) (j : Ino) (ph : DirPhS) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osDirFdS (L := L) fd j ph -∗ (osDirFdS (L := L) fd j ph -∗ Φ (#(1 : w64))) -∗
      WP (ExternalOp fsExt.name "FdKind" (Val (#fd))) @ s; E {{ Φ }} := by
  sorry

/-- **One step of a read of a shared directory fd**, with a claim on the names `N` (a fraction;
nothing of them changed since the read began, `h.next ≤ r0`): a name (in `N`: one there, not yet
returned), the end (once every name of `N` there was returned), or an errno. -/
theorem wp_osDirReadNextS (R : Roots) (fd : w64) (j : Ino) (N : NameSet) (r0 : Nat)
    (rs : List GoString) (fresh : Bool) (dq : DFrac) (h : NamesH)
    (hfr : fresh = true → rs = []) (hr0 : fresh = false → h.next ≤ r0)
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗
      osDirFdS (L := L) fd j (if fresh then .idle else .reading N r0 rs) -∗
      osNames (L := L) j N dq h -∗
      (∀ v, osNames (L := L) j N dq h -∗
        (∃ r0', ⌜fresh = false → r0' = r0⌝ ∗ ⌜fresh = true → h.next ≤ r0'⌝ ∗
          ((∃ b, ⌜v = rdName b ∧ NameOk b ∧ (N.Mem b → (h.cur !! b).isSome ∧ b ∉ rs)⌝ ∗
              osDirFdS (L := L) fd j (.reading N r0' (b :: rs))) ∨
           (⌜v = rdEnd ∧ ∀ b, N.Mem b → (h.cur !! b).isSome → b ∈ rs⌝ ∗
              osDirFdS (L := L) fd j .done) ∨
           (∃ e : w64, ⌜e ≠ 0 ∧ v = rdErr e⌝ ∗ osDirFdS (L := L) fd j (.reading N r0' rs)))) -∗
        Φ v) -∗
      WP (ExternalOp fsExt.name "DirReadNext" (Val (#fd))) @ s; E {{ Φ }} := by
  sorry

/-- **One step of a blind read of a shared directory fd** (no claim): a valid name, the end, or an
errno. -/
theorem wp_osDirReadNextBlind (fd : w64) (j : Ino) (ph : DirPhS) (hph : ph ≠ .done)
    (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osDirFdS (L := L) fd j ph -∗
      (∀ v, ((∃ b, ⌜v = rdName b ∧ NameOk b⌝ ∗ osDirFdS (L := L) fd j (.reading (.only []) 0 [])) ∨
          (⌜v = rdEnd⌝ ∗ osDirFdS (L := L) fd j .done) ∨
          (∃ e : w64, ⌜e ≠ 0 ∧ v = rdErr e⌝ ∗ osDirFdS (L := L) fd j (.reading (.only []) 0 []))) -∗
        Φ v) -∗
      WP (ExternalOp fsExt.name "DirReadNext" (Val (#fd))) @ s; E {{ Φ }} := by
  sorry

end specs

/-! ## Crashes -/

section crash
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]

/-- **What a region concludes of a crash** of a generation `L` in the shared mode: from its claims
and a lower bound on the committed prefix, `RegionCrashed` of the new generation's tree. -/
theorem crashRest_region (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF) (D : List Ino)
    (tt : Bool) (V' : Hist) (R : Roots) (cl : List (Claim × DFrac)) (n : Nat) (E : CoPset)
    (hE : ↑osShN ⊆ E) :
    ⊢ osSharedInv (L := L) R -∗ crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D tt V' -∗
      osClaims L cl -∗ osCommitLb (L := L) n ={E}=∗
      ⌜RegionCrashed (cl.map (·.1)) n V'.now⌝ ∗
      crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D tt V' ∗ osClaims L cl :=
  crashRest_region' Q L L' D tt V' R cl n E hE

/-- **The tree after a crash, in the shared mode**: the new generation's history, whole (the new
generation starts in the legacy mode), the crashed tree with the shared invariant's roots. -/
theorem crashRest_treeS (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF) (D : List Ino)
    (V' : Hist) (R : Roots) (E : CoPset) (hE : ↑osShN ⊆ E) :
    ⊢ osSharedInv (L := L) R -∗
      crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D false V' ={E}=∗
      ⌜V'.2 = []⌝ ∗ osTree (L := L') (DFrac.own 1) R V' ∗
      crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D true V' :=
  crashRest_treeS' Q L L' D V' R E hE

end crash

end Fs
end Perennial

end
