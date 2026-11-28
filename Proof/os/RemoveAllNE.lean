/-
The shared-mode specs of `unlink(2)` and `rmdir(2)` on `d/b`, their errno witnessed when the file
system does not fail on `d/b` (`FsNoErrAt`, `NoErrRemoveSteps.lean`), through `wp_fs_postSh`
(wal-safe, 2026-11-22, step 2 (D), design (FNE) of `notes/wal-units/tester.md`): an `unlink` of a
file answers 0 (`wp_osUnlinkSW`), of a directory `EISDIR` (`wp_osUnlinkS_noneW`); an `rmdir` of a
non-empty directory `ENOTEMPTY` (`wp_osRmdirS_nonemptyW`), of an empty one 0 (`wp_osRmdirSGW`).
For `os.RemoveAll.specSubS`'s witness (`RemoveAll(d/b)` returns `nil` only with `b` gone). Untrusted.
-/
module

public import GooseLang.Ext.Fs.WpPostShared
public import GooseLang.Ext.Fs.NoErrRemoveSteps
public import Proof.os.RemoveAllExt

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section step
variable [GooseExts] [GoGlobalContext] [go.BasicIntoValInj] [S : ExtSemantics fsExt] [FsSemOk]
variable {tf : GoTypeFns}

/-- A step of `unlink(2)` returns a value. -/
theorem unlink_isVal {k : Nat} {p : GoString}
    {h : GMap Loc (NonAtomic val)} {st : OsState} {g : Unit} {e' : Expr}
    {h' : GMap Loc (NonAtomic val)} {st' : OsState} {g' : Unit}
    (hs : S.step tf "Unlink" (PairV (osTokV k) (#p)) h st g e' h' st' g') : ∃ r, e' = Val r := by
  have hst := (fsStepV_of_ne (by decide) (FsSemOk.step_sub _ _ _ _ _ _ _ _ _ hs)).1
  simp only [IsFsStep] at hst
  obtain ⟨p', k', s0, hv, htn, hcall, hr⟩ := hst
  rcases hr with ⟨-, -, -, -, -, ⟨-, rfl⟩ | ⟨-, -, rfl, -⟩⟩ | ⟨-, -, rfl, -⟩ <;> exact ⟨_, rfl⟩

/-- A step of `rmdir(2)` returns a value. -/
theorem rmdir_isVal {k : Nat} {p : GoString}
    {h : GMap Loc (NonAtomic val)} {st : OsState} {g : Unit} {e' : Expr}
    {h' : GMap Loc (NonAtomic val)} {st' : OsState} {g' : Unit}
    (hs : S.step tf "Rmdir" (PairV (osTokV k) (#p)) h st g e' h' st' g') : ∃ r, e' = Val r := by
  have hst := (fsStepV_of_ne (by decide) (FsSemOk.step_sub _ _ _ _ _ _ _ _ _ hs)).1
  simp only [IsFsStep] at hst
  obtain ⟨p', k', s0, hv, htn, hcall, hr⟩ := hst
  rcases hr with ⟨-, -, -, -, -, ⟨-, rfl⟩ | ⟨-, -, rfl, -⟩⟩ | ⟨-, -, rfl, -⟩ <;> exact ⟨_, rfl⟩

/-- A step of `open(2)` returns a value. -/
theorem open_isVal {k : Nat} {p : GoString} {fl : w64}
    {h : GMap Loc (NonAtomic val)} {st : OsState} {g : Unit} {e' : Expr}
    {h' : GMap Loc (NonAtomic val)} {st' : OsState} {g' : Unit}
    (hs : S.step tf "Open" (PairV (osTokV k) (PairV (#p) (#fl))) h st g e' h' st' g') :
    ∃ fd e : w64, e' = osRes (#fd) e := by
  have hst := (fsStepV_of_ne (by decide) (FsSemOk.step_sub _ _ _ _ _ _ _ _ _ hs)).1
  simp only [IsFsStep] at hst
  rcases hst with ⟨p1, fl1, t1, s1, hv1, htp1, hfl1, hc1, htr1, hr⟩ |
    ⟨p1, fl1, t1, s1, hv1, hn1, ha1, hro1, hc1, hr⟩
  · rcases hr with ⟨-, -, fd, -, -, -, rfl⟩ | ⟨e, -, -, rfl, -⟩
    · exact ⟨_, _, rfl⟩
    · exact ⟨_, _, rfl⟩
  · rcases hr with ⟨fd, -, -, rfl⟩ | ⟨e, -, -, rfl⟩
    · exact ⟨_, _, rfl⟩
    · exact ⟨_, _, rfl⟩

end step

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- **`unlink(2)` of the file `d/b`**, `wp_osUnlinkS` with its errno witnessed: 0 when the file
system does not fail on `d/b`. -/
theorem wp_osUnlinkSW (R : Roots) (d b : GoString) (j i : Ino) (dq : DFrac) (h : NamesH)
    (k s0 : Nat) (q : Qp) (hb : NameOk b) (hi : h.cur !! b = some (.file i)) (hs : h.next ≤ s0)
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j (.only [b]) (DFrac.own 1) h -∗ osCallS (L := L) k s0 (child d b) q -∗
      (∀ e : w64, ⌜FsNoErrAt (child d b) → e = 0⌝ -∗ osCallPerm (L := L) (callKey R d) q -∗
        osPathS (L := L) R d dq j -∗
        osNamesAfter (L := L) j (.only [b]) h ⟨.remove j b (.file i), s0⟩ (GMap.delete b h.cur)
          (e ≠ 0) -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Unlink" (Val (PairV (osTokV k) (#(child d b))))) @ s; E {{ Φ }} := by
  iintro #Hinv #Hsi Hp Hn Hk HΦ
  iapply wp_fs_postSh "Unlink" _ (by simp [val.isPanic]) R
    iprop(osPathS (L := L) R d dq j ∗ osNames (L := L) j (.only [b]) (DFrac.own 1) h)
    (fun st => PathNames st d j (.only [b]) h)
    (fun st Γn hR hcoh => pathNames_of R d dq j _ _ h st Γn hR hcoh)
    (fun w => FsNoErrAt (child d b) → w = #(0 : w64))
    (fun _ st _ e' _ _ _ hP hw _ hst => by
      by_cases hne : FsNoErrAt (child d b)
      · have := (unlink_noErrAt hne hP.1 hb hw hst).1
          ⟨i, by rw [hP.2 b (by simp [NameSet.Mem]), hi]⟩
        exact ⟨_, this, fun _ => rfl⟩
      · obtain ⟨r, hr⟩ := unlink_isVal hst
        exact ⟨r, hr, fun h0 => absurd h0 hne⟩)
    hE' Φ $$ Hsi [Hp Hn]
  · iframe
  iintro ⟨Hp, Hn⟩
  iapply wp_osUnlinkS R d b j i dq h k s0 q hb hi hs hE hE' _ $$ Hinv Hsi Hp Hn Hk
  iintro %e Hperm Hp Hres %hw
  iapply HΦ $$ %e [] Hperm Hp Hres
  ipureintro; intro hne; exact go.intoVal_inj (hw hne)

/-- **`unlink(2)` of `d/b` holding nothing or a directory**, `wp_osUnlinkS_none` with its errno
witnessed: `EISDIR` on a directory when the file system does not fail on `d/b`. -/
theorem wp_osUnlinkS_noneW (R : Roots) (d b : GoString) (j : Ino) (dq dqn : DFrac) (h : NamesH)
    (k s0 : Nat) (q : Qp) (hb : NameOk b) (hi : ∀ i, h.cur !! b ≠ some (.file i))
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j (.only [b]) dqn h -∗ osCallS (L := L) k s0 (child d b) q -∗
      (∀ e : w64, ⌜e ≠ 0⌝ -∗
        ⌜FsNoErrAt (child d b) → (∃ J, h.cur !! b = some (.dir J)) → e = EISDIR⌝ -∗
        osCallPerm (L := L) (callKey R d) q -∗ osPathS (L := L) R d dq j -∗
        osNames (L := L) j (.only [b]) dqn h -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Unlink" (Val (PairV (osTokV k) (#(child d b))))) @ s; E {{ Φ }} := by
  iintro #Hinv #Hsi Hp Hn Hk HΦ
  iapply wp_fs_postSh "Unlink" _ (by simp [val.isPanic]) R
    iprop(osPathS (L := L) R d dq j ∗ osNames (L := L) j (.only [b]) dqn h)
    (fun st => PathNames st d j (.only [b]) h)
    (fun st Γn hR hcoh => pathNames_of R d dq j _ _ h st Γn hR hcoh)
    (fun w => FsNoErrAt (child d b) → (∃ J, h.cur !! b = some (.dir J)) → w = #EISDIR)
    (fun _ st _ e' _ _ _ hP hw _ hst => by
      obtain ⟨r, hr⟩ := unlink_isVal hst
      refine ⟨r, hr, fun hne ⟨J, hJ⟩ => ?_⟩
      have := (unlink_noErrAt hne hP.1 hb hw hst).2
        ⟨J, by rw [hP.2 b (by simp [NameSet.Mem]), hJ]⟩
      rw [hr] at this; injection this)
    hE' Φ $$ Hsi [Hp Hn]
  · iframe
  iintro ⟨Hp, Hn⟩
  iapply wp_osUnlinkS_none R d b j dq dqn h k s0 q hb hi hE hE' _ $$ Hinv Hsi Hp Hn Hk
  iintro %e %he Hperm Hp Hn %hw
  iapply HΦ $$ %e %he [] Hperm Hp Hn
  ipureintro; intro hne hJ; exact go.intoVal_inj (hw hne hJ)

/-- **`rmdir(2)` of `d/b`, a directory `J` holding the name `c`**, `wp_osRmdirS_nonempty` with its
errno witnessed: `ENOTEMPTY` when the file system does not fail on `d/b`. -/
theorem wp_osRmdirS_nonemptyW (R : Roots) (d b : GoString) (j J : Ino) (N : NameSet)
    (dq dqJ dqn : DFrac) (hJ : NamesH) (c : GoString) (k s0 : Nat) (q : Qp) (hb : NameOk b)
    (hN : N.Mem c) (hc : (hJ.cur !! c).isSome) (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osPathS (L := L) R (child d b) dqJ J -∗
      osNames (L := L) J N dqn hJ -∗ osCallS (L := L) k s0 (child d b) q -∗
      (∀ e : w64, ⌜e ≠ 0⌝ -∗ ⌜FsNoErrAt (child d b) → e = ENOTEMPTY⌝ -∗
        osCallPerm (L := L) (callKey R d) q -∗ osPathS (L := L) R d dq j -∗
        osPathS (L := L) R (child d b) dqJ J -∗ osNames (L := L) J N dqn hJ -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Rmdir" (Val (PairV (osTokV k) (#(child d b))))) @ s; E {{ Φ }} := by
  iintro #Hinv #Hsi Hp Hp' Hn Hk HΦ
  iapply wp_fs_postSh "Rmdir" _ (by simp [val.isPanic]) R
    iprop(osPathS (L := L) R d dq j ∗ osPathS (L := L) R (child d b) dqJ J ∗
      osNames (L := L) J N dqn hJ)
    (fun st => st.lookup d = some (.dir j) ∧ st.lookup (child d b) = some (.dir J) ∧
      ∀ x, N.Mem x → st.tree.entry J x = hJ.cur !! x)
    (fun st Γn hR hcoh => by
      iintro HA ⟨Hp, Hp', Hn⟩
      icases osPathS_lookup hR hcoh d dq j $$ HA Hp with %h1
      icases osPathS_lookup hR hcoh (child d b) dqJ J $$ HA Hp' with %h2
      icases osNames_entry hcoh J N dqn hJ $$ HA Hn with %h3
      ipureintro; exact ⟨h1, h2, h3⟩)
    (fun w => FsNoErrAt (child d b) → w = #ENOTEMPTY)
    (fun _ st _ e' _ _ _ hP hw _ hst => by
      obtain ⟨r, hr⟩ := rmdir_isVal hst
      refine ⟨r, hr, fun hne => ?_⟩
      have hbJ : st.tree.entry j b = some (.dir J) := by
        rw [← lookup_child hw.roots hP.1 hb]; exact hP.2.1
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 hc
      have := (rmdir_noErrAt hne hP.1 hb hw hbJ hst).2 ⟨c, n, by rw [hP.2.2 c hN, hn]⟩
      rw [hr] at this; injection this)
    hE' Φ $$ Hsi [Hp Hp' Hn]
  · iframe
  iintro ⟨Hp, Hp', Hn⟩
  iapply wp_osRmdirS_nonempty R d b j J N dq dqJ dqn hJ c k s0 q hb hN hc hE hE' _
    $$ Hinv Hsi Hp Hp' Hn Hk
  iintro %e %he Hperm Hp Hp' Hn %hw
  iapply HΦ $$ %e %he [] Hperm Hp Hp' Hn
  ipureintro; intro hne; exact go.intoVal_inj (hw hne)

/-- **`rmdir(2)` of the empty directory `d/b`** (under a guard), `wp_osRmdirSG` with its errno
witnessed: 0 when the file system does not fail on `d/b`. -/
theorem wp_osRmdirSGW (R : Roots) (d b : GoString) (j J : Ino) (dq : DFrac) (h hJ : NamesH)
    (k s0 t sg : Nat) (pg : GoString) (q g : Qp) (hqg : q + g = 1) (hsg : sg ≤ s0)
    (hkg : callKey R pg = callKey R (child d b)) (hb : NameOk b)
    (hd : h.cur !! b = some (.dir J)) (he : hJ.cur = ∅)
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j (.only [b]) (DFrac.own 1) h -∗
      osNames (L := L) J (.except []) (DFrac.own 1) hJ -∗ osCallS (L := L) k s0 (child d b) q -∗
      osGuardS (L := L) t sg pg g -∗
      (∀ e : w64, ⌜FsNoErrAt (child d b) → e = 0⌝ -∗ osCallPerm (L := L) (callKey R d) q -∗
        osGuardS (L := L) t sg pg g -∗ osPathS (L := L) R d dq j -∗
        osNames (L := L) J (.except []) (DFrac.own 1) hJ -∗
        osNamesAfter (L := L) j (.only [b]) h ⟨.remove j b (.dir J), s0⟩ (GMap.delete b h.cur)
          (e ≠ 0) -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Rmdir" (Val (PairV (osTokV k) (#(child d b))))) @ s; E {{ Φ }} := by
  iintro #Hinv #Hsi Hp Hn HJ Hk Hg HΦ
  iapply wp_fs_postSh "Rmdir" _ (by simp [val.isPanic]) R
    iprop(osPathS (L := L) R d dq j ∗ osNames (L := L) j (.only [b]) (DFrac.own 1) h ∗
      osNames (L := L) J (.except []) (DFrac.own 1) hJ)
    (fun st => PathNames st d j (.only [b]) h ∧ ∀ x, st.tree.entry J x = hJ.cur !! x)
    (fun st Γn hR hcoh => by
      iintro HA ⟨Hp, Hn, HJ⟩
      icases osPathS_lookup hR hcoh d dq j $$ HA Hp with %h1
      icases osNames_entry hcoh j (.only [b]) _ h $$ HA Hn with %h2
      icases osNames_entry hcoh J (.except []) _ hJ $$ HA HJ with %h3
      ipureintro; exact ⟨⟨h1, h2⟩, fun x => h3 x (by simp [NameSet.Mem])⟩)
    (fun w => FsNoErrAt (child d b) → w = #(0 : w64))
    (fun _ st _ e' _ _ _ hP hw _ hst => by
      obtain ⟨r, hr⟩ := rmdir_isVal hst
      refine ⟨r, hr, fun hne => ?_⟩
      have hbJ : st.tree.entry j b = some (.dir J) := by
        rw [hP.1.2 b (by simp [NameSet.Mem]), hd]
      have := (rmdir_noErrAt hne hP.1.1 hb hw hbJ hst).1 (fun x => by rw [hP.2 x, he]; rfl)
      rw [hr] at this; injection this)
    hE' Φ $$ Hsi [Hp Hn HJ]
  · iframe
  iintro ⟨Hp, Hn, HJ⟩
  iapply wp_osRmdirSG R d b j J dq h hJ k s0 t sg pg q g hqg hsg hkg hb hd he hE hE' _
    $$ Hinv Hsi Hp Hn HJ Hk Hg
  iintro %e Hperm Hg Hp HJ Hres %hw
  iapply HΦ $$ %e [] Hperm Hg Hp HJ Hres
  ipureintro; intro hne; exact go.intoVal_inj (hw hne)

/-- **`open(2)` read-only of the directory `p`** (a spine to it), `wp_osOpenDirS` with its errno
witnessed: 0 or `EINTR` when the file system does not fail on `p`. -/
theorem wp_osOpenDirSW (R : Roots) (p : GoString) (j : Ino) (dq : DFrac) (k s0 : Nat) (q : Qp)
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R p dq j -∗
      osCallS (L := L) k s0 p q -∗
      (∀ fd : w64, ∀ e : w64, ⌜(e = 0 ∧ 0 ≤ fd.toInt) ∨ (e ≠ 0 ∧ e ≠ ENOENT ∧ fd = -1)⌝ -∗
        ⌜FsNoErrAt p → e = 0 ∨ e = EINTR⌝ -∗
        osCallPerm (L := L) (callKey R p) q -∗
        osPathS (L := L) R p dq j -∗ (⌜e = 0⌝ -∗ osDirFdS (L := L) fd j .idle) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp fsExt.name "Open" (Val (PairV (osTokV k) (PairV (#p) (#flRO))))) @ s; E
        {{ Φ }} := by
  iintro #Hinv #Hsi Hp Hk HΦ
  iapply wp_fs_postSh "Open" _ (by simp [val.isPanic]) R (osPathS (L := L) R p dq j)
    (fun st => st.lookup p = some (.dir j))
    (fun st Γn hR hcoh => by
      iintro HA Hp
      icases osPathS_lookup hR hcoh p dq j $$ HA Hp with %h1
      ipureintro; exact h1)
    (fun w => FsNoErrAt p → ∀ fd e : w64, w = PairV (#fd) (#e) → e = 0 ∨ e = EINTR)
    (fun _ st _ e' _ _ _ hP _ _ hst => by
      obtain ⟨fd, e, he⟩ := open_isVal hst
      refine ⟨_, he, fun hne fd' e2 hw => ?_⟩
      have := openDir_noErrAt hne hP hst fd e he
      have h2 : e2 = e := by injection hw with _ hw; exact (go.intoVal_inj hw).symm
      rw [h2]; exact this)
    hE' Φ $$ Hsi Hp
  iintro Hp
  iapply wp_osOpenDirS R p j dq k s0 q hE hE' _ $$ Hinv Hsi Hp Hk
  iintro %fd %e %hres Hperm Hp Hfd %hw
  iapply HΦ $$ %fd %e %hres [] Hperm Hp Hfd
  ipureintro; exact fun hne => hw hne fd e rfl

end specs

end Fs
end Perennial

end
