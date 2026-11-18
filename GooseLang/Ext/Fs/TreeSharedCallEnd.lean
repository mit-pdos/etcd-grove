/-
The shared mode of the tree: the steps that only end their call (`wp_callEndS`): `LstatDir`, and
`Unlink`, `Rmdir`, `Rename` of a name holding nothing they act on. `TreeShared.lean` states the
specs and takes their proofs from here. Untrusted.
-/
module

public import GooseLang.Ext.Fs.TreeSharedStep

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- What a spine and a claim on names of its directory say of the state. -/
def PathNames (st : OsState) (d : GoString) (j : Ino) (N : NameSet) (h : NamesH) : Prop :=
  st.lookup d = some (.dir j) ∧ ∀ b, N.Mem b → st.tree.entry j b = h.cur !! b

theorem pathNames_of (R : Roots) (d : GoString) (dq : DFrac) (j : Ino) (N : NameSet) (dqn : DFrac)
    (h : NamesH) (st : OsState) (Γn : GMap (Ino × NameSet) NamesH) (hR : st.fs.roots = R)
    (hcoh : NamesCoh (st.fs.treeDur, st.fs.metaLog) Γn) :
    ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γn -∗
      iprop(osPathS (L := L) R d dq j ∗ osNames (L := L) j N dqn h) -∗ ⌜PathNames st d j N h⌝ := by
  iintro HA ⟨Hp, Hn⟩
  icases osPathS_lookup hR hcoh d dq j $$ HA Hp with %h1
  icases osNames_entry hcoh j N dqn h $$ HA Hn with %h2
  ipureintro; exact ⟨h1, h2⟩

theorem pathNames_child {st : OsState} {d b : GoString} {j : Ino} {N : NameSet} {h : NamesH}
    (hw : FsTreeWf st) (hp : PathNames st d j N h) (hb : NameOk b) (hN : N.Mem b) :
    st.lookup (child d b) = h.cur !! b := by
  rw [lookup_child hw.roots hp.1 hb, hp.2 b hN]

theorem wp_osLstatDirS' (R : Roots) (d b : GoString) (j : Ino) (dq dqn : DFrac) (h : NamesH)
    (k s0 : Nat) (q : Qp) (hb : NameOk b) (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j (.only [b]) dqn h -∗ osCallS (L := L) k s0 q -∗
      (∀ isDir : w64, ∀ e : w64, ⌜isDir = 1 → (∃ J, h.cur !! b = some (.dir J)) ∧ e ≠ 0⌝ -∗
        osCallPerm (L := L) q -∗ osPathS (L := L) R d dq j -∗
        osNames (L := L) j (.only [b]) dqn h -∗ Φ (PairV (#isDir) (#e))) -∗
      WP (ExternalOp fsExt.name "LstatDir" (Val (PairV (osTokV k) (#(child d b))))) @ s; E
        {{ Φ }} := by
  have hbN : (NameSet.only [b]).Mem b := by simp [NameSet.Mem]
  have hprog : ∀ st, FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      PathNames st d j (.only [b]) h →
      ∃ e', IsFsStep "LstatDir" (PairV (osTokV k) (#(child d b))) st e' (st.metaEnd k) :=
    fun st _ _ hcall hp => ⟨_, child d b, 0, 0, k, s0, rfl, Or.inr (treeName_child hp.1 hb), hcall,
      rfl, .inr rfl, rfl⟩
  have hpost : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      PathNames st d j (.only [b]) h →
      IsFsStep "LstatDir" (PairV (osTokV k) (#(child d b))) st e' st' →
      st' = st.metaEnd k ∧ ∃ w, e' = Val w ∧ ∃ isDir e : w64, w = PairV (#isDir) (#e) ∧
        (isDir = 1 → (∃ J, h.cur !! b = some (.dir J)) ∧ e ≠ 0) := by
    intro st e' st' hw _ _ hp Hst
    simp only [IsFsStep] at Hst
    obtain ⟨p', isDir, e, k', s', hv, -, -, hst, hres, rfl⟩ := Hst
    obtain ⟨rfl, rfl⟩ := tokPath_inj hv
    refine ⟨hst, _, rfl, isDir, e, rfl, fun h1 => ?_⟩
    rcases hres with ⟨⟨J, hJ⟩, -, he0⟩ | h0
    · rw [pathNames_child hw hp hb hbN] at hJ
      exact ⟨⟨J, hJ⟩, he0⟩
    · rw [h0] at h1; exact absurd h1 (by decide)
  iintro #Hinv #Hsi Hp Hn Hk HΦ
  iapply wp_callEndS "LstatDir" _ (by simp [val.isPanic]) R k s0 q
    iprop(osPathS (L := L) R d dq j ∗ osNames (L := L) j (.only [b]) dqn h)
    (fun st => PathNames st d j (.only [b]) h)
    (fun w => ∃ isDir e : w64, w = PairV (#isDir) (#e) ∧
      (isDir = 1 → (∃ J, h.cur !! b = some (.dir J)) ∧ e ≠ 0))
    (fun st Γn hR hcoh => pathNames_of R d dq j _ dqn h st Γn hR hcoh) hprog hpost hE hE' Φ
    $$ Hinv Hsi [Hp Hn] Hk
  · isplitl [Hp]
    · iexact Hp
    · iexact Hn
  iintro %w %hW Hq ⟨Hp, Hn⟩
  obtain ⟨isDir, e, rfl, h1⟩ := hW
  iapply HΦ $$ %isDir %e %h1 Hq Hp Hn

theorem wp_osUnlinkS_none' (R : Roots) (d b : GoString) (j : Ino) (dq dqn : DFrac) (h : NamesH)
    (k s0 : Nat) (q : Qp) (hb : NameOk b) (hi : ∀ i, h.cur !! b ≠ some (.file i))
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j (.only [b]) dqn h -∗ osCallS (L := L) k s0 q -∗
      (∀ e : w64, ⌜e ≠ 0⌝ -∗ osCallPerm (L := L) q -∗ osPathS (L := L) R d dq j -∗
        osNames (L := L) j (.only [b]) dqn h -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Unlink" (Val (PairV (osTokV k) (#(child d b))))) @ s; E {{ Φ }} := by
  have hbN : (NameSet.only [b]).Mem b := by simp [NameSet.Mem]
  have hprog : ∀ st, FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      PathNames st d j (.only [b]) h →
      ∃ e', IsFsStep "Unlink" (PairV (osTokV k) (#(child d b))) st e' (st.metaEnd k) :=
    fun st _ _ hcall hp => ⟨_, child d b, k, s0, rfl, treeName_child hp.1 hb, hcall,
      Or.inr ⟨1, by decide, rfl, rfl⟩⟩
  have hpost : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      PathNames st d j (.only [b]) h →
      IsFsStep "Unlink" (PairV (osTokV k) (#(child d b))) st e' st' →
      st' = st.metaEnd k ∧ ∃ w, e' = Val w ∧ ∃ e : w64, e ≠ 0 ∧ w = #e := by
    intro st e' st' hw _ _ hp Hst
    simp only [IsFsStep] at Hst
    obtain ⟨p', k', s', hv, -, -, hres⟩ := Hst
    obtain ⟨rfl, rfl⟩ := tokPath_inj hv
    rcases hres with ⟨i, -, -, hl, -⟩ | ⟨e, he0, rfl, rfl⟩
    · rw [pathNames_child hw hp hb hbN] at hl; exact absurd hl (hi i)
    · exact ⟨rfl, _, rfl, e, he0, rfl⟩
  iintro #Hinv #Hsi Hp Hn Hk HΦ
  iapply wp_callEndS "Unlink" _ (by simp [val.isPanic]) R k s0 q
    iprop(osPathS (L := L) R d dq j ∗ osNames (L := L) j (.only [b]) dqn h)
    (fun st => PathNames st d j (.only [b]) h) (fun w => ∃ e : w64, e ≠ 0 ∧ w = #e)
    (fun st Γn hR hcoh => pathNames_of R d dq j _ dqn h st Γn hR hcoh) hprog hpost hE hE' Φ
    $$ Hinv Hsi [Hp Hn] Hk
  · isplitl [Hp]
    · iexact Hp
    · iexact Hn
  iintro %w %hW Hq ⟨Hp, Hn⟩
  obtain ⟨e, he, rfl⟩ := hW
  iapply HΦ $$ %e %he Hq Hp Hn

theorem wp_osRmdirS_none' (R : Roots) (d b : GoString) (j : Ino) (dq dqn : DFrac) (h : NamesH)
    (k s0 : Nat) (q : Qp) (hb : NameOk b) (hi : ∀ J, h.cur !! b ≠ some (.dir J))
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j (.only [b]) dqn h -∗ osCallS (L := L) k s0 q -∗
      (∀ e : w64, ⌜e ≠ 0⌝ -∗ osCallPerm (L := L) q -∗ osPathS (L := L) R d dq j -∗
        osNames (L := L) j (.only [b]) dqn h -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Rmdir" (Val (PairV (osTokV k) (#(child d b))))) @ s; E {{ Φ }} := by
  have hbN : (NameSet.only [b]).Mem b := by simp [NameSet.Mem]
  have hprog : ∀ st, FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      PathNames st d j (.only [b]) h →
      ∃ e', IsFsStep "Rmdir" (PairV (osTokV k) (#(child d b))) st e' (st.metaEnd k) :=
    fun st _ _ hcall hp => ⟨_, child d b, k, s0, rfl, treeName_child hp.1 hb, hcall,
      Or.inr ⟨1, by decide, rfl, rfl⟩⟩
  have hpost : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      PathNames st d j (.only [b]) h →
      IsFsStep "Rmdir" (PairV (osTokV k) (#(child d b))) st e' st' →
      st' = st.metaEnd k ∧ ∃ w, e' = Val w ∧ ∃ e : w64, e ≠ 0 ∧ w = #e := by
    intro st e' st' hw _ _ hp Hst
    simp only [IsFsStep] at Hst
    obtain ⟨p', k', s', hv, -, -, hres⟩ := Hst
    obtain ⟨rfl, rfl⟩ := tokPath_inj hv
    rcases hres with ⟨J, -, -, ⟨hl, -⟩, -⟩ | ⟨e, he0, rfl, rfl⟩
    · rw [pathNames_child hw hp hb hbN] at hl; exact absurd hl (hi J)
    · exact ⟨rfl, _, rfl, e, he0, rfl⟩
  iintro #Hinv #Hsi Hp Hn Hk HΦ
  iapply wp_callEndS "Rmdir" _ (by simp [val.isPanic]) R k s0 q
    iprop(osPathS (L := L) R d dq j ∗ osNames (L := L) j (.only [b]) dqn h)
    (fun st => PathNames st d j (.only [b]) h) (fun w => ∃ e : w64, e ≠ 0 ∧ w = #e)
    (fun st Γn hR hcoh => pathNames_of R d dq j _ dqn h st Γn hR hcoh) hprog hpost hE hE' Φ
    $$ Hinv Hsi [Hp Hn] Hk
  · isplitl [Hp]
    · iexact Hp
    · iexact Hn
  iintro %w %hW Hq ⟨Hp, Hn⟩
  obtain ⟨e, he, rfl⟩ := hW
  iapply HΦ $$ %e %he Hq Hp Hn

theorem wp_osRenameAbsentS' (R : Roots) (d bs d' bt : GoString) (j j' : Ino) (N : NameSet)
    (dq dq' dqn : DFrac) (h : NamesH) (k s0 : Nat) (q : Qp) (hbs : NameOk bs) (hbt : NameOk bt)
    (hN : N.Mem bs) (hsrc : h.cur !! bs = none) (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osPathS (L := L) R d' dq' j' -∗ osNames (L := L) j N dqn h -∗ osCallS (L := L) k s0 q -∗
      (∀ e : w64, ⌜e ≠ 0⌝ -∗ osCallPerm (L := L) q -∗ osPathS (L := L) R d dq j -∗
        osPathS (L := L) R d' dq' j' -∗ osNames (L := L) j N dqn h -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Rename" (Val (PairV (osTokV k)
        (PairV (#(child d bs)) (#(child d' bt)))))) @ s; E {{ Φ }} := by
  have hprog : ∀ st, FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      (PathNames st d j N h ∧ st.lookup d' = some (.dir j')) →
      ∃ e', IsFsStep "Rename" (PairV (osTokV k) (PairV (#(child d bs)) (#(child d' bt)))) st e'
        (st.metaEnd k) := by
    intro st hw _ hcall ⟨hp, hd'⟩
    have hnone : st.lookup (child d bs) = none := by rw [pathNames_child hw hp hbs hN, hsrc]
    refine ⟨_, child d bs, child d' bt, k, s0, rfl, treeName_child hp.1 hbs,
      treeName_child hd' hbt, hcall, fun ⟨J, hJ⟩ => ?_, Or.inr (Or.inr ⟨1, by decide, rfl, rfl⟩)⟩
    rw [hnone] at hJ; cases hJ
  have hpost : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      (PathNames st d j N h ∧ st.lookup d' = some (.dir j')) →
      IsFsStep "Rename" (PairV (osTokV k) (PairV (#(child d bs)) (#(child d' bt)))) st e' st' →
      st' = st.metaEnd k ∧ ∃ w, e' = Val w ∧ ∃ e : w64, e ≠ 0 ∧ w = #e := by
    intro st e' st' hw _ _ ⟨hp, _⟩ Hst
    have hnone : st.lookup (child d bs) = none := by rw [pathNames_child hw hp hbs hN, hsrc]
    simp only [IsFsStep] at Hst
    obtain ⟨s', t', k', st0, hv, -, -, -, -, hres⟩ := Hst
    obtain ⟨rfl, rfl, rfl⟩ := tokPair_inj hv
    rcases hres with ⟨⟨-, -, -, hm⟩, -⟩ | ⟨-, hne, -⟩ | ⟨e, he0, rfl, rfl⟩
    · rw [hnone] at hm; exact hm.elim
    · exact absurd hnone hne
    · exact ⟨rfl, _, rfl, e, he0, rfl⟩
  have hF : ∀ st Γn, st.fs.roots = R → NamesCoh (st.fs.treeDur, st.fs.metaLog) Γn →
      ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γn -∗
        iprop(osPathS (L := L) R d dq j ∗ osPathS (L := L) R d' dq' j' ∗
          osNames (L := L) j N dqn h) -∗ ⌜PathNames st d j N h ∧ st.lookup d' = some (.dir j')⌝ := by
    intro st Γn hR hcoh
    iintro HA ⟨Hp, Hp', Hn⟩
    icases osPathS_lookup hR hcoh d dq j $$ HA Hp with %h1
    icases osPathS_lookup hR hcoh d' dq' j' $$ HA Hp' with %h1'
    icases osNames_entry hcoh j N dqn h $$ HA Hn with %h2
    ipureintro; exact ⟨⟨h1, h2⟩, h1'⟩
  iintro #Hinv #Hsi Hp Hp' Hn Hk HΦ
  iapply wp_callEndS "Rename" _ (by simp [val.isPanic]) R k s0 q
    iprop(osPathS (L := L) R d dq j ∗ osPathS (L := L) R d' dq' j' ∗ osNames (L := L) j N dqn h)
    (fun st => PathNames st d j N h ∧ st.lookup d' = some (.dir j'))
    (fun w => ∃ e : w64, e ≠ 0 ∧ w = #e) hF hprog hpost hE hE' Φ
    $$ Hinv Hsi [Hp Hp' Hn] Hk
  · isplitl [Hp]
    · iexact Hp
    isplitl [Hp']
    · iexact Hp'
    · iexact Hn
  iintro %w %hW Hq ⟨Hp, Hp', Hn⟩
  obtain ⟨e, he, rfl⟩ := hW
  iapply HΦ $$ %e %he Hq Hp Hp' Hn

end specs

end Fs
end Perennial

end
