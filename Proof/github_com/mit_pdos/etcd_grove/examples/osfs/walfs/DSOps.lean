/-
Two extension-level specs of the tree's shared view that `GooseLang/Ext/Fs/TreeShared.lean` does
not state: `unlink(2)` and `rmdir(2)` of `d/b/c` where `d/b` holds no directory (absent, or a file;
a fraction of the claim on `b` of `d`'s directory shows it). Both fail with no effect: the
extension's step removes only a name whose parent is a directory (`OsState.parent`). `dirswap`'s
`Create` makes these calls (`os.Remove(dir/wal.tmp/seg)` where `wal.tmp` may be absent or a file).
Proved over `wp_callEndS`, as `TreeSharedCallEnd.lean`'s are. Untrusted.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.DSCheck
public import GooseLang.Ext.Fs.TreeSharedCallEnd

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_walfs
namespace DS

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

theorem parent_child_noDir {st : OsState} {d b : GoString} (hb : NameOk b)
    (hd : ∀ J, st.lookup d ≠ some (.dir J)) : st.parent (child d b) = none := by
  unfold OsState.parent
  rw [parentOf_child' d b hb]
  cases h : st.lookup d with
  | none => simp only [h]
  | some n =>
    cases n with
    | file i => simp only [h]
    | dir J => exact absurd h (hd J)

theorem treeName_child2 {st : OsState} {d b c : GoString} {j : Ino}
    (hd : st.lookup d = some (.dir j)) (hb : NameOk b) (hc : NameOk c) :
    st.TreeName (child (child d b) c) := by
  obtain ⟨r, j0, cs, hrj, hcs, rfl, -⟩ := lookup_some hd
  refine ⟨(r, j0), hrj, cs ++ [b] ++ [c], by simp, ?_, by rw [joinPath_snoc, joinPath_snoc]⟩
  intro x hx
  simp only [List.mem_append, List.mem_singleton] at hx
  rcases hx with (h | rfl) | rfl
  · exact hcs x h
  · exact hb
  · exact hc

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- The calls on the names of a spine's directory's names have its key. -/
theorem osPathS_callKey2 (R : Roots) (d : GoString) (dq : DFrac) (j : Ino) :
    osPathS (L := L) R d dq j ⊢
      osPathS (L := L) R d dq j ∗ ⌜∀ b c, callKey R (child (child d b) c) = callKey R d⌝ := by
  unfold osPathS
  iintro ⟨%r, %j0, %cs, %hp, Hs⟩
  isplitl [Hs]
  · iexists r, j0, cs; iframe; ipureintro; exact hp
  · ipureintro
    obtain ⟨hR, hr, -, rfl⟩ := hp
    intro b c
    rw [callKey_eq hR hr (by rw [← joinPath_snoc, ← joinPath_snoc]; exact isUnder_joinPath _ _),
      callKey_eq hR hr (isUnder_joinPath _ _)]

theorem pathNames_noDir {st : OsState} {d b : GoString} {j : Ino} {h : NamesH} (hw : FsTreeWf st)
    (hp : PathNames st d j (.only [b]) h) (hb : NameOk b) (hnd : ∀ J, h.cur !! b ≠ some (.dir J)) :
    ∀ J, st.lookup (child d b) ≠ some (.dir J) := by
  intro J hJ
  rw [pathNames_child hw hp hb (by simp [NameSet.Mem])] at hJ
  exact hnd J hJ

/-- **`unlink(2)`** of `d/b/c`, `d/b` no directory: an errno, no effect. -/
theorem wp_osUnlinkS_noDir (R : Roots) (d b c : GoString) (j : Ino) (dq dqn : DFrac) (h : NamesH)
    (k s0 : Nat) (q : Qp) (hb : NameOk b) (hc : NameOk c) (hnd : ∀ J, h.cur !! b ≠ some (.dir J))
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j (.only [b]) dqn h -∗ osCallS (L := L) k s0 (child (child d b) c) q -∗
      (∀ e : w64, ⌜e ≠ 0⌝ -∗ osCallPerm (L := L) (callKey R d) q -∗ osPathS (L := L) R d dq j -∗
        osNames (L := L) j (.only [b]) dqn h -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Unlink" (Val (PairV (osTokV k) (#(child (child d b) c)))))
        @ s; E {{ Φ }} := by
  have hprog : ∀ st, FsTreeWf st → st.fs.roots = R →
      st.proc.calls !! k = some (s0, child (child d b) c) → PathNames st d j (.only [b]) h →
      ∃ e', IsFsStep "Unlink" (PairV (osTokV k) (#(child (child d b) c))) st e' (st.metaEnd k) :=
    fun st _ _ hcall hp => ⟨_, child (child d b) c, k, s0, rfl, treeName_child2 hp.1 hb hc, hcall,
      Or.inr ⟨1, by decide, rfl, rfl⟩⟩
  have hpost : ∀ st e' st', FsTreeWf st → st.fs.roots = R →
      st.proc.calls !! k = some (s0, child (child d b) c) → PathNames st d j (.only [b]) h →
      IsFsStep "Unlink" (PairV (osTokV k) (#(child (child d b) c))) st e' st' →
      st' = st.metaEnd k ∧ ∃ w, e' = Val w ∧ ∃ e : w64, e ≠ 0 ∧ w = #e := by
    intro st e' st' hw _ _ hp Hst
    simp only [IsFsStep] at Hst
    obtain ⟨p', k', s', hv, -, -, hres⟩ := Hst
    obtain ⟨rfl, rfl⟩ := tokPath_inj hv
    rcases hres with ⟨i, j0, b0, -, hpar, -⟩ | ⟨e, he0, rfl, rfl⟩
    · rw [parent_child_noDir hc (pathNames_noDir hw hp hb hnd)] at hpar; cases hpar
    · exact ⟨rfl, _, rfl, e, he0, rfl⟩
  iintro #Hinv #Hsi Hp Hn Hk HΦ
  iapply wp_callEndS "Unlink" _ (by simp [val.isPanic]) R k s0 (child (child d b) c) q
    iprop(osPathS (L := L) R d dq j ∗ osNames (L := L) j (.only [b]) dqn h)
    (fun st => PathNames st d j (.only [b]) h) (fun w => ∃ e : w64, e ≠ 0 ∧ w = #e)
    (fun st Γn hR hcoh => pathNames_of R d dq j _ dqn h st Γn hR hcoh) hprog hpost hE hE' Φ
    $$ Hinv Hsi [Hp Hn] Hk
  · isplitl [Hp]
    · iexact Hp
    · iexact Hn
  iintro %w %hW Hq ⟨Hp, Hn⟩
  obtain ⟨e, he, rfl⟩ := hW
  icases osPathS_callKey2 R d dq j $$ Hp with ⟨Hp, %hk⟩
  iapply HΦ $$ %e %he [Hq] Hp Hn
  iapply osCallPerm_congr q (hk b c) $$ Hq

/-- **`rmdir(2)`** of `d/b/c`, `d/b` no directory: an errno, no effect. -/
theorem wp_osRmdirS_noDir (R : Roots) (d b c : GoString) (j : Ino) (dq dqn : DFrac) (h : NamesH)
    (k s0 : Nat) (q : Qp) (hb : NameOk b) (hc : NameOk c) (hnd : ∀ J, h.cur !! b ≠ some (.dir J))
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j (.only [b]) dqn h -∗ osCallS (L := L) k s0 (child (child d b) c) q -∗
      (∀ e : w64, ⌜e ≠ 0⌝ -∗ osCallPerm (L := L) (callKey R d) q -∗ osPathS (L := L) R d dq j -∗
        osNames (L := L) j (.only [b]) dqn h -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Rmdir" (Val (PairV (osTokV k) (#(child (child d b) c)))))
        @ s; E {{ Φ }} := by
  have hprog : ∀ st, FsTreeWf st → st.fs.roots = R →
      st.proc.calls !! k = some (s0, child (child d b) c) → PathNames st d j (.only [b]) h →
      ∃ e', IsFsStep "Rmdir" (PairV (osTokV k) (#(child (child d b) c))) st e' (st.metaEnd k) :=
    fun st _ _ hcall hp => ⟨_, child (child d b) c, k, s0, rfl, treeName_child2 hp.1 hb hc, hcall,
      Or.inr ⟨1, by decide, rfl, rfl⟩⟩
  have hpost : ∀ st e' st', FsTreeWf st → st.fs.roots = R →
      st.proc.calls !! k = some (s0, child (child d b) c) → PathNames st d j (.only [b]) h →
      IsFsStep "Rmdir" (PairV (osTokV k) (#(child (child d b) c))) st e' st' →
      st' = st.metaEnd k ∧ ∃ w, e' = Val w ∧ ∃ e : w64, e ≠ 0 ∧ w = #e := by
    intro st e' st' hw _ _ hp Hst
    simp only [IsFsStep] at Hst
    obtain ⟨p', k', s', hv, -, -, hres⟩ := Hst
    obtain ⟨rfl, rfl⟩ := tokPath_inj hv
    rcases hres with ⟨j', j0, b0, -, hpar, -⟩ | ⟨e, he0, rfl, rfl⟩
    · rw [parent_child_noDir hc (pathNames_noDir hw hp hb hnd)] at hpar; cases hpar
    · exact ⟨rfl, _, rfl, e, he0, rfl⟩
  iintro #Hinv #Hsi Hp Hn Hk HΦ
  iapply wp_callEndS "Rmdir" _ (by simp [val.isPanic]) R k s0 (child (child d b) c) q
    iprop(osPathS (L := L) R d dq j ∗ osNames (L := L) j (.only [b]) dqn h)
    (fun st => PathNames st d j (.only [b]) h) (fun w => ∃ e : w64, e ≠ 0 ∧ w = #e)
    (fun st Γn hR hcoh => pathNames_of R d dq j _ dqn h st Γn hR hcoh) hprog hpost hE hE' Φ
    $$ Hinv Hsi [Hp Hn] Hk
  · isplitl [Hp]
    · iexact Hp
    · iexact Hn
  iintro %w %hW Hq ⟨Hp, Hn⟩
  obtain ⟨e, he, rfl⟩ := hW
  icases osPathS_callKey2 R d dq j $$ Hp with ⟨Hp, %hk⟩
  iapply HΦ $$ %e %he [Hq] Hp Hn
  iapply osCallPerm_congr q (hk b c) $$ Hq

end specs

end DS
end osfs_walfs
end EtcdGrove
end Perennial

end
