/-
Two metadata specs the file extension v2 does not have (`GooseLang/Ext/Fs/TreeSpecsMeta.lean` has
them only for a name in a directory): `unlink(2)` and `rmdir(2)` of `d/b` where `d` is no
directory (absent, or a file). Both fail, the history unchanged: the extension's step removes
only a name whose parent is a directory (`OsState.parent`). `dirswap`'s `Create` makes these calls
(`os.Remove(dir/wal.tmp/seg)` where `wal.tmp` may be absent). Proved from `wp_metaStep`, as the
extension's own specs are; candidates for the extension.
-/
module

public import GooseLang.Ext.Fs.TreeSpecsMeta

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

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt fsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- **`unlink(2)`** of `d/b`, a name below a root, `d` no directory, by the call `k`, with the
rest of the history: it fails, the history unchanged. -/
theorem wp_osUnlinkNoDir (d b : GoString) (hb : NameOk b) (R : Roots) (V : Hist) (q1 q : Qp)
    (k s' : Nat) (hq : q1 + q = 1) (hn : ∃ rj ∈ R, CanonBelow rj.1 (child d b))
    (hd : ∀ J, lookupH R V d ≠ some (.dir J)) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osTree (L := L) (DFrac.own q1) R V -∗ osCall (L := L) k s' q -∗
      (∀ (e : w64) (V' : Hist), ⌜e ≠ 0 ∧ V' = V⌝ -∗
        osTree (L := L) (DFrac.own 1) R V' -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Unlink" (Val (PairV (osTokV k) (#(child d b))))) @ s; E {{ Φ }} := by
  refine wp_metaStep "Unlink" _ (by simp [val.isPanic]) R V q1 q k s' hq _ ?_ ?_ hE Φ
  · intro st hp
    have htn : st.TreeName (child d b) := by rw [OsState.TreeName, hp.roots]; exact hn
    exact ⟨_, st.metaEnd k, ⟨child d b, k, s', rfl, htn,
      by rw [hp.calls]; simp, .inr ⟨W64 1, by decide, rfl, rfl⟩⟩, ⟨rfl, rfl, rfl, rfl⟩⟩
  · intro st e' st' hp hst
    have hd' : ∀ J, st.lookup d ≠ some (.dir J) := fun J => by rw [lookup_pre hp d]; exact hd J
    obtain ⟨p, k', start, hv, -, hk', hres⟩ := hst
    obtain ⟨rfl, rfl⟩ := tokPath_inj hv
    obtain rfl := start_eq hp hk'
    rcases hres with ⟨i, j0, b0, -, hpar, -⟩ | ⟨e, he, rfl, rfl⟩
    · rw [parent_child_noDir hb hd'] at hpar; cases hpar
    · exact ⟨e, rfl, (metaPost_end hp).1, he, (metaPost_end hp).2⟩

/-- **`rmdir(2)`** of `d/b`, a name below a root, `d` no directory, by the call `k`, with the
rest of the history: it fails, the history unchanged. -/
theorem wp_osRmdirNoDir (d b : GoString) (hb : NameOk b) (R : Roots) (V : Hist) (q1 q : Qp)
    (k s' : Nat) (hq : q1 + q = 1) (hn : ∃ rj ∈ R, CanonBelow rj.1 (child d b))
    (hd : ∀ J, lookupH R V d ≠ some (.dir J)) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osTree (L := L) (DFrac.own q1) R V -∗ osCall (L := L) k s' q -∗
      (∀ (e : w64) (V' : Hist), ⌜e ≠ 0 ∧ V' = V⌝ -∗
        osTree (L := L) (DFrac.own 1) R V' -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Rmdir" (Val (PairV (osTokV k) (#(child d b))))) @ s; E {{ Φ }} := by
  refine wp_metaStep "Rmdir" _ (by simp [val.isPanic]) R V q1 q k s' hq _ ?_ ?_ hE Φ
  · intro st hp
    have htn : st.TreeName (child d b) := by rw [OsState.TreeName, hp.roots]; exact hn
    exact ⟨_, st.metaEnd k, ⟨child d b, k, s', rfl, htn,
      by rw [hp.calls]; simp, .inr ⟨W64 1, by decide, rfl, rfl⟩⟩, ⟨rfl, rfl, rfl, rfl⟩⟩
  · intro st e' st' hp hst
    have hd' : ∀ J, st.lookup d ≠ some (.dir J) := fun J => by rw [lookup_pre hp d]; exact hd J
    obtain ⟨p, k', start, hv, -, hk', hres⟩ := hst
    obtain ⟨rfl, rfl⟩ := tokPath_inj hv
    obtain rfl := start_eq hp hk'
    rcases hres with ⟨j', j0, b0, -, hpar, -⟩ | ⟨e, he, rfl, rfl⟩
    · rw [parent_child_noDir hb hd'] at hpar; cases hpar
    · exact ⟨e, rfl, (metaPost_end hp).1, he, (metaPost_end hp).2⟩

end specs

end DS
end osfs_walfs
end EtcdGrove
end Perennial

end
