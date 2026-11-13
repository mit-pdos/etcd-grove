/-
Every step of the Linux file extension keeps the committed entries of the tree's log committed (a
directory `fsync` only adds to them; `IsFsStep`, `Impl.lean`). Untrusted.
-/
module

public import GooseLang.Ext.Fs.Impl

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

/-- `st'` has every entry `st` has committed committed. -/
def CommitGrows (st st' : OsState) : Prop := ∀ y, st.fs.committed y → st'.fs.committed y

theorem commitGrows_of_eq {st st' : OsState} (h : st'.fs.committed = st.fs.committed) :
    CommitGrows st st' := fun _ hy => h ▸ hy

theorem commitGrows_refl (st : OsState) : CommitGrows st st := fun _ hy => hy

theorem commitGrows_trans {st st' st'' : OsState} (h1 : CommitGrows st st')
    (h2 : CommitGrows st' st'') : CommitGrows st st'' := fun y hy => h2 y (h1 y hy)

@[simp] theorem committed_setFile (st : OsState) (i : Ino) (f : OsFile) :
    (st.setFile i f).fs.committed = st.fs.committed := rfl
@[simp] theorem committed_stampFile (st : OsState) (i : Ino) (g : Nat → OsFile) :
    (st.stampFile i g).fs.committed = st.fs.committed := rfl
@[simp] theorem committed_setProc (st : OsState) (p : ProcState) :
    (st.setProc p).fs.committed = st.fs.committed := rfl
@[simp] theorem committed_metaEnd (st : OsState) (t : Nat) :
    (st.metaEnd t).fs.committed = st.fs.committed := rfl
@[simp] theorem committed_metaDo (st : OsState) (o : MetaOp) (s : Nat) :
    (st.metaDo o s).fs.committed = st.fs.committed := rfl
@[simp] theorem committed_takeIno (st : OsState) :
    st.takeIno.fs.committed = st.fs.committed := rfl
@[simp] theorem committed_doneInflight (st : OsState) (t : Nat) :
    (st.doneInflight t).fs.committed = st.fs.committed := rfl
@[simp] theorem committed_addInflight (st : OsState) (t : Nat) (c : OsChange) :
    (st.addInflight t c).fs.committed = st.fs.committed := rfl

theorem openEffect_committed {st : OsState} {p : GoString} {acc : Nat} {creat trunc : Bool}
    {start : Nat} {st1 : OsState} {tgt : Node} (h : OpenEffect st p acc creat trunc start st1 tgt) :
    st1.fs.committed = st.fs.committed := by
  unfold OpenEffect at h
  split at h
  · rw [h.2.2.2.1]
  · obtain ⟨⟨f, -, rfl⟩, -⟩ := h
    split <;> rfl
  · obtain ⟨-, j, b, -, rfl, -⟩ := h
    rfl

section
variable [GooseExts] [GoGlobalContext]

/-- **Every step keeps the committed entries committed.** -/
theorem isFsStep_commitGrows {o : String} {v : val} {st st' : OsState} {e' : Expr}
    (h : IsFsStep o v st e' st') : CommitGrows st st' := by
  intro y hy
  unfold IsFsStep at h
  split at h
  · obtain ⟨p, fl, t, start, -, -, -, -, -, hc⟩ := h
    rcases hc with ⟨st1, tgt, fd, he, -, rfl, -⟩ | ⟨e, -, -, rfl | ⟨tgt, he⟩⟩
    · have h1 := openEffect_committed he
      cases tgt <;> (show st1.fs.committed y; rw [h1]; exact hy)
    · exact hy
    · rw [openEffect_committed he]; exact hy
  all_goals (try simp only [] at h)
  all_goals (grind [OsState.commitAll, openEffect_committed, committed_setFile,
    committed_stampFile, committed_setProc, committed_metaEnd, committed_metaDo, committed_takeIno,
    committed_doneInflight, committed_addInflight])

/-- **Every step keeps the committed entries committed** (`FsStep`). -/
theorem fsStep_commitGrows {o : String} {v : val} {h : GMap Loc (NonAtomic val)} {st st' : OsState}
    {e' : Expr} {h' : GMap Loc (NonAtomic val)} (hs : FsStep o v h st () e' h' st' ()) :
    CommitGrows st st' := isFsStep_commitGrows hs.1

end

end Fs
end Perennial

end
