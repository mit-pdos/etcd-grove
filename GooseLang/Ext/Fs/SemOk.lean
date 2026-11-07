/-
The program logic's specs hold for any semantics of the extension whose steps are steps of the
extension's own (`FsStep`) and which keeps a step wherever `FsStep` has one (`FsSemOk`): a semantics
that restricts the extension's steps by a premise on the executions (an assumption about the
environment, e.g. `NoTear.lean`) and keeps a step from every state `FsStep` has one from. The specs
are stated over a semantics `S` with `[FsSemOk]`; `fs_semantics` is one. Untrusted.
-/
module

public import GooseLang.Ext.Fs.Impl

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

/-- `S`'s steps are `FsStep`s, and `S` has a step from every state (with mappings that do not
overlap, as every reachable state's) and operation `FsStep` has one from. -/
class FsSemOk [S : ExtSemantics fsExt] : Prop where
  step_sub : ∀ [GooseExts] [GoGlobalContext] (o : String) (v : val) (h : GMap Loc (NonAtomic val))
    (st : OsState) (g : Unit) (e' : Expr) (h' : GMap Loc (NonAtomic val)) (st' : OsState) (g' : Unit),
    S.step o v h st g e' h' st' g' → FsStep o v h st g e' h' st' g'
  step_ex : ∀ [GooseExts] [GoGlobalContext] (o : String) (v : val) (h : GMap Loc (NonAtomic val))
    (st : OsState) (g : Unit) (e' : Expr) (h' : GMap Loc (NonAtomic val)) (st' : OsState) (g' : Unit),
    (∀ l i b i' b', MapsTo st l i b → MapsTo st l i' b' → i = i' ∧ b = b') →
    FsStep o v h st g e' h' st' g' →
      ∃ e'' h'' st'' g'', S.step o v h st g e'' h'' st'' g''

instance fs_semantics_ok : @FsSemOk fs_semantics where
  step_sub _ _ _ _ _ _ _ _ _ hs := hs
  step_ex _ _ _ _ _ _ _ _ _ _ hs := ⟨_, _, _, _, hs⟩

end Fs
end Perennial

end
