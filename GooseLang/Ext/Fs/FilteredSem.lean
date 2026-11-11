/-
The program logic over the semantics restricted by premises (`Premises.lean`, `fsSemWithS SQ Q`).
The program logic's specs hold over it when `SQ` keeps a step from every
state `FsStep` has one from (`StepKeeps`, giving `FsSemOk`). Untrusted.
-/
module

public import GooseLang.Ext.Fs.CrashTok
public import GooseLang.Ext.Fs.Premises

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

/-- `SQ` keeps a step from every state, with mappings that do not overlap, that `FsStep` has one
from. -/
def StepKeeps (SQ : StepPrem) : Prop :=
  ∀ [GooseExts] [GoGlobalContext] (o : String) (v : val) (h : GMap Loc (NonAtomic val))
    (st : OsState) (e' : Expr) (h' : GMap Loc (NonAtomic val)) (st' : OsState),
    (∀ l i b i' b', MapsTo st l i b → MapsTo st l i' b' → i = i' ∧ b = b') →
    FsStep o v h st () e' h' st' () →
      ∃ e'' h'' st'', FsStep o v h st () e'' h'' st'' () ∧ SQ o v st e'' st''

theorem fsSemWithS_ok (SQ : StepPrem) (Q : OsState → OsState → Prop) (hk : StepKeeps SQ) :
    letI := fsSemWithS SQ Q; FsSemOk := by
  letI := fsSemWithS SQ Q
  refine ⟨fun _ _ _ _ _ _ _ _ _ hs => hs.1, ?_⟩
  intro _ _ o v h st g e' h' st' g' hd hs
  cases g; cases g'
  obtain ⟨e'', h'', st'', h1, h2⟩ := hk o v h st e' h' st' hd hs
  exact ⟨e'', h'', st'', (), h1, h2⟩

/-- Every step of the semantics satisfies `SQ`: what a proof over `fsSemWithS SQ Q` may use of
the premise on steps (`wp_os_stepX`'s continuation gets the semantics' step). -/
class FsStepSat (SQ : StepPrem) [S : ExtSemantics fsExt] : Prop where
  sat : ∀ [GooseExts] [GoGlobalContext] (o : String) (v : val) (h : GMap Loc (NonAtomic val))
    (st : OsState) (g : Unit) (e' : Expr) (h' : GMap Loc (NonAtomic val)) (st' : OsState) (g' : Unit),
    S.step o v h st g e' h' st' g' → SQ o v st e' st'

theorem fsSemWithS_sat (SQ : StepPrem) (Q : OsState → OsState → Prop) :
    letI := fsSemWithS SQ Q; FsStepSat SQ := by
  letI := fsSemWithS SQ Q
  exact ⟨fun _ _ _ _ _ _ _ _ _ hs => hs.2⟩

/-- The crash interpretation of `fsSemWithS SQ Q`: as under the premise `Q` alone (steps are no
part of it). -/
@[instance_reducible] def fs_crash_interpS (SQ : StepPrem) (Q : OsState → OsState → Prop) :
    @ExtCrashInterp fsExt (fsSemWithS SQ Q) fs_interp :=
  @ExtCrashInterp.mk fsExt (fsSemWithS SQ Q) fs_interp (fun hL hL' => osCrashStart Q hL hL')
    (fun _ hPre hL st st' (hc : OsCrash st st' ∧ Q st st') =>
      os_local_crash hL Q hPre st st' hc.1 hc.2)

end Fs
end Perennial

end
