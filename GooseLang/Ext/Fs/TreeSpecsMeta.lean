/-
WP specs of the directory tree's metadata steps (`Impl.lean`): `Unlink`, `Rmdir`, `Mkdir`, `Rename`
(of a file; of a directory onto an absent name in the same directory; of an absent source, the
retry case). Untrusted.

Each takes the caller's fraction `q1` of the tree's history and its call `osCall k s q`, with
`q1 + q = 1`: the step holds the whole history (`wp_metaStep`), so no directory fd is open and no
other call is in flight, and the new history is the old one, or the old one with the step's
operation logged (`Hist.push`), its start the old history's length (the log stays `Sequential`).
What a path names is `lookupH R V p`; the specs name the directory a path is in by the path's
parent, `d`, of inode `j` (`lookupH R V d = some (.dir j)`).
-/
module

public import GooseLang.Ext.Fs.TreeSpecs

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-! ## What a metadata step finds and leaves -/

/-- A state a metadata step of the call `k` (begun at `s'`) runs in, with the roots `R` and the
history `V`, the caller holding all of it: no directory fd, no other call. -/
structure MetaPre (st : OsState) (R : Roots) (V : Hist) (k s' : Nat) : Prop where
  wf : FsTreeWf st
  roots : st.fs.roots = R
  hist : V = (st.fs.treeDur, st.fs.metaLog)
  calls : st.proc.calls = {[k := s']}
  start : s' = st.fs.metaLog.length
  dfds : st.proc.dfds = ∅
  seq : Sequential st.fs.metaLog

/-- What a metadata step leaves: the files' part unchanged, the tree well formed, no call, no
directory fd, the log sequential. -/
structure MetaPost (st st' : OsState) : Prop where
  same : FilesSame st st'
  wf : FsTreeWf st'
  roots : st'.fs.roots = st.fs.roots
  calls : st'.proc.calls = ∅
  dfds : st'.proc.dfds = ∅
  seq : Sequential st'.fs.metaLog

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt fsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- **A metadata step**, from what it finds and leaves of the state (`hprog`: it can step; `hpost`:
each of its steps leaves an errno, a state as `MetaPost`, and the new history as `Q` says). -/
theorem wp_metaStep (op : String) (v : val) (hv : v.isPanic = false) (R : Roots) (V : Hist)
    (q1 q : Qp) (k s' : Nat) (hq : q1 + q = 1) (Q : w64 → Hist → Prop)
    (hprog : ∀ st, MetaPre st R V k s' → ∃ e' st', IsFsStep op v st e' st' ∧ FilesSame st st')
    (hpost : ∀ st e' st', MetaPre st R V k s' → IsFsStep op v st e' st' →
      ∃ e : w64, e' = Val (#e) ∧ MetaPost st st' ∧ Q e (st'.fs.treeDur, st'.fs.metaLog))
    (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osTree (L := L) (DFrac.own q1) R V -∗ osCall (L := L) k s' q -∗
      (∀ (e : w64) (V' : Hist), ⌜Q e V'⌝ -∗ osTree (L := L) (DFrac.own 1) R V' -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name op (Val v)) @ s; E {{ Φ }} := by
  iintro #Hinv Hh Hk HΦ
  iapply wp_fs_stepT op _ Φ hv hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %V0 %Γdf %Γc %h Hw Hn
  unfold osWorld treeWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases Hn with ⟨%Hns, HAd, HAdf, HAc, Hrd, Hcr⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  obtain ⟨hw, hc⟩ := Hns
  icases osTree_auth _ _ _ _ _ $$ HAd Hh with %Heq
  obtain ⟨rfl, rfl⟩ := Heq
  imod call_end _ _ Γc k s' q $$ HAd HAc Hcr Hk with ⟨%hk, HAd, HAc, Hcr, Hq⟩
  ihave Hwhole : osTree (L := L) (DFrac.own 1) st.fs.roots V $$ [Hh Hq]
  · rw [← hq]; iapply (osTree_split q1 q _ _).2; iframe
  icases whole_alone _ _ Γdf (GMap.delete k Γc) $$ Hwhole Hrd Hcr with ⟨%Hal, Hwhole, Hrd, Hcr⟩
  obtain ⟨hdf, hcl⟩ := Hal
  subst hdf
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hcalls : st.proc.calls = {[k := s']} := by
    apply GMap.ext; intro t
    rw [← hc.calls t, GMap.lookup_singleton_iff]
    by_cases ht : k = t
    · subst ht; rw [hk]; simp
    · rw [if_neg ht]
      have := congrArg (· !! t) hcl
      simp only [GMap.lookup_delete_ne _ ht, GMap.lookup_empty] at this
      rw [this]; rfl
  have hpre : MetaPre st st.fs.roots V k s' :=
    ⟨hw, rfl, hc.hist, hcalls, hc.start k _ hk, dfds_empty hc, hc.seq⟩
  imodintro
  isplitr
  · ipureintro
    obtain ⟨e', st', hs, hfs⟩ := hprog st hpre
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) hwf hfs Hag
    exact ⟨e', h, st', hs, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  obtain ⟨e, rfl, hpo, hQ⟩ := hpost st e' st' hpre Hst
  imod osWorld_filesSame (st := st) (st' := st') hpo.same Hr Hfr
    $$ [HAb HAm HAf HAt Htok Hcells Hσ] with Hw
  · unfold osWorld; iframe; ipureintro; exact ⟨hwf, hcoh⟩
  imod osTree_update _ _ (st'.fs.treeDur, st'.fs.metaLog) _ _ $$ HAd Hwhole with ⟨HAd, Hwhole⟩
  imodintro
  iexists Γb, Γm, Γf, Γt, (st'.fs.treeDur, st'.fs.metaLog), ∅, GMap.delete k Γc
  unfold osWorld
  isplitl [Hw]
  · iexact Hw
  isplitl [HAd HAdf HAc Hrd Hcr]
  · rw [hpo.roots]
    iframe
    ipureintro
    refine ⟨hpo.wf, ⟨rfl, hpo.seq, fun fd => ?_, fun fd x df hx => by simp at hx,
      fun fd x hx => by simp at hx, fun t => ?_, fun t x hx => by rw [hcl] at hx; simp at hx⟩⟩
    · rw [hpo.dfds]; simp
    · rw [hpo.calls, hcl]; simp
  iapply wp_value'
  iapply HΦ $$ %e %_ %hQ Hwhole

end specs

end Fs
end Perennial

end
