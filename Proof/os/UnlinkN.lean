/-
The extension's unlink and rmdir specs (`GooseLang/Ext/Fs/TreeSharedMeta.lean`,
`TreeSharedCallEnd.lean`) with the name in a claim on any set of names `N` (`N.Mem b`), not only
`.only [b]`: what `os.Remove.specFileSncN` (`Spec/os/RemoveN.lean`) needs to remove a segment of a
WAL directory under the directory's claim (`(j, .except X, hj)`, split between the WAL handle and the
WAL invariant; unit `locks`, session 6, `notes/wal-units/locks.md`). The proofs are the originals'
with the claim generalized. Kept here rather than in the extension so that nothing else rebuilds;
untrusted.
-/
module

public import GooseLang.Ext.Fs.TreeSharedMeta

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

theorem wp_osUnlinkSN (R : Roots) (d b : GoString) (j i : Ino) (N : NameSet) (dq : DFrac) (h : NamesH)
    (k s0 : Nat) (q : Qp) (hb : NameOk b) (hbN : N.Mem b) (hi : h.cur !! b = some (.file i)) (hs : h.next ≤ s0)
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j N (DFrac.own 1) h -∗ osCallS (L := L) k s0 q -∗
      (∀ e : w64, osCallPerm (L := L) q -∗ osPathS (L := L) R d dq j -∗
        osNamesAfter (L := L) j N h ⟨.remove j b (.file i), s0⟩ (GMap.delete b h.cur)
          (e ≠ 0) -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Unlink" (Val (PairV (osTokV k) (#(child d b))))) @ s; E {{ Φ }} := by
  let o : MetaOp := .remove j b (.file i)
  let cl : List ClaimW := [(j, N, h, restrictN N (GMap.delete b h.cur))]
  have hent : ∀ st, ClaimsAt st cl → st.tree.entry j b = some (.file i) := by
    intro st hat; rw [hat.ent _ (List.mem_singleton_self _) b hbN]; exact hi
  have hprog : ∀ st, FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → k' = k) →
      st.lookup d = some (.dir j) → ClaimsAt st cl →
      ∃ e' st', IsFsStep "Unlink" (PairV (osTokV k) (#(child d b))) st e' st' ∧ FilesSame st st' :=
    fun st _ _ hcall _ hp _ => ⟨_, st.metaEnd k, ⟨child d b, k, s0, rfl, treeName_child hp hb, hcall,
      Or.inr ⟨1, by decide, rfl, rfl⟩⟩, filesSame_metaEnd st k⟩
  have hpost : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      (q = 1 → ∀ k' s', st.proc.calls !! k' = some s' → k' = k) →
      st.lookup d = some (.dir j) → ClaimsAt st cl →
      IsFsStep "Unlink" (PairV (osTokV k) (#(child d b))) st e' st' → ∃ w, e' = Val w ∧
        ((st' = st.metaEnd k ∧ (fun w lg => ∃ e : w64, w = #e ∧ (lg = false → e ≠ 0)) w false) ∨
         (LoggedFrom st st' k s0 o ∧ (∀ x, x ∈ o.apply st.tree → x < st'.fs.nextIno) ∧
          (fun w lg => ∃ e : w64, w = #e ∧ (lg = false → e ≠ 0)) w true)) := by
    intro st e' st' hw _ hcall _ hp hat Hst
    simp only [IsFsStep] at Hst
    obtain ⟨p', k', s', hv, -, hk', hres⟩ := Hst
    obtain ⟨rfl, rfl⟩ := tokPath_inj hv
    rw [calls_start hcall hk'] at hres
    obtain ⟨htw, -, hlt⟩ := wf_tree hw
    have hlt' : ∀ x, x ∈ o.apply st.tree → x < ((st.metaEnd k).metaDo o s0).fs.nextIno := by
      intro x hx
      rcases mem_remove _ _ _ _ _ hx with rfl | hx
      · exact hlt _ (mem_of_reach htw (reach_of_lookup hp))
      · exact hlt _ hx
    rcases hres with ⟨i', j0, b0, hfi, hpar, hr⟩ | ⟨e, he, rfl, rfl⟩
    · rw [parent_child hp hb] at hpar
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hpar)
      rw [lookup_child hw.roots hp hb, hent st hat] at hfi
      cases Option.some.inj hfi
      rcases hr with ⟨rfl, rfl⟩ | ⟨e, he, rfl, rfl | rfl⟩
      · exact ⟨_, rfl, .inr ⟨loggedFrom_metaDo st k s0 o, hlt', 0, rfl, by simp⟩⟩
      · exact ⟨_, rfl, .inl ⟨rfl, e, rfl, fun _ => he⟩⟩
      · exact ⟨_, rfl, .inr ⟨loggedFrom_metaDo st k s0 o, hlt', e, rfl, by simp⟩⟩
    · exact ⟨_, rfl, .inl ⟨rfl, e, rfl, fun _ => he⟩⟩
  have htree : ∀ st, FsTreeWf st → st.fs.roots = R → st.lookup d = some (.dir j) →
      ClaimsAt st cl →
      TreeWf R (o.apply st.tree) ∧ (∀ i, Named (o.apply st.tree) i → Named st.tree i) ∧
      (∀ x, x ∈ o.apply st.tree → x ∈ st.tree ∨ x ∈ o.newDirs) ∧
      (∀ J ∈ o.newDirs, J ∉ st.tree) ∧
      (¬ o.IsDirOp → OpOk st.tree o ∧ ∀ j b i, o = .create j b i → ∀ t,
        t ≤ st.fs.metaLog.length → ¬ Named (prefTree st.fs.treeDur st.fs.metaLog t) i) ∧
      (∀ c ∈ cl, restrictN c.2.1 (entsOf (o.apply st.tree) c.1) = c.2.2.2) := by
    intro st hw hR hp hat
    obtain ⟨htw, -, -⟩ := wf_tree hw
    have hjm : j ∈ st.tree := mem_of_reach htw (reach_of_lookup hp)
    refine ⟨hR ▸ treeWf_removeFile htw (reach_of_lookup hp) (hent st hat) _,
      named_remove _ _ _ _, fun x hx => ?_, fun J hJ => by simp [o, MetaOp.newDirs] at hJ,
      fun _ => ⟨⟨hjm, hent st hat⟩, fun _ _ _ he => by simp [o] at he⟩, fun c hc => ?_⟩
    · rcases mem_remove _ _ _ _ _ hx with rfl | hx
      · exact .inl hjm
      · exact .inl hx
    · rw [List.mem_singleton] at hc; subst hc
      apply restrictN_eq_of
      intro b' hb'
      rw [entsOf_lookup, entry_remove]
      by_cases e : b = b'
      · subst e; simp
      · rw [if_neg (fun h' => e h'.2), GMap.lookup_delete_ne _ e]
        exact hat.ent _ (List.mem_singleton_self _) b' hb'
  iintro #Hinv #Hsi Hp Hn Hk HΦ
  iapply wp_logStepS "Unlink" _ (by simp [val.isPanic]) R k s0 q o cl
    (osPathS (L := L) R d dq j) (fun st => st.lookup d = some (.dir j))
    (fun w lg => ∃ e : w64, w = #e ∧ (lg = false → e ≠ 0))
    (by simp [cl]; rintro rfl; simp [NameSet.Mem] at hbN) (fun c hc => by
      rw [List.mem_singleton] at hc; subst hc
      exact ⟨b, hbN, .inl (by simp [o, MetaOp.slots])⟩)
    (by intro sl hsl; simp [o, MetaOp.slots] at hsl; subst hsl; exact ⟨_, List.mem_singleton_self _, rfl, hbN⟩)
    (by simp [cl, hs]) (by rintro ⟨J, hJ⟩; cases hJ) (by intro j b hb; simp [o, MetaOp.adds] at hb)
    (fun st Γn hR hcoh => pathS_of R d dq j st Γn hR hcoh) hprog hpost htree hE hE' Φ
    $$ Hinv Hsi Hp [Hn] Hk
  · iapply (BigSepL.bigSepL_singleton).2; iexact Hn
  iintro %w Hq Hp Hpost
  icases Hpost with (⟨%hW, Hl⟩ | ⟨%hW, %x, Hlg, Hl, -⟩)
  · obtain ⟨e, rfl, he⟩ := hW
    iapply HΦ $$ %e Hq Hp
    unfold osNamesAfter
    ileft
    isplitr
    · ipureintro; exact he rfl
    · iapply (BigSepL.bigSepL_singleton).1 $$ Hl
  · obtain ⟨e, rfl, -⟩ := hW
    iapply HΦ $$ %e Hq Hp
    unfold osNamesAfter
    iright
    iexists x
    isplitl [Hlg]
    · iexact Hlg
    · iapply (BigSepL.bigSepL_singleton).1 $$ Hl

theorem wp_osUnlinkSN_none (R : Roots) (d b : GoString) (j : Ino) (N : NameSet) (dq dqn : DFrac) (h : NamesH)
    (k s0 : Nat) (q : Qp) (hb : NameOk b) (hbN : N.Mem b) (hi : ∀ i, h.cur !! b ≠ some (.file i))
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j N dqn h -∗ osCallS (L := L) k s0 q -∗
      (∀ e : w64, ⌜e ≠ 0⌝ -∗ osCallPerm (L := L) q -∗ osPathS (L := L) R d dq j -∗
        osNames (L := L) j N dqn h -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Unlink" (Val (PairV (osTokV k) (#(child d b))))) @ s; E {{ Φ }} := by
  have hprog : ∀ st, FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      PathNames st d j N h →
      ∃ e', IsFsStep "Unlink" (PairV (osTokV k) (#(child d b))) st e' (st.metaEnd k) :=
    fun st _ _ hcall hp => ⟨_, child d b, k, s0, rfl, treeName_child hp.1 hb, hcall,
      Or.inr ⟨1, by decide, rfl, rfl⟩⟩
  have hpost : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      PathNames st d j N h →
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
    iprop(osPathS (L := L) R d dq j ∗ osNames (L := L) j N dqn h)
    (fun st => PathNames st d j N h) (fun w => ∃ e : w64, e ≠ 0 ∧ w = #e)
    (fun st Γn hR hcoh => pathNames_of R d dq j _ dqn h st Γn hR hcoh) hprog hpost hE hE' Φ
    $$ Hinv Hsi [Hp Hn] Hk
  · isplitl [Hp]
    · iexact Hp
    · iexact Hn
  iintro %w %hW Hq ⟨Hp, Hn⟩
  obtain ⟨e, he, rfl⟩ := hW
  iapply HΦ $$ %e %he Hq Hp Hn

theorem wp_osRmdirSN_none (R : Roots) (d b : GoString) (j : Ino) (N : NameSet) (dq dqn : DFrac) (h : NamesH)
    (k s0 : Nat) (q : Qp) (hb : NameOk b) (hbN : N.Mem b) (hi : ∀ J, h.cur !! b ≠ some (.dir J))
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j N dqn h -∗ osCallS (L := L) k s0 q -∗
      (∀ e : w64, ⌜e ≠ 0⌝ -∗ osCallPerm (L := L) q -∗ osPathS (L := L) R d dq j -∗
        osNames (L := L) j N dqn h -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Rmdir" (Val (PairV (osTokV k) (#(child d b))))) @ s; E {{ Φ }} := by
  have hprog : ∀ st, FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      PathNames st d j N h →
      ∃ e', IsFsStep "Rmdir" (PairV (osTokV k) (#(child d b))) st e' (st.metaEnd k) :=
    fun st _ _ hcall hp => ⟨_, child d b, k, s0, rfl, treeName_child hp.1 hb, hcall,
      Or.inr ⟨1, by decide, rfl, rfl⟩⟩
  have hpost : ∀ st e' st', FsTreeWf st → st.fs.roots = R → st.proc.calls !! k = some s0 →
      PathNames st d j N h →
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
    iprop(osPathS (L := L) R d dq j ∗ osNames (L := L) j N dqn h)
    (fun st => PathNames st d j N h) (fun w => ∃ e : w64, e ≠ 0 ∧ w = #e)
    (fun st Γn hR hcoh => pathNames_of R d dq j _ dqn h st Γn hR hcoh) hprog hpost hE hE' Φ
    $$ Hinv Hsi [Hp Hn] Hk
  · isplitl [Hp]
    · iexact Hp
    · iexact Hn
  iintro %w %hW Hq ⟨Hp, Hn⟩
  obtain ⟨e, he, rfl⟩ := hW
  iapply HΦ $$ %e %he Hq Hp Hn

end specs

end Fs
end Perennial

end
