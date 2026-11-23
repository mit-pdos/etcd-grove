/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/SyncSeq.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**A ballot's `MSync` against its own sequence `syncSeq`** (round 48, descriptor side; D64, 47-a):
the facts `handleSync` and `handleSyncEntry` need of an `MSync` `M` (`sp.syncIs γ b M`), all from
`sync_ok` (`M = recoverSync N reps = lkAlong cs`, `cs` without duplicates):

* `sp.syncSeq_fst`'s ghost form `sp.syncIs_seq`: `syncSeq M`'s ids are `syncOrder M`, and every
  entry `(y, c, D)` of `M` has `(y, c) ∈ syncSeq M` and `D ~ depsIn (syncSeq M) y`
  (`sp.lkAlong_deps_perm`, D-SWC2-4);
* `sp.locLb_syncSeq`: the replica's `locAt`s of `syncOrder M` (`takeSync_stepD`'s, at every
  replica) with the commands' `cmdIs` are `sp.locLb γ r b (syncSeq M)`. `handleSync` hands it to
  each sync entry (`syncMP`), whose descriptor's `ldrPrefix` it is.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncFacts
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Local
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Model.SyncDeps
import all Spec.swift.Inv

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-! ## Pure -/

theorem sp.fmFst_sublist {β : Type} (f : sp.CmdId → Option (sp.CmdId × β))
    (hf : ∀ c p, f c = some p → p.1 = c) :
    ∀ O : List sp.CmdId, ((O.filterMap f).map Prod.fst).Sublist O
  | [] => by simp
  | c :: O => by
    rw [List.filterMap_cons]
    cases h : f c with
    | none => exact (sp.fmFst_sublist f hf O).cons c
    | some p =>
      simp only [List.map_cons]
      rw [hf c p h]
      exact (sp.fmFst_sublist f hf O).cons_cons c

/-- `recoverSync` is `lkAlong` of a sequence without duplicates. -/
theorem sp.recoverSync_lk (N : Nat) (reps : List (Nat × sp.Report)) :
    ∃ cs : sp.Seq, (cs.map Prod.fst).Nodup ∧ sp.recoverSync N reps = sp.lkAlong cs := by
  unfold sp.recoverSync
  simp only []
  refine ⟨_, ?_, rfl⟩
  refine (sp.fmFst_sublist _ ?_ _).nodup (sp.recOrder_nodup _ _)
  intro c p h
  cases hk : Kept.get _ c with
  | none => rw [hk] at h; cases h
  | some e => rw [hk] at h; cases h; rfl

/-- An entry of `syncSeq M` is an entry of `M` (any `M`). -/
theorem sp.syncSeq_mem (M : sp.SyncMsg) (p : sp.CmdId × sp.Cmd) (h : p ∈ sp.syncSeq M) :
    ∃ D, (p.1, p.2, D) ∈ M := by
  unfold sp.syncSeq at h
  obtain ⟨x, -, hx⟩ := List.mem_filterMap.mp h
  cases hf : M.find? (·.1 == x) with
  | none => rw [hf] at hx; cases hx
  | some q =>
    rw [hf] at hx
    simp only [Option.map_some, Option.some.injEq] at hx
    subst hx
    have hq1 : q.1 = x := by simpa using List.find?_some hf
    refine ⟨q.2.2, ?_⟩
    have hq := List.mem_of_find?_eq_some hf
    rw [← hq1]
    exact hq

/-- **A recovered `MSync` against its sequence** (see the file header). -/
theorem sp.recoverSync_seq (N : Nat) (reps : List (Nat × sp.Report)) :
    (sp.syncSeq (sp.recoverSync N reps)).map Prod.fst = sp.syncOrder (sp.recoverSync N reps) ∧
    ∀ y c D, (y, c, D) ∈ sp.recoverSync N reps →
      (y, c) ∈ sp.syncSeq (sp.recoverSync N reps) ∧
      D.Perm (sp.depsIn (sp.syncSeq (sp.recoverSync N reps)) y) := by
  obtain ⟨cs, hnd, hM⟩ := sp.recoverSync_lk N reps
  rw [hM]
  refine ⟨sp.syncSeq_lkAlong_fst cs hnd, fun y c D hm => ⟨?_, sp.lkAlong_deps_perm cs hnd y c D hm⟩⟩
  apply (sp.syncSeq_lkAlong_mem cs hnd (y, c)).mpr
  rw [← sp.lkAlong_ids cs]
  exact List.mem_map.mpr ⟨_, hm, rfl⟩

/-! ## Ghost -/

section ghost
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable {γ : sp.Names} {γc γm γl : GName}

/-- **A ballot's `MSync` against its sequence** (`sync_ok`, `sp.recoverSync_seq`). -/
theorem sp.syncIs_seq (E : CoPset) (hE : ↑sp.spN ⊆ E) (b : Nat) (M : sp.SyncMsg) :
    sp.inv γ γc γm γl ∗ sp.syncIs γ b M ⊢ |={E}=>
      ⌜(sp.syncSeq M).map Prod.fst = sp.syncOrder M ∧
        ∀ y c D, (y, c, D) ∈ M → (y, c) ∈ sp.syncSeq M ∧ D.Perm (sp.depsIn (sp.syncSeq M) y)⌝ := by
  unfold sp.inv sp.syncIs
  iintro ⟨#Hinv, #HM⟩
  iinv Hinv with Hi Hclose
  unfold sp.invBody
  icases Hi with ⟨%S, %mC, %mL, %mS, %mA, %mP, %mCo, %mR, %mN, %sh, %mD, %mQ, %mK, %mPa, HC, HL, >HS, HA, HP, HCo, HRp, HN, HH, HD, Hown, HQ, HK, HPa, >%Hrepr, Hnodes, Hproto, HQs, HCl, HDom, Hslots, Hconns⟩
  ihave %Hlk := ghost_map_lookup $$ HS HM
  have hS : S.sync b = some M := by rw [← Hrepr.sync]; exact Hlk
  icases Hproto with (>%Hemp | ⟨%N, %fr, %l, #Hcfg, >%HP⟩)
  · exact absurd (Hemp.1.2.1 b ▸ hS) (by simp)
  · obtain ⟨-, -, -, reps, -, -, hM⟩ := HP.1.sync_ok b M hS
    imod Hclose $$ [HC HL HS HA HP HCo HRp HN HH HD Hown HQ HK HPa Hnodes HQs HCl HDom Hslots Hconns Hcfg] with -
    · inext
      iexists S, mC, mL, mS, mA, mP, mCo, mR, mN, sh, mD, mQ, mK, mPa
      iframe
      isplitr
      · ipureintro; exact Hrepr
      iright
      iexists N, fr, l
      isplitr
      · iexact Hcfg
      ipureintro; exact HP
    imodintro
    ipureintro
    subst hM
    exact sp.recoverSync_seq N reps

/-- **The replica's `locLb` of an `MSync`'s sequence** (see the file header). -/
theorem sp.locLb_syncSeq (r b : Nat) (M : sp.SyncMsg)
    (h : (sp.syncSeq M).map Prod.fst = sp.syncOrder M) :
    ([∗list] i ↦ x ∈ sp.syncOrder M, sp.locAt γ r b i x) ∗
      ([∗list] p ∈ M, sp.cmdIs γ p.1 p.2.1) ⊢ sp.locLb γ r b (sp.syncSeq M) := by
  iintro ⟨#Hl, #Hc⟩
  unfold sp.locLb
  iapply (BigSepL.bigSepL_intro (P := iprop(□ (([∗list] i ↦ x ∈ sp.syncOrder M, sp.locAt γ r b i x) ∗
      ([∗list] p ∈ M, sp.cmdIs γ p.1 p.2.1)))))
  · intro i p hp
    have hO : (sp.syncOrder M)[i]? = some p.1 := by
      rw [← h, List.getElem?_map, hp]; rfl
    obtain ⟨D, hD⟩ := sp.syncSeq_mem M p (List.mem_of_getElem? hp)
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hD
    iintro #⟨H1, H2⟩
    isplitr
    · iapply (BigSepL.bigSepL_lookup (Φ := fun i x => sp.locAt γ r b i x) hO); iexact H1
    · iapply (BigSepL.bigSepL_lookup (Φ := fun _ q => sp.cmdIs γ q.1 q.2.1) hj); iexact H2
  imodintro
  iframe Hl Hc

end ghost

end Perennial.github_com.imdea_software.swiftpaxos
