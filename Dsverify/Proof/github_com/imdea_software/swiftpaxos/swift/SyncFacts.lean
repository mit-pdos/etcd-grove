/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/SyncFacts.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
Facts about an `MSync` (the swift group's; not frozen):
* `sp.recoverSync_cmd`: every command `recoverSync` keeps is a reported entry's (pure: rules 1,
  2, the closure's `best`, and 3b/4 keep the commands they set);
* `sp.syncIs_cmdIs`: an `MSync`'s commands are registered (`cmdIs`), from `sp.inv` (`sync_ok`,
  `rep_ok`'s `entryOk`, and the registration facts the invariant keeps with each slot,
  `slotRes`'s `cmdIs`: notes/swift-shared-changes.md, change 1).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Steps
import all Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Inv

@[expose] public section

noncomputable section

set_option linter.unusedSimpArgs false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace sp

/-- Every kept entry's command is some report entry's (of `acks`). -/
def CmdFrom (acks : List (Nat × Report)) (k : Kept) : Prop :=
  ∀ c e, k.get c = some e → ∃ a ∈ acks, ∃ re ∈ a.2.entries, re.id = c ∧ re.cmd = e.cmd

theorem CmdFrom.nil (acks : List (Nat × Report)) : CmdFrom acks [] := by
  intro c e h; simp [Kept.get] at h

theorem CmdFrom.set {acks : List (Nat × Report)} {k : Kept} (H : CmdFrom acks k) {x : CmdId}
    {e : RecEntry} (hx : ∃ a ∈ acks, ∃ re ∈ a.2.entries, re.id = x ∧ re.cmd = e.cmd) :
    CmdFrom acks (k.set x e) := by
  intro c e' h
  rw [Kept.get_set] at h
  by_cases hc : c = x
  · subst hc; simp at h; subst h; exact hx
  · simp [hc] at h; exact H c e' h

/-- An entry's dependencies replaced: the command stays. -/
theorem CmdFrom.setDep {acks : List (Nat × Report)} {k : Kept} (H : CmdFrom acks k) {x : CmdId}
    {e : RecEntry} (hx : k.get x = some e) (D : List CmdId) :
    CmdFrom acks (k.set x { e with dep := D }) :=
  H.set (by obtain ⟨a, ha, re, hre, h1, h2⟩ := H x e hx; exact ⟨a, ha, re, hre, h1, h2⟩)

theorem CmdFrom.mono {acks acks' : List (Nat × Report)} {k : Kept} (H : CmdFrom acks k)
    (h : ∀ a ∈ acks, a ∈ acks') : CmdFrom acks' k := by
  intro c e hc
  obtain ⟨a, ha, re, hre, h1, h2⟩ := H c e hc
  exact ⟨a, h a ha, re, hre, h1, h2⟩

theorem foldl_inv {α β : Type} (P : β → Prop) (f : β → α → β) (l : List α)
    (hf : ∀ b a, a ∈ l → P b → P (f b a)) : ∀ b, P b → P (l.foldl f b) := by
  induction l with
  | nil => intro b h; exact h
  | cons a l ih =>
    intro b h
    exact ih (fun b' a' ha' => hf b' a' (List.mem_cons_of_mem a ha')) _
      (hf b a List.mem_cons_self h)

theorem rule1_cmd (acks : List (Nat × Report)) (oldL : Nat) (U : List (Nat × Report))
    (hU : ∀ a ∈ U, a ∈ acks) : CmdFrom acks (rule1 oldL U) := by
  unfold rule1
  refine foldl_inv _ _ _ (fun k a ha H => ?_) _ (CmdFrom.nil _)
  refine foldl_inv _ _ _ (fun k e he H => ?_) _ H
  have hx : ∀ ph dp cl, ∃ a' ∈ acks, ∃ re ∈ a'.2.entries, re.id = e.id ∧
      re.cmd = (⟨ph, e.cmd, dp, cl⟩ : RecEntry).cmd := fun _ _ _ => ⟨a, hU a ha, e, he, rfl, rfl⟩
  split
  · exact H
  · split
    · split
      · exact H.set (hx _ _ _)
      · exact H
    · exact H.set (hx _ _ _)

theorem rule2_cmd (acks : List (Nat × Report)) (k1 : Kept) (leaderInU : Bool)
    (R : List (Nat × Report)) (hR : ∀ a ∈ R, a ∈ acks) (H : CmdFrom acks k1) :
    CmdFrom acks (rule2 k1 leaderInU R) := by
  unfold rule2
  split
  · exact H
  · split
    · exact H
    · rename_i _ r0 rs
      have ha := hR r0 List.mem_cons_self
      refine foldl_inv _ _ _ (fun k e he H => ?_) _ H
      split
      · exact H
      · split
        · exact H.set ⟨r0, ha, e, he, rfl, rfl⟩
        · exact H

/-- A `best` candidate's command is a report entry's (of `S`). -/
def PickOk (S : List (Nat × Report)) (d : CmdId) (b : Option RecEntry) : Prop :=
  ∀ b0, b = some b0 → ∃ a ∈ S, ∃ re ∈ a.2.entries, re.id = d ∧ re.cmd = b0.cmd

theorem pickEntries_ok (S : List (Nat × Report)) (d : CmdId) (a : Nat × Report) (ha : a ∈ S)
    (c0 : Option RecEntry) (H : PickOk S d c0) :
    PickOk S d (a.2.entries.foldl (fun b e => if e.id != d then b else match b with
        | none => some ⟨e.phase.toNat, e.cmd, e.dep, 2⟩
        | some b0 => if e.phase.toNat > b0.phase then some ⟨e.phase.toNat, e.cmd, e.dep, 2⟩
            else some b0) c0) := by
  refine foldl_inv _ _ _ (fun c e he H => ?_) _ H
  split
  · exact H
  · rename_i hid
    have hid : e.id = d := by simpa using hid
    have hnew : PickOk S d (some ⟨e.phase.toNat, e.cmd, e.dep, 2⟩) := by
      intro b0 hb; cases hb; exact ⟨a, ha, e, he, hid, rfl⟩
    split
    · exact hnew
    · split
      · exact hnew
      · exact H

theorem recPickFrom_ok (S : List (Nat × Report)) (d : CmdId) :
    ∀ (l : List (Nat × Report)) (b0 : Option RecEntry), (∀ a ∈ l, a ∈ S) → PickOk S d b0 →
      PickOk S d (recPickFrom l d b0) := by
  intro l
  induction l with
  | nil => intro b0 _ H; exact H
  | cons a l ih =>
    intro b0 hl H
    rw [recPickFrom_cons]
    exact ih _ (fun b hb => hl b (List.mem_cons_of_mem a hb))
      (pickEntries_ok S d a (hl a List.mem_cons_self) _ H)

theorem recBest_ok (acks : List (Nat × Report)) (leaderInU : Bool) (R U : List (Nat × Report))
    (hR : ∀ a ∈ R, a ∈ acks) (hU : ∀ a ∈ U, a ∈ acks) (d : CmdId) :
    PickOk acks d (recBest leaderInU R U acks d) := by
  have hnone : PickOk acks d none := by intro b h; cases h
  unfold recBest
  split
  · rename_i e he
    intro b0 hb; cases hb
    split at he
    · cases he
    · split at he
      · cases he
      · rename_i r0 rs
        have hm := List.mem_of_find?_eq_some he
        have hid := List.find?_some he
        exact ⟨r0, hR r0 List.mem_cons_self, e, hm, by simpa using hid, rfl⟩
  · split
    · rename_i b hb
      exact fun b0 h => (recPickFrom_ok acks d U none hU hnone) b0 (by rw [← recPick_eq, hb, h])
    · exact recPickFrom_ok acks d acks none (fun a h => h) hnone

theorem closeStep_cmd {acks : List (Nat × Report)} {best : CmdId → Option RecEntry}
    (hb : ∀ d, PickOk acks d (best d)) (st : Kept × List CmdId) (H : CmdFrom acks st.1) :
    CmdFrom acks (closeStep best st).1 := by
  unfold closeStep
  split
  · exact H
  · rename_i c work _
    split
    · exact H
    · rename_i e he
      -- the dependencies' fold keeps the property
      have hfold : ∀ (ds : List CmdId) (acc : Kept × List CmdId × List CmdId),
          CmdFrom acks acc.1 → acc.1.get c = some e →
          CmdFrom acks (ds.foldl (closeDep best c) acc).1 ∧
            (ds.foldl (closeDep best c) acc).1.get c = some e := by
        intro ds
        induction ds with
        | nil => intro acc h1 h2; exact ⟨h1, h2⟩
        | cons d ds ih =>
          intro acc h1 h2
          simp only [List.foldl_cons]
          apply ih
          · unfold closeDep
            split
            · exact h1
            · split
              · exact h1
              · split
                · exact h1
                · rename_i _ bd hbd
                  exact h1.set (hb d bd hbd)
          · unfold closeDep
            split
            · exact h2
            · split
              · exact h2
              · split
                · exact h2
                · rename_i hdc _ _ _ _
                  simp only [beq_iff_eq] at hdc
                  show (acc.1.set d _).get c = some e
                  rw [Kept.get_set, if_neg (Ne.symm hdc)]; exact h2
      obtain ⟨h1, h2⟩ := hfold e.dep (st.1, work, []) H he
      exact h1.setDep h2 _

theorem iter_closeStep_cmd {acks : List (Nat × Report)} {best : CmdId → Option RecEntry}
    (hb : ∀ d, PickOk acks d (best d)) (n : Nat) :
    ∀ st : Kept × List CmdId, CmdFrom acks st.1 → CmdFrom acks (iter (closeStep best) n st).1 := by
  induction n with
  | zero => intro st H; exact H
  | succ n ih => intro st H; exact ih _ (closeStep_cmd hb st H)

theorem rule3b_cmd (acks : List (Nat × Report)) (leaderInU : Bool) (R : List (Nat × Report))
    (k3 : Kept) (H : CmdFrom acks k3) : CmdFrom acks (rule3b leaderInU R k3) := by
  unfold rule3b
  split
  · exact H
  · split
    · exact H
    · refine foldl_inv _ _ _ (fun k c _ H => ?_) _ H
      unfold rule3bCmd
      split
      · split
        · exact H
        · refine foldl_inv _ _ _ (fun k w _ H => ?_) _ H
          unfold rule3bPair
          split
          · rename_i hc _
            split
            · exact H
            · split
              · exact H
              · exact H.setDep hc _
          · exact H
      · exact H

theorem rule4_cmd (acks : List (Nat × Report)) (ids : List CmdId) (k3 : Kept)
    (H : CmdFrom acks k3) : CmdFrom acks (rule4 ids k3) := by
  unfold rule4
  refine foldl_inv _ _ _ (fun k c _ H => ?_) _ H
  unfold rule4Cmd
  split
  · exact H
  · split
    · exact H
    · refine foldl_inv _ _ _ (fun k w _ H => ?_) _ H
      unfold rule4Pair
      split
      · rename_i hc
        split
        · exact H
        · split
          · exact H.setDep hc _
          · exact H
      · exact H

/-- **Every command of `recoverSync N reps` is a reported entry's.** -/
theorem recoverSync_cmd (N : Nat) (reps : List (Nat × Report)) (p : CmdId × Cmd × List CmdId)
    (hp : p ∈ recoverSync N reps) :
    ∃ a ∈ reps, ∃ re ∈ a.2.entries, re.id = p.1 ∧ re.cmd = p.2.1 := by
  have hacks : ∀ a ∈ recAcks reps, a ∈ reps := fun a ha => by
    unfold recAcks at ha; exact (List.mergeSort_perm _ _).mem_iff.mp ha
  have hU : ∀ a ∈ recU (recAcks reps), a ∈ recAcks reps := fun a ha => by
    unfold recU at ha; exact (List.mem_filter.mp ha).1
  unfold recoverSync at hp
  simp only at hp
  generalize hk1 : rule1 _ _ = k1 at hp
  have H1 : CmdFrom (recAcks reps) k1 := hk1 ▸ rule1_cmd _ _ _ hU
  have hR : ∀ a ∈ (recU (recAcks reps)).filter
      (fun a => decide (a.1 ∈ AQ N (recMaxC (recAcks reps)))), a ∈ recAcks reps :=
    fun a ha => hU a (List.mem_filter.mp ha).1
  generalize hk2 : rule2 k1 _ _ = k2 at hp
  have H2 : CmdFrom (recAcks reps) k2 := hk2 ▸ rule2_cmd _ _ _ _ hR H1
  generalize hk3 : closure _ _ k2 = k3 at hp
  have H3 : CmdFrom (recAcks reps) k3 := by
    rw [← hk3]; unfold closure
    exact iter_closeStep_cmd (recBest_ok _ _ _ _ hR hU) _ _ H2
  generalize hk3b : rule3b _ _ k3 = k3b at hp
  have H3b : CmdFrom (recAcks reps) k3b := hk3b ▸ rule3b_cmd _ _ _ _ H3
  generalize hk4 : rule4 _ k3b = k4 at hp
  have H4 : CmdFrom (recAcks reps) k4 := hk4 ▸ rule4_cmd _ _ _ H3b
  have hmem : (p.1, p.2.1) ∈ (lkAlong (List.filterMap (fun c => (k4.get c).map (fun e => (c, e.cmd)))
      (recOrder k4 (sortIds (k3b.map Prod.fst))))).map (fun p => (p.1, p.2.1)) :=
    List.mem_map.mpr ⟨p, hp, rfl⟩
  rw [lkAlong_ids, List.mem_filterMap] at hmem
  obtain ⟨c, -, hc⟩ := hmem
  cases he : k4.get c with
  | none => rw [he] at hc; cases hc
  | some e =>
    rw [he] at hc; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, hcmd⟩ := hc
    obtain ⟨a, ha, re, hre, h1, h2⟩ := H4 _ e he
    exact ⟨a, hacks a ha, re, hre, h1, by rw [h2, hcmd]⟩

/-- An `MSync`'s commands are registered in the protocol state (`S.cmds`), from `sync_ok` and
the reports' truthfulness (`rep_ok`, `entryOk`). -/
theorem sync_cmds {S : PState} {N : Nat} {fr : Bool} (HI : S.PInv N fr) {b : Nat} {M : SyncMsg}
    (hM : S.sync b = some M) : ∀ p ∈ M, S.cmds p.1 = some p.2.1 := by
  intro p hp
  obtain ⟨-, -, -, reps, -, hreps, rfl⟩ := HI.sync_ok b M hM
  obtain ⟨a, ha, re, hre, h1, h2⟩ := recoverSync_cmd N reps p hp
  have hok := (HI.rep_ok a.1 b a.2 (hreps a ha)).2.2.2.2.2.2.2.2 re hre
  rw [← h1, ← h2]; exact hok.1

end sp

namespace sp

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

section ghost
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF] [π : NetProtoGS] [Perennial.github_com.imdea_software.swiftpaxos.sp.GobFmt]
variable {γ : Names} {γc γm γl : GName}

instance cmdIs_timeless (x : CmdId) (c : Cmd) : Timeless (cmdIs γ x c) := by
  unfold cmdIs; infer_instance

/-- The invariant keeps each registered command's `cmdIs` (D11; change log C12: directly). -/
theorem slots_cmdIs (mC : GMap CmdId Cmd) :
    ([∗map] x ↦ c ∈ mC, cmdIs γ x c) ⊢
      ([∗map] x ↦ c ∈ mC, cmdIs γ x c) ∗ □ ([∗map] x ↦ c ∈ mC, cmdIs γ x c) := by
  iintro #H1
  isplitl
  · iexact H1
  · imodintro; iexact H1

/-- A persistent family of `cmdIs` over the registration map gives each listed entry's. -/
theorem cmdIs_list (mC : GMap CmdId Cmd) (M : SyncMsg)
    (hc : ∀ p ∈ M, mC.lookup p.1 = some p.2.1) :
    (□ [∗map] x ↦ c ∈ mC, cmdIs γ x c) ⊢ □ [∗list] p ∈ M, cmdIs γ p.1 p.2.1 := by
  iintro #H
  imodintro
  iapply (BigSepL.bigSepL_intro (P := iprop(□ [∗map] x ↦ c ∈ mC, cmdIs γ x c))
    (fun i p hp => intuitionistically_elim.trans
    (BigSepM.bigSepM_lookup (show Iris.Std.PartialMap.get? mC p.1 = some p.2.1 from
      hc p (List.mem_of_getElem? hp)))))
  iexact H

/-- **An `MSync`'s commands are registered** (`cmdIs` of each entry): the model facts
(`sync_cmds`: `S.cmds` has each entry, so the `cmds` authority has it) and the fragments the
invariant keeps with each slot (`slotRes`, D11). -/
theorem syncIs_cmdIs (E : CoPset) (hE : ↑spN ⊆ E) (b : Nat) (M : SyncMsg) :
    inv γ γc γm γl ∗ syncIs γ b M ⊢ |={E}=> [∗list] p ∈ M, cmdIs γ p.1 p.2.1 := by
  unfold inv syncIs
  iintro ⟨#Hinv, #HM⟩
  iinv Hinv with Hi Hclose
  unfold invBody
  icases Hi with ⟨%S, %mC, %mL, %mS, %mA, %mP, %mCo, %mR, %mN, %sh, %mD, %mQ, %mK, %mPa, >HC, HL, >HS, HA, HP, HCo, HRp, HN, HH, HD, Hown, HQ, HK, HPa, >%Hrepr, Hnodes, Hproto, HQs, HCl, HDom, Hslots, Hconns⟩
  ihave %Hlk := ghost_map_lookup $$ HS HM
  have hS : S.sync b = some M := by rw [← Hrepr.sync]; exact Hlk
  icases Hproto with (>%Hemp | ⟨%N, %fr, %l, #Hcfg, >%HP⟩)
  · exact absurd (Hemp.1.2.1 b ▸ hS) (by simp)
  · have hc : ∀ p ∈ M, mC.lookup p.1 = some p.2.1 := fun p hp => by
      rw [Hrepr.cmds]; exact sync_cmds HP.1 hS p hp
    ihave Hx := later_mono (slots_cmdIs (γ := γ) mC) $$ Hslots
    icases Hx with ⟨Hslots, Hcm⟩
    ihave Hlist := later_mono (cmdIs_list mC M hc) $$ Hcm
    icases Hlist with >#Hlist
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
    iexact Hlist

end ghost

end sp

end Perennial.github_com.imdea_software.swiftpaxos
