/-
The definitions, specs and lemmas of `RecKept.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

theorem swift.toCmdId_inj {a b : swift.CommandId} (h : toCmdId a = toCmdId b) : a = b := by
  rw [← ofCmdId_toCmdId a, h, ofCmdId_toCmdId]

/-- `o` with `x`'s flag `b`. -/
def swift.updO (o : sp.CmdId → Bool) (x : sp.CmdId) (b : Bool) : sp.CmdId → Bool :=
  fun y => if y = x then b else o y

theorem swift.updO_const (b : Bool) (x : sp.CmdId) :
    swift.updO (fun _ => b) x b = fun _ => b := by
  funext y; unfold swift.updO; split <;> rfl

/-- The pure part of `keptOwn`. -/
def swift.keptPure (k : sp.Kept) (mk : GMap swift.CommandId Loc) : Prop :=
  (k.map Prod.fst).Nodup ∧ ∀ c, (mk !! c).isSome = (k.get (toCmdId c)).isSome

theorem swift.keptPure_insert {k : sp.Kept} {mk : GMap swift.CommandId Loc} (H : swift.keptPure k mk)
    (x : swift.CommandId) (p : Loc) (e : sp.RecEntry) :
    swift.keptPure (k.set (toCmdId x) e) (<[x := p]> mk) := by
  refine ⟨sp.Kept.keys_set_nodup k _ e H.1, fun c => ?_⟩
  rw [sp.Kept.get_set]
  by_cases h : c = x
  · subst h; simp
  · have : toCmdId c ≠ toCmdId x := fun h' => h (swift.toCmdId_inj h')
    rw [GMap.lookup_insert_ne _ _ (Ne.symm h), if_neg this]; exact H.2 c

/-- `sortedIds`' result against the kept list's keys. -/
theorem swift.keys_perm (k : sp.Kept) (ids : List swift.CommandId) (hnd : ids.Nodup)
    (hk : (k.map Prod.fst).Nodup) (hmem : ∀ c, c ∈ ids ↔ (k.get (toCmdId c)).isSome) :
    (k.map Prod.fst).Perm (ids.map toCmdId) := by
  have hnd' : (ids.map toCmdId).Nodup := by
    clear hmem
    induction ids with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd ⊢
      refine ⟨?_, ih hnd.2⟩
      rintro ⟨b, hb, hba⟩
      have : b = a := by simpa using congrArg ofCmdId hba
      exact hnd.1 (this ▸ hb)
  rw [List.perm_ext_iff_of_nodup hk hnd']
  intro x
  rw [← sp.Kept.get_isSome_iff]
  constructor
  · intro h
    exact List.mem_map.mpr ⟨ofCmdId x, (hmem _).mpr (by simpa using h), by simp⟩
  · intro h
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h
    exact (hmem c).mp hc

theorem swift.nodup_map_ofCmdId {l : List sp.CmdId} (h : l.Nodup) : (l.map ofCmdId).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h ⊢
    refine ⟨?_, ih h.2⟩
    rintro ⟨b, hb, hba⟩
    have : b = a := by simpa using congrArg toCmdId hba
    exact h.1 (this ▸ hb)

theorem swift.keptPure_size {k : sp.Kept} {mk : GMap swift.CommandId Loc} (H : swift.keptPure k mk) :
    GMap.size mk = k.length := by
  have hnd : (k.map (fun p => ofCmdId p.1)).Nodup := by
    rw [show k.map (fun p => ofCmdId p.1) = (k.map Prod.fst).map ofCmdId by simp]
    exact swift.nodup_map_ofCmdId H.1
  rw [GMap.size_eq_length mk _ hnd, List.length_map]
  intro c
  rw [H.2 c, sp.Kept.get_isSome_iff]
  constructor
  · intro h; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h; simpa using List.mem_map_of_mem (f := Prod.fst) hp
  · intro h; obtain ⟨p, hp, hpc⟩ := List.mem_map.mp h
    exact List.mem_map.mpr ⟨p, hp, by rw [hpc]; simp⟩

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]

/-- The entries of `kept` (`keptOwn`'s map part). -/
abbrev swift.keptEnts (k : sp.Kept) (o : sp.CmdId → Bool) (mk : GMap swift.CommandId Loc) :
    IProp netDistGF :=
  iprop([∗map] c ↦ p ∈ mk, ∃ e, ⌜k.get (toCmdId c) = some e⌝ ∗ swift.recOwn p e (o (toCmdId c)))

/-- **An entry set** (inserted or replaced): `kept` is the model's `Kept.set`, with the new
entry's ownership flag. The old entry (if any) was taken out (`delete`). -/
theorem swift.kept_set (m : Loc) (k : sp.Kept) (o : sp.CmdId → Bool) (mk : GMap swift.CommandId Loc)
    (x : swift.CommandId) (p : Loc) (e : sp.RecEntry) (b : Bool) (H : swift.keptPure k mk) :
    m ↦$ (<[x := p]> mk) ∗ swift.keptEnts k o (GMap.delete x mk) ∗ swift.recOwn p e b ⊢
      swift.keptOwn m (k.set (toCmdId x) e) (swift.updO o (toCmdId x) b) := by
  iintro ⟨Hm, Hents, Hp⟩
  iunfold swift.keptOwn
  iexists _
  iframe Hm
  isplitr
  · ipureintro; exact swift.keptPure_insert H x p e
  iapply (BigSepM.bigSepM_insert_delete
    (Φ := fun c q => iprop(∃ e', ⌜(k.set (toCmdId x) e).get (toCmdId c) = some e'⌝ ∗
      swift.recOwn q e' (swift.updO o (toCmdId x) b (toCmdId c))))
    (m := mk) (i := x) (x := p)).2
  isplitl [Hp]
  · iexists e
    isplitr
    · ipureintro; rw [sp.Kept.get_set]; simp
    · unfold swift.updO; simp only [↓reduceIte]; iexact Hp
  · iapply (BigSepM.bigSepM_mono (m := GMap.delete x mk) ?_) $$ Hents
    intro c q hcq
    have hc : c ≠ x := by
      intro h; subst h
      simp [Iris.Std.PartialMap.get?] at hcq
    have hc' : toCmdId c ≠ toCmdId x := fun h' => hc (swift.toCmdId_inj h')
    iintro ⟨%e', %he', Hq⟩
    iexists e'
    isplitr
    · ipureintro; rw [sp.Kept.get_set, if_neg hc']; exact he'
    · unfold swift.updO; rw [if_neg hc']; iexact Hq

/-- **An entry replaced in place** (the same pointer, e.g. its dependencies appended): the
entries of `kept` are those of the model's `Kept.set`. -/
theorem swift.keptEnts_upd (k : sp.Kept) (o : sp.CmdId → Bool) (mk : GMap swift.CommandId Loc)
    (x : swift.CommandId) (p : Loc) (e : sp.RecEntry) (hx : mk !! x = some p) :
    swift.keptEnts k o (GMap.delete x mk) ∗ swift.recOwn p e (o (toCmdId x)) ⊢
      swift.keptEnts (k.set (toCmdId x) e) o mk := by
  refine (?_ : _ ⊢ swift.keptEnts (k.set (toCmdId x) e) o (<[x := p]> mk)).trans
    (by rw [GMap.insert_id _ _ _ hx])
  iintro ⟨Hents, Hp⟩
  iapply (BigSepM.bigSepM_insert_delete
    (Φ := fun c q => iprop(∃ e', ⌜(k.set (toCmdId x) e).get (toCmdId c) = some e'⌝ ∗
      swift.recOwn q e' (o (toCmdId c))))
    (m := mk) (i := x) (x := p)).2
  isplitl [Hp]
  · iexists e
    isplitr
    · ipureintro; rw [sp.Kept.get_set]; simp
    · iexact Hp
  · iapply (BigSepM.bigSepM_mono (m := GMap.delete x mk) ?_) $$ Hents
    intro c q hcq
    have hc : c ≠ x := by
      intro h; subst h
      simp [Iris.Std.PartialMap.get?] at hcq
    have hc' : toCmdId c ≠ toCmdId x := fun h' => hc (swift.toCmdId_inj h')
    iintro ⟨%e', %he', Hq⟩
    iexists e'
    isplitr
    · ipureintro; rw [sp.Kept.get_set, if_neg hc']; exact he'
    · iexact Hq

theorem swift.keptPure_upd {k : sp.Kept} {mk : GMap swift.CommandId Loc} (H : swift.keptPure k mk)
    (x : swift.CommandId) (p : Loc) (e : sp.RecEntry) (hx : mk !! x = some p) :
    swift.keptPure (k.set (toCmdId x) e) mk := by
  have := swift.keptPure_insert H x p e
  rwa [GMap.insert_id _ _ _ hx] at this

/-- A new entry (not yet in `kept`). -/
theorem swift.kept_insert (m : Loc) (k : sp.Kept) (o : sp.CmdId → Bool) (mk : GMap swift.CommandId Loc)
    (x : swift.CommandId) (p : Loc) (e : sp.RecEntry) (b : Bool) (H : swift.keptPure k mk)
    (hx : mk !! x = none) :
    m ↦$ (<[x := p]> mk) ∗ swift.keptEnts k o mk ∗ swift.recOwn p e b ⊢
      swift.keptOwn m (k.set (toCmdId x) e) (swift.updO o (toCmdId x) b) := by
  rw [← GMap.delete_notin mk x hx]
  iintro ⟨Hm, Hents, Hp⟩
  rw [GMap.delete_notin mk x hx]
  iapply swift.kept_set m k o mk x p e b H
  rw [GMap.delete_notin mk x hx]
  iframe

/-- `best`'s result: `nil` (no entry) or a new entry (read-only dependencies). -/
def swift.optOwn (p : Loc) (ob : Option sp.RecEntry) : IProp netDistGF :=
  match ob with
  | none => iprop(⌜p = null⌝)
  | some e => swift.recOwn p e false

/-- A new entry added to `kept`'s entries (a key not in the map). -/
theorem swift.keptEnts_insert (k : sp.Kept) (o : sp.CmdId → Bool) (m : GMap swift.CommandId Loc)
    (x : swift.CommandId) (p : Loc) (e : sp.RecEntry) (b : Bool) (hx : m !! x = none) :
    swift.keptEnts k o m ∗ swift.recOwn p e b ⊢
      swift.keptEnts (k.set (toCmdId x) e) (swift.updO o (toCmdId x) b) (<[x := p]> m) := by
  iintro ⟨Hents, Hp⟩
  iapply (BigSepM.bigSepM_insert
    (Φ := fun c q => iprop(∃ e', ⌜(k.set (toCmdId x) e).get (toCmdId c) = some e'⌝ ∗
      swift.recOwn q e' (swift.updO o (toCmdId x) b (toCmdId c))))
    (show Iris.Std.PartialMap.get? m x = none from hx)).2
  isplitl [Hp]
  · iexists e
    isplitr
    · ipureintro; rw [sp.Kept.get_set]; simp
    · unfold swift.updO; simp only [↓reduceIte]; iexact Hp
  · iapply (BigSepM.bigSepM_mono (m := m) ?_) $$ Hents
    intro c q hcq
    have hc : c ≠ x := by
      intro h; subst h
      simp [Iris.Std.PartialMap.get?] at hcq; rw [hx] at hcq; cases hcq
    have hc' : toCmdId c ≠ toCmdId x := fun h' => hc (swift.toCmdId_inj h')
    iintro ⟨%e', %he', Hq⟩
    iexists e'
    isplitr
    · ipureintro; rw [sp.Kept.get_set, if_neg hc']; exact he'
    · unfold swift.updO; rw [if_neg hc']; iexact Hq

/-- The ownership flags matter only on the kept commands. -/
theorem swift.kept_o_congr (m : Loc) (k : sp.Kept) (o o' : sp.CmdId → Bool)
    (h : ∀ y, (k.get y).isSome → o y = o' y) :
    swift.keptOwn m k o ⊢ swift.keptOwn m k o' := by
  unfold swift.keptOwn
  iintro Hk
  icases Hk with ⟨%mk, Hm, %Hmk, Hents⟩
  iexists mk
  iframe Hm
  isplitr
  · ipureintro; exact Hmk
  iapply (BigSepM.bigSepM_mono (m := mk) ?_) $$ Hents
  intro c q _
  iintro ⟨%e, %he, Hq⟩
  iexists e
  isplitr
  · ipureintro; exact he
  · rw [← h (toCmdId c) (by rw [he]; rfl)]; iexact Hq

theorem swift.kept_close (m : Loc) (k : sp.Kept) (o : sp.CmdId → Bool)
    (mk : GMap swift.CommandId Loc) (H : swift.keptPure k mk) :
    m ↦$ mk ∗ swift.keptEnts k o mk ⊢ swift.keptOwn m k o := by
  iintro ⟨Hm, Hents⟩
  iunfold swift.keptOwn
  iexists mk
  iframe Hm
  isplitr
  · ipureintro; exact H
  · iexact Hents

theorem swift.kept_empty (m : Loc) (o : sp.CmdId → Bool) :
    m ↦$ (∅ : GMap swift.CommandId Loc) ⊢ swift.keptOwn m [] o := by
  iintro Hm
  iunfold swift.keptOwn
  iexists ∅
  iframe Hm
  isplitr
  · ipureintro; refine ⟨List.nodup_nil, fun c => ?_⟩; simp [sp.Kept.get]
  · iapply (BigSepM.bigSepM_eqv_empty (Φ := fun c p => iprop(∃ e, ⌜sp.Kept.get [] (toCmdId c) = some e⌝ ∗
      swift.recOwn p e (o (toCmdId c)))) rfl).2
    iempintro

end lemmas

section sorted
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [swift.Assumptions] [slices.Assumptions]

/-- `sortedIds.specI` with the result's capacity (the closure appends to its work list). -/
abbrev swift.sortedIds.specC : Prop :=
  ∀ (m : Loc) (mk : GMap swift.CommandId Loc) (dq : DFrac),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      m ↦${dq} mk ∗ ⌜GMap.size mk ≤ 2 ^ 62⌝ }}
    (App (Val (@! swift.sortedIds)) (Val #m))
  {{ (sl : GoSlice) (ids : List swift.CommandId), RET #sl; m ↦${dq} mk ∗ sl ↦* ids ∗
      ownSliceCap swift.CommandId sl (DFrac.own 1) ∗
      ⌜ids.Nodup ∧ (∀ k, k ∈ ids ↔ (mk !! k).isSome) ∧
        ∀ L : List sp.CmdId, List.Perm L (ids.map swift.toCmdId) →
          sp.sortIds L = ids.map swift.toCmdId⌝ }}

end sorted

end Perennial.github_com.imdea_software.swiftpaxos
