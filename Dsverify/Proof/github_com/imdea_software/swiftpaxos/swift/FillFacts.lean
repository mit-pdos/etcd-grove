/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/FillFacts.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**Phase 4 (round N6, sv-swc): the report's pure facts** (`fillNewLeaderAckN`'s h5-h9 for
`sp.upd_report`, `swift.fillFacts`) and the bounds of `Msg.wf`'s entries (D75 (2)).

* `swift.fillFacts_of` (pure): the facts from the four collections. The entries `E4` are the
  first three collections' (`E4.take n3`: the execution log's `XS`, the stopped descriptors'
  `S`, the base `B` in `COMMIT`) and the pending proposals' in `START` (`E4.drop n3`, with
  `proposeDeps`' `depsIn`, D75 (3)); `coverOk` (N1-R2) and the base's acceptances (`nodeX`)
  give the phases; `localOk` gives `cballot`'s sequence `B ++ handled`, each of whose commands
  is an entry (a `proposes` key, or delivered, hence in `XS`); the sort by rank
  (`swift.fill_order`) gives the order. The report is any permutation `Rs` of `E4` sorted by
  rank (`swift.fill_perm`, `swift.fill_sorted` for `SortFunc`'s post).
* `sp.locLb_depsIn_len` (ghost): `depsIn` of a `locLb`'s sequence is short (`loc_ok`'s
  duplicate-free sequence of registered, small ids).
* `swift.repEntWs_wf` (ghost): the witnessed entries' commands are well formed and, outside
  `START`, their dependencies short (`sp.preacc_depWf`, `sp.locLb_depsIn_len`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.NewLeaderReqs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.FillOrder
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.FastAckLemmas
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Steps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncSeq
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HandleSync
import all Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Inv

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-! ## Pure -/

/-- The comparator's rank of the index `i` (the rank of `ids[i]`, `swift.hrank`). -/
def swift.fillRk (H ids : List swift.CommandId) (i : w64) : Int :=
  match ids[(sint.Z i).toNat]? with
  | some z => (swift.hrank H z : Int)
  | none => 0

/-- The comparator's order on indices: by rank, then by index. -/
def swift.FillLt (H ids : List swift.CommandId) (a b : w64) : Prop :=
  swift.fillRk H ids a < swift.fillRk H ids b ∨
    (swift.fillRk H ids a = swift.fillRk H ids b ∧ sint.Z a < sint.Z b)

/-- The pure facts `sp.upd_report` needs of the entries (h5-h9), at a node state `st` of the
run loop's view `w`, given the descriptor side's coverage (N1-R2) and the base's acceptances
(`swift.nodeX`). -/
def swift.fillFacts (N r b' : Nat) (st : sp.RState) (R : sp.Report) (s : sp.Seq)
    (B : List sp.CmdId) : Prop :=
  (∀ x, (R.cbal, x) ∈ st.accR ∨ (R.cbal, x) ∈ st.comR →
    ∃ e ∈ R.entries, e.id = x ∧ (e.phase.toNat ≥ 2 ∨ (r = sp.leaderOf N R.cbal ∧ e.phase.toNat ≥ 1))) ∧
  (∀ x D, st.preAt R.cbal x = some D → ∃ e ∈ R.entries, e.id = x ∧
    (e.phase.toNat ≥ 2 ∨ (e.phase.toNat = 1 ∧ e.dep = D))) ∧
  (r = sp.leaderOf N R.cbal → ∀ x ∈ st.locAt R.cbal, ∃ e ∈ R.entries, e.id = x) ∧
  (∃ B', B'.Perm B ∧ R.entries.map (·.id) = B' ++ (st.locAt R.cbal).drop B.length) ∧
  (∀ e ∈ R.entries, e.id ∈ st.locAt R.cbal ∧ e.phase.toNat ≤ 3 ∧
    (e.phase.toNat ≥ 2 → (R.cbal, e.id) ∈ st.accR ∨ (R.cbal, e.id) ∈ st.comR) ∧
    (e.phase.toNat = 0 → ∀ d ∈ e.dep, d ∈ sp.depsIn s e.id))

/-- A pending proposal's entry (`fillNewLeaderAckN`'s fourth collection): in `START`, of
`proposes`, its dependencies of `x`'s in the run loop's sequence `s` and short. -/
def swift.startOk (pM : GMap swift.CommandId Loc) (s : sp.Seq) (e : sp.RepEntry) : Prop :=
  e.phase = W64 0 ∧ (pM !! ofCmdId e.id).isSome ∧ (∀ d ∈ e.dep, d ∈ sp.depsIn s e.id) ∧
    e.dep.length < 2 ^ 62

/-- `filterMap` with functions agreeing on the list. -/
theorem swift.filterMap_congr' {α β : Type} (f g : α → Option β) :
    ∀ l : List α, (∀ a ∈ l, f a = g a) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.filterMap_cons, List.filterMap_cons, h a (by simp),
      swift.filterMap_congr' f g l (fun b hb => h b (by simp [hb]))]

/-- The entries along the indices `0, …, n-1`. -/
theorem swift.filterMap_range_take {α : Type} (E : List α) :
    ∀ n, (List.range n).filterMap (fun k => E[k]?) = E.take n
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.filterMap_append, swift.filterMap_range_take E n, List.take_succ]
    cases h : E[n]? <;> simp [h]

/-- `SortFunc`'s indices, a permutation of `0, …, n-1`, give a permutation of the entries. -/
theorem swift.fill_perm {α : Type} (E : List α) (xs : List w64) (hlen : E.length < 2 ^ 62)
    (hp : ((List.range E.length).map (fun (k : Nat) => W64 (k : Int))).Perm xs) :
    (xs.filterMap (fun a => E[(sint.Z a).toNat]?)).Perm E := by
  have h := (hp.filterMap (fun a => E[(sint.Z a).toNat]?)).symm
  refine h.trans ?_
  rw [List.filterMap_map]
  rw [swift.filterMap_congr' _ (fun k => E[k]?) _ (fun k hk => by
    have := List.mem_range.mp hk
    simp only [Function.comp_apply]
    have : sint.Z (W64 (k : Int)) = k := by
      have : (k : Int) < 2 ^ 62 := by omega
      word
    rw [this]; rfl)]
  rw [swift.filterMap_range_take, List.take_length]

/-- `SortFunc`'s post (no later index strictly before an earlier one) on the entries: their
ranks do not decrease. -/
theorem swift.fill_sorted (E : List sp.RepEntry) (H : List swift.CommandId) (xs : List w64)
    (hs : ∀ (i j : Nat) (xi xj : w64), xs[i]? = some xi → xs[j]? = some xj → i < j →
      ¬ swift.FillLt H (E.map (fun e => ofCmdId e.id)) xj xi) :
    (xs.filterMap (fun a => E[(sint.Z a).toNat]?)).Pairwise
      (fun e f => swift.hrank H (ofCmdId e.id) ≤ swift.hrank H (ofCmdId f.id)) := by
  have hpw : xs.Pairwise (fun a b => ¬ swift.FillLt H (E.map (fun e => ofCmdId e.id)) b a) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    exact hs i j _ _ (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hj) hij
  rw [List.pairwise_filterMap]
  refine hpw.imp ?_
  intro a b hab e he f hf
  have hra : swift.fillRk H (E.map (fun e => ofCmdId e.id)) a = swift.hrank H (ofCmdId e.id) := by
    unfold swift.fillRk; rw [List.getElem?_map, he]; rfl
  have hrb : swift.fillRk H (E.map (fun e => ofCmdId e.id)) b = swift.hrank H (ofCmdId f.id) := by
    unfold swift.fillRk; rw [List.getElem?_map, hf]; rfl
  unfold swift.FillLt at hab
  rw [hra, hrb] at hab
  omega

/-- An entry whose id is among a duplicate-free list's prefix's ids is in the prefix. -/
theorem swift.mem_take_of_id (E : List sp.RepEntry) (n : Nat) (hnd : (E.map (·.id)).Nodup)
    (e : sp.RepEntry) (he : e ∈ E) (hid : e.id ∈ (E.take n).map (·.id)) : e ∈ E.take n := by
  rw [← List.take_append_drop n E] at he hnd
  rcases List.mem_append.mp he with h | h
  · exact h
  · exfalso
    rw [List.map_append] at hnd
    exact (List.nodup_append.mp hnd).2.2 _ hid _ (List.mem_map_of_mem h) rfl

/-- **The report's pure facts** (see the file header). -/
theorem swift.fillFacts_of (N r b' c : Nat) (st : sp.RState) (s : sp.Seq) (B : List sp.CmdId)
    (XS S : List sp.RepEntry) (dl : List sp.CmdId) (Pd : List (sp.CmdId × List sp.CmdId))
    (E4 : List sp.RepEntry) (n3 : Nat) (H : List swift.CommandId) (Rs : List sp.RepEntry)
    (hcov : swift.coverOk N r c st s B XS S dl Pd)
    (hbase : ∀ y ∈ B, (c, y) ∈ st.accR)
    (hlocEq : st.locAt c = B ++ H.map toCmdId)
    (hlnd : (st.locAt c).Nodup)
    (hnd : (E4.map (·.id)).Nodup)
    (htake : ∀ e ∈ E4.take n3, e ∈ XS ∨ e ∈ S ∨ (e.phase.toNat = 3 ∧ e.id ∈ B))
    (hdrop : ∀ e ∈ E4.drop n3, e.phase.toNat = 0 ∧ e.id ∈ st.locAt c ∧
      ∀ d ∈ e.dep, d ∈ sp.depsIn s e.id)
    (hcovT : ∀ y, y ∈ (XS ++ S).map (·.id) ∨ y ∈ B → y ∈ (E4.take n3).map (·.id))
    (hloc : ∀ y ∈ st.locAt c, y ∈ E4.map (·.id))
    (hperm : Rs.Perm E4)
    (hsort : Rs.Pairwise (fun e f => swift.hrank H (ofCmdId e.id) ≤ swift.hrank H (ofCmdId f.id))) :
    swift.fillFacts N r b' st ⟨c, Rs⟩ s B := by
  obtain ⟨hc1, hc2, -, -⟩ := hcov
  have hBloc : ∀ y ∈ B, y ∈ st.locAt c := fun y hy => by rw [hlocEq]; exact List.mem_append_left _ hy
  -- an id covered by the first three collections: its (unique) entry is of them
  have hent : ∀ y, y ∈ (XS ++ S).map (·.id) ∨ y ∈ B → ∃ e ∈ E4.take n3, e.id = y := by
    intro y hy
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (hcovT y hy)
    exact ⟨e, he, rfl⟩
  -- every entry's facts (h9)
  have h9 : ∀ e ∈ E4, e.id ∈ st.locAt c ∧ e.phase.toNat ≤ 3 ∧
      (e.phase.toNat ≥ 2 → (c, e.id) ∈ st.accR ∨ (c, e.id) ∈ st.comR) ∧
      (e.phase.toNat = 0 → ∀ d ∈ e.dep, d ∈ sp.depsIn s e.id) := by
    intro e he
    rw [← List.take_append_drop n3 E4] at he
    rcases List.mem_append.mp he with h | h
    · rcases htake e h with hx | hx | ⟨h3, hB⟩
      · obtain ⟨a1, a2, a3, -, -, a6⟩ := hc1 e (List.mem_append_left _ hx)
        exact ⟨a1, a2, a3, a6⟩
      · obtain ⟨a1, a2, a3, -, -, a6⟩ := hc1 e (List.mem_append_right _ hx)
        exact ⟨a1, a2, a3, a6⟩
      · exact ⟨hBloc _ hB, by omega, fun _ => Or.inl (hbase _ hB), fun h0 => by omega⟩
    · obtain ⟨h0, hl, hd⟩ := hdrop e h
      exact ⟨hl, by omega, fun h2 => by omega, fun _ => hd⟩
  -- the phases of a command of the first three collections' entries
  have hph : ∀ e ∈ E4.take n3, (e ∈ XS ++ S) ∨ e.phase.toNat = 3 := by
    intro e he
    rcases htake e he with hx | hx | ⟨h3, -⟩
    · exact Or.inl (List.mem_append_left _ hx)
    · exact Or.inl (List.mem_append_right _ hx)
    · exact Or.inr h3
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- h5
    intro y hy
    obtain ⟨e, he, rfl⟩ := hent y (hc2 _ (by rcases hy with h | h; exact Or.inl h; exact Or.inr (Or.inl h)))
    refine ⟨e, hperm.symm.subset (List.take_subset _ _ he), rfl, ?_⟩
    rcases hph e he with hx | h3
    · exact (hc1 e hx).2.2.2.2.1 hy
    · exact Or.inl (by omega)
  · -- h6
    intro y D hy
    obtain ⟨e, he, rfl⟩ := hent y (hc2 _ (Or.inr (Or.inr (by rw [hy]; rfl))))
    refine ⟨e, hperm.symm.subset (List.take_subset _ _ he), rfl, ?_⟩
    rcases hph e he with hx | h3
    · exact (hc1 e hx).2.2.2.1 D hy
    · exact Or.inl (by omega)
  · -- h7
    intro _ y hy
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (hloc y hy)
    exact ⟨e, hperm.symm.subset he, rfl⟩
  · -- h8: the order (`swift.fill_order` over the Go ids)
    have hndL : (B.map ofCmdId ++ H).Nodup := by
      have h := hlnd.map (S := fun x y => x ≠ y) ofCmdId (fun a b h (heq : ofCmdId a = ofCmdId b) => h (by simpa using congrArg toCmdId heq))
      rw [hlocEq, List.map_append, List.map_map] at h
      have e : H.map (ofCmdId ∘ toCmdId) = H := by
        rw [show (ofCmdId ∘ toCmdId) = id from funext fun _ => rfl, List.map_id]
      rw [e] at h
      exact h
    have hRnd : (Rs.map (fun e => ofCmdId e.id)).Nodup := by
      have h1 : (Rs.map (·.id)).Nodup := (hperm.map (·.id)).nodup_iff.mpr hnd
      have h2 := h1.map (S := fun x y => x ≠ y) ofCmdId (fun a b h (heq : ofCmdId a = ofCmdId b) => h (by simpa using congrArg toCmdId heq))
      rw [List.map_map] at h2
      exact h2
    have hmem : ∀ e ∈ Rs, e ∈ E4 := fun e he => hperm.subset he
    have hpL : (Rs.map (fun e => ofCmdId e.id)).Perm (B.map ofCmdId ++ H) := by
      rw [List.perm_ext_iff_of_nodup hRnd hndL]
      intro z
      constructor
      · intro hz
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hz
        have hl := (h9 e (hmem e he)).1
        rw [hlocEq] at hl
        rcases List.mem_append.mp hl with h | h
        · exact List.mem_append_left _ (List.mem_map_of_mem h)
        · obtain ⟨z', hz', hz''⟩ := List.mem_map.mp h
          refine List.mem_append_right _ ?_
          have : ofCmdId e.id = z' := by rw [← hz'']; rfl
          rw [this]; exact hz'
      · intro hz
        have hl : toCmdId z ∈ st.locAt c := by
          rw [hlocEq]
          rcases List.mem_append.mp hz with h | h
          · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h
            exact List.mem_append_left _ (by simpa using hy)
          · exact List.mem_append_right _ (List.mem_map_of_mem h)
        obtain ⟨e, he, hid⟩ := List.mem_map.mp (hloc _ hl)
        have heR : e ∈ Rs := hperm.symm.subset he
        refine List.mem_map.mpr ⟨e, heR, ?_⟩
        rw [hid]; rfl
    obtain ⟨B'', hB'', hL⟩ := swift.fill_order (B.map ofCmdId) H (Rs.map (fun e => ofCmdId e.id))
      hndL hpL (by rw [List.pairwise_map]; exact hsort)
    refine ⟨B''.map toCmdId, ?_, ?_⟩
    · have := hB''.map toCmdId
      simpa [List.map_map, Function.comp_def] using this
    · show Rs.map (·.id) = B''.map toCmdId ++ (st.locAt c).drop B.length
      rw [hlocEq, List.drop_left]
      have := congrArg (List.map toCmdId) hL
      rw [List.map_map, List.map_append] at this
      simpa [Function.comp_def] using this
  · -- h9
    intro e he
    exact h9 e (hperm.subset he)

end Perennial.github_com.imdea_software.swiftpaxos

/-! ## Ghost: the bounds -/

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace sp
section ghost
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF] [π : NetProtoGS] [GobFmt]
variable {γ : Names} {γc γm γl : GName}

/-- **`depsIn` of a `locLb`'s sequence is short** (round N6, D75 (2)): the sequence is a prefix of
the replica's (`locLb_prefix`), duplicate-free and of registered, small ids (`loc_ok`, the
invariant's client bound). -/
theorem locLb_depsIn_len (r b : Nat) (s : Seq) (y : CmdId) :
    inv γ γc γm γl ∗ locLb γ r b s ⊢ |={↑spN}=> ⌜(depsIn s y).length < 2 ^ 62⌝ := by
  iintro ⟨#Hinv, #Hlb⟩
  unfold inv
  iinv Hinv with Hi Hclose
  unfold invBody
  icases Hi with ⟨%S, %mC, %mL, %mS, %mA, %mP, %mCo, %mR, %mN, %sh, %mD, %mQ, %mK, %mPa, >HC, >HL, HS, HA, HP, HCo, HRp, HN, HH, HD, Hown, HQ, HK, HPa, >%Hrepr, Hnodes, >Hproto, HQs, >%Hcl, >%HDom, Hcmds, Hconns⟩
  ihave ⟨%Hlk, Hx⟩ := BI.persistent_entails_right (locLb_lookups (γ := γ) r b s mL mC)
    $$ [HL HC Hlb]
  · iframe HL HC Hlb
  icases Hx with ⟨HL, HC, -⟩
  icases Hproto with (%He | ⟨%N, %fr, %l, #Hcfg, %Hq⟩)
  · -- the empty state: no `locLb` but `[]`
    imod Hclose $$ [HC HL HS HA HP HCo HRp HN HH HD Hown HQ HK HPa Hnodes HQs Hcmds Hconns] with -
    · inext
      iexists S, mC, mL, mS, mA, mP, mCo, mR, mN, sh, mD, mQ, mK, mPa
      iframe
      isplitr
      · ipureintro; exact Hrepr
      isplitr
      · ileft; ipureintro; exact He
      ipureintro; exact ⟨Hcl, HDom⟩
    imodintro
    ipureintro
    have hs : s = [] := by
      cases s with
      | nil => rfl
      | cons p t =>
        have := (Hlk 0 p rfl).1
        rw [Hrepr.loc, He.1.1 r b] at this
        cases this
    rw [hs]
    have := depsIn_length ([] : Seq) y
    simp only [List.length_nil] at this
    omega
  · imod Hclose $$ [HC HL HS HA HP HCo HRp HN HH HD Hown HQ HK HPa Hnodes HQs Hcmds Hconns] with -
    · inext
      iexists S, mC, mL, mS, mA, mP, mCo, mR, mN, sh, mD, mQ, mK, mPa
      iframe
      isplitr
      · ipureintro; exact Hrepr
      isplitr
      · iright; iexists N, fr, l; iframe Hcfg; ipureintro; exact Hq
      ipureintro; exact ⟨Hcl, HDom⟩
    imodintro
    ipureintro
    obtain ⟨hpre1, -⟩ := locLb_prefix Hq.1 Hrepr Hlk
    obtain ⟨hnd, hreg, -⟩ := Hq.1.loc_ok r b
    have hnd' : (s.map Prod.fst).Nodup := hnd.sublist hpre1.sublist
    have hsm : ∀ z ∈ s.map Prod.fst, swift.idSmall z := fun z hz => by
      have hz' := hpre1.subset hz
      obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp (hreg z hz')
      have hlk : mC.lookup z = some c := by rw [Hrepr.cmds]; exact hc
      obtain ⟨⟨n, hn, -⟩, -⟩ := Hcl z c hlk
      exact HDom.2 z.cl n hn
    have h1 := swift.small_ids_len _ hnd' hsm
    have h2 := depsIn_length s y
    simp only [List.length_map] at h1
    omega

end ghost
end sp

section wf
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions]

/-- **The witnessed entries' bounds** (`Msg.wf`'s, D75 (2)): each entry's command is well formed
(`sp.cmdIs_wf`); outside `START`, its dependencies are short: a pre-acceptance's
(`sp.preacc_depWf`), or `depsIn` of a `locLb`'s sequence up to order (`sp.locLb_depsIn_len`). -/
theorem swift.repEntWs_wf (γ : sp.Names) (γc γm γl : GName) (N r c : Nat) :
    ∀ es : List sp.RepEntry,
    sp.inv γ γc γm γl ∗ ([∗list] e ∈ es, swift.repEntW γ N r c e) ⊢
      |={⊤}=> ⌜∀ e ∈ es, e.cmd.wf ∧ (e.phase.toNat ≠ 0 → e.dep.length < 2 ^ 62)⌝
  | [] => by
    iintro -
    imodintro
    ipureintro
    simp
  | e :: es => by
    iintro ⟨#Hinv, H⟩
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨He, Hs⟩
    imod swift.repEntWs_wf γ γc γm γl N r c es $$ [Hinv Hs] with %hs
    · iframe Hinv Hs
    iunfold swift.repEntW at He
    icases He with ⟨#Hc, Hw⟩
    imod sp.cmdIs_wf (γ := γ) (γc := γc) (γm := γm) (γl := γl) e.id e.cmd $$ [Hinv Hc] with %hwf
    · iframe Hinv Hc
    have fin : (e.phase.toNat ≠ 0 → e.dep.length < 2 ^ 62) →
        ∀ e' ∈ e :: es, e'.cmd.wf ∧ (e'.phase.toNat ≠ 0 → e'.dep.length < 2 ^ 62) := by
      intro hd e' he'
      rcases List.mem_cons.mp he' with rfl | h
      · exact ⟨hwf, hd⟩
      · exact hs e' h
    icases Hw with (%h0 | ⟨%h1, #Hpre⟩ | ⟨%h2, %s', #Hlb, %hs'⟩)
    · imodintro; ipureintro; exact fin (fun h => absurd h0 h)
    · ihave HD := sp.preacc_depWf (γ := γ) (γc := γc) (γm := γm) (γl := γl) r c e.id e.dep
        $$ [Hinv Hpre]
      · iframe Hinv Hpre
      imod (fupd_mask_mono (E1 := ↑sp.spN) (E2 := ⊤) (by simp)) $$ HD with %hD
      imodintro; ipureintro; exact fin (fun _ => hD)
    · ihave HD := sp.locLb_depsIn_len (γ := γ) (γc := γc) (γm := γm) (γl := γl)
        (sp.leaderOf N c) c s' e.id $$ [Hinv Hlb]
      · iframe Hinv Hlb
      imod (fupd_mask_mono (E1 := ↑sp.spN) (E2 := ⊤) (by simp)) $$ HD with %hD
      imodintro; ipureintro; exact fin (fun _ => by rw [hs'.2.length_eq]; exact hD)

end wf

end Perennial.github_com.imdea_software.swiftpaxos

end
