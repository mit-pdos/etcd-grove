/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/HandleSync.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`r.handleSync(msg)` (recovery.go): the run loop takes ballot `b'`'s `MSync` `M` (internal spec;
the swift group's, not frozen). Its parts:

* pure: the `MSync`'s sequence `syncSeq M` has the ids `syncOrder M` (`swift.syncSeq_fst`); the
  keys' `lightKeyInfo`s along a sequence grow by one command at a time (`swift.lkOf_snoc`);
* `swift.localOkS`/`swift.runStS`: the run loop's state as `handleSync` may find it: `runSt`'s,
  but the new leader already holds its row of `b'` (`upd_computeSync`, from
  `handleNewLeaderAckNs`), so `localOk`'s "no row above `cballot`" excludes `b'`
  (`swift.runSt_runStS`: every `runSt` is one);
* `swift.sync_runSt`: **the ghost composition** after `swift.takeSync_step`: the new view (ballot
  and `cballot` `b'`, normal, the sequence of `b'` the order), the order's `locAt`s with the
  commands' `cmdIs`, the fields reset (`handled` empty, the hash logs and pending updates empty,
  `keys` along `syncSeq M`, `lastSync` the `MSync`, every command of the order in `proposes`) give
  `runSt` at `b'` with base `syncSeq M`;
* the spec `swift.Replica.handleSync.specI` (the epoch's resources, which the descriptor and
  reply-channel machinery will define, are a parameter `Ep`; the callees' specs are
  Proof/swift/SyncSpecs.lean's).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncStep
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncFacts

@[expose] public section

noncomputable section

set_option linter.unusedSimpArgs false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-! ## Pure -/

namespace sp

theorem syncOrder_mem (M : SyncMsg) (x : CmdId) (h : x ∈ syncOrder M) : x ∈ M.map Prod.fst := by
  have := recOrder_sub _ _ x h
  unfold sortIds at this
  exact List.mem_mergeSort.mp this

/-- `x`'s command in an `MSync`. -/
def syncCmd (M : SyncMsg) (x : CmdId) : Cmd := ((M.find? (·.1 == x)).map (·.2.1)).getD default

theorem mem_eq_of_fst {α β : Type} {M : List (α × β)} (hnd : (M.map Prod.fst).Nodup)
    {p q : α × β} (hp : p ∈ M) (hq : q ∈ M) (h : p.1 = q.1) : p = q := by
  induction M with
  | nil => cases hp
  | cons a M ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hp with rfl | hp' <;> rcases List.mem_cons.mp hq with rfl | hq'
    · rfl
    · exact absurd (by rw [h]; exact List.mem_map_of_mem hq') hnd.1
    · exact absurd (by rw [← h]; exact List.mem_map_of_mem hp') hnd.1
    · exact ih hnd.2 hp' hq'

theorem syncCmd_of_mem {M : SyncMsg} (hnd : (M.map Prod.fst).Nodup) {p : CmdId × Cmd × List CmdId}
    (hp : p ∈ M) : syncCmd M p.1 = p.2.1 := by
  unfold syncCmd
  obtain ⟨q, hq⟩ : ∃ q, M.find? (·.1 == p.1) = some q :=
    Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨p, hp, by simp⟩)
  have hqm := List.mem_of_find?_eq_some hq
  have hqid : q.1 = p.1 := by simpa using List.find?_some hq
  rw [hq, mem_eq_of_fst hnd hqm hp hqid]; rfl

theorem filterMap_eq_map_of {α β : Type} (f : α → Option β) (g : α → β) (l : List α)
    (h : ∀ x ∈ l, f x = some (g x)) : l.filterMap f = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.filterMap_cons, h a List.mem_cons_self, List.map_cons,
      ih (fun x hx => h x (List.mem_cons_of_mem a hx))]

/-- `syncSeq M`: the order with each command's. -/
theorem syncSeq_eq (M : SyncMsg) : syncSeq M = (syncOrder M).map (fun x => (x, syncCmd M x)) := by
  unfold syncSeq
  apply filterMap_eq_map_of
  intro x hx
  have hm := syncOrder_mem M x hx
  obtain ⟨q, hq⟩ : ∃ q, M.find? (·.1 == x) = some q := by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
    exact Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨p, hp, by simp⟩)
  simp [syncCmd, hq]

theorem syncSeq_fst (M : SyncMsg) : (syncSeq M).map Prod.fst = syncOrder M := by
  rw [syncSeq_eq, List.map_map]; exact List.map_id' _

end sp

theorem swift.lkOf_snoc (s : sp.Seq) (p : sp.CmdId × sp.Cmd) (k : w64) :
    swift.lkOf (s ++ [p]) k =
      if p.2.key = k then swift.lki.addTo p.2.op (ofCmdId p.1) (swift.lkOf s k).1 (swift.lkOf s k).2
      else swift.lkOf s k := by
  unfold swift.lkOf; rw [List.foldl_append]; rfl

/-! ## The run loop's state as `handleSync` finds it -/

/-- `localOk`, but the row of `b'` may be there (the new leader's computed order). -/
def swift.localOkS (N r : Nat) (ld : Bool) (v : swift.RunV) (M : Option sp.SyncMsg)
    (w : swift.LView) (b' : Nat) : Prop :=
  0 ≤ sint.Z v.ballot ∧ 0 ≤ sint.Z v.cballot ∧
  w.1 = sp.bal v.ballot ∧ w.2.1 = sp.bal v.cballot ∧
  (w.2.2.1 = true ↔ v.status = swift.stNORMAL) ∧
  (w.2.2.1 = true → w.2.1 = w.1) ∧
  (M = none ↔ w.2.1 = 0) ∧
  w.locAt w.2.1 = (M.map sp.syncOrder).getD [] ++ v.handled.map toCmdId ∧
  (∀ y ∈ w.locAt w.2.1, (v.propsM !! ofCmdId y).isSome) ∧
  (∀ b o, w.2.1 < b → b ≠ b' → (b, o) ∉ w.2.2.2) ∧
  (ld = true ↔ sp.leaderOf N w.2.1 = r)

theorem swift.localOk_localOkS {N r : Nat} {ld : Bool} {v : swift.RunV} {M : Option sp.SyncMsg}
    {w : swift.LView} (b' : Nat) (h : swift.localOk N r ld v M w) : swift.localOkS N r ld v M w b' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, -⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, fun b o hb _ => h10 b o hb, h11⟩

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [swift.Assumptions]

/-- `runSt` with `localOkS` (see the file header). -/
def swift.runStS (γ : sp.Names) (γv : GName) (rp : Loc) (N r : Nat) (ld : Bool) (v : swift.RunV)
    (M : Option sp.SyncMsg) (bs hd : sp.Seq) (w : swift.LView) (b' : Nat) : IProp netDistGF :=
  iprop(typedPointsto (swift.fld rp go!"ballot") v.ballot (DFrac.own (1 : Qp).half.half) ∗
    swift.fld rp go!"cballot" ↦ v.cballot ∗
    typedPointsto (swift.fld rp go!"status") v.status (DFrac.own (1 : Qp).half) ∗
    swift.fld rp go!"handled" ↦ v.hdSl ∗ v.hdSl ↦* v.handled ∗
      ownSliceCap swift.CommandId v.hdSl (DFrac.own 1) ∗
    swift.fld rp go!"proposes" ↦ v.props ∗ swift.propsOwn γ v.props v.propsM ∗
    swift.fld rp go!"keys" ↦ v.keys ∗
      swift.keysOwn v.keys v.keysM (bs ++ hd) ∗
    swift.fld rp go!"hlog" ↦ v.hlog ∗
      (∃ Λ, swift.hlogOwn v.hlog v.hlogM ld hd (swift.propsK v.propsM) Λ ∗
        swift.ldSound γ (sp.leaderOf N w.2.1) w.2.1 Λ) ∗
    swift.fld rp go!"pendingHashUpds" ↦ v.pend ∗
      swift.pendOwnH γ (sp.leaderOf N w.2.1) w.2.1 v.pend v.pendM ∗
    swift.fld rp go!"lastSync" ↦ v.lastSync ∗ swift.syncObj γ N v.lastSync w.2.1 M ∗
    ghostVar γv (1 : Qp).half w ∗ sp.locLb γ r w.2.1 (bs ++ hd) ∗
    ⌜swift.localOkS N r ld v M w b' ∧ hd.map Prod.fst = v.handled.map toCmdId ∧
      bs.map Prod.fst = (M.map sp.syncOrder).getD []⌝)

theorem swift.runSt_runStS (γ : sp.Names) (γv : GName) (rp : Loc) (N r : Nat) (ld : Bool)
    (v : swift.RunV) (M : Option sp.SyncMsg) (bs hd : sp.Seq) (w : swift.LView) (b' : Nat) :
    swift.runSt γ γv rp N r ld v M bs hd w ⊢ swift.runStS γ γv rp N r ld v M bs hd w b' := by
  unfold swift.runSt swift.runStS
  iintro ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, H17, H18, %Hok⟩
  iframe
  ipureintro
  exact ⟨swift.localOk_localOkS b' Hok.1, Hok.2⟩

end defs

/-! ## The ghost composition after taking the `MSync` -/

section compose
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [swift.Assumptions]

/-- The run loop's values after `handleSync`. -/
def swift.RunV.synced (v : swift.RunV) (bl : w32) (hsl : GoSlice) (pm : Loc)
    (pM : GMap swift.CommandId Loc) (km : Loc) (kM : GMap w64 GoInterface) (hm pp ls : Loc) :
    swift.RunV :=
  { ballot := bl, cballot := bl, status := swift.stNORMAL, hdSl := hsl, handled := [],
    props := pm, propsM := pM, keys := km, keysM := kM, hlog := hm, hlogM := ∅, pend := pp,
    pendM := ∅, lastSync := ls }

/-- **The ghost composition** (see the file header): after `swift.takeSync_step` and the Go
fields' reset, the run loop's state is `runSt` at `b'`, base `syncSeq M`, nothing handled. -/
theorem swift.sync_runSt (γ : sp.Names) (γv : GName) (rp : Loc) (N r : Nat) (ld : Bool)
    (v : swift.RunV) (M0 : Option sp.SyncMsg) (w : swift.LView) (b' : Nat) (M : sp.SyncMsg)
    (bl : w32) (hsl : GoSlice) (pm : Loc) (pM : GMap swift.CommandId Loc) (km : Loc)
    (kM : GMap w64 GoInterface) (hm pp ls : Loc)
    (hok : swift.localOkS N r ld v M0 w b') (hb' : w.2.1 < b') (hbl : sp.bal bl = b')
    (hprops : ∀ y ∈ sp.syncOrder M, (pM !! ofCmdId y).isSome)
    (hprops' : ∀ y, (pM !! ofCmdId y).isSome → y ∈ sp.syncOrder M) :
    typedPointsto (swift.fld rp go!"ballot") bl (DFrac.own (1 : Qp).half.half) ∗
    swift.fld rp go!"cballot" ↦ bl ∗
    typedPointsto (swift.fld rp go!"status") swift.stNORMAL (DFrac.own (1 : Qp).half) ∗
    swift.fld rp go!"handled" ↦ hsl ∗ hsl ↦* ([] : List swift.CommandId) ∗
      ownSliceCap swift.CommandId hsl (DFrac.own 1) ∗
    swift.fld rp go!"proposes" ↦ pm ∗ swift.propsOwn γ pm pM ∗
    swift.fld rp go!"keys" ↦ km ∗ swift.keysOwn km kM (sp.syncSeq M) ∗
    swift.fld rp go!"hlog" ↦ hm ∗ hm ↦$ (∅ : GMap w64 Loc) ∗
    swift.fld rp go!"pendingHashUpds" ↦ pp ∗ pp ↦$ (∅ : GMap swift.CommandId Loc) ∗
    swift.fld rp go!"lastSync" ↦ ls ∗ swift.syncMaps ls b' M ∗ sp.syncIs γ b' M ∗
    sp.locLb γ (sp.leaderOf N b') b' (sp.syncSeq M) ∗
    ghostVar γv (1 : Qp).half (w.tookSync b' (sp.syncOrder M)) ∗
    ([∗list] i ↦ x ∈ sp.syncOrder M, sp.locAt γ r b' i x) ∗
    ([∗list] p ∈ M, sp.cmdIs γ p.1 p.2.1) ⊢
    swift.runSt γ γv rp N r (decide (sp.leaderOf N b' = r))
      (v.synced bl hsl pm pM km kM hm pp ls) (some M) (sp.syncSeq M) []
      (w.tookSync b' (sp.syncOrder M)) := by
  iintro ⟨Hb, Hcb, Hst, Hh, Hhs, Hhc, Hp, HP, Hk, HK, Hl, HL, Hpp, HPP, Hls, #HM, #HMs, #HlbL, Hw,
    #Hloc, #Hcmds⟩
  unfold swift.runSt swift.RunV.synced
  simp only [List.append_nil]
  iframe Hb Hcb Hst Hh Hhs Hhc Hp HP Hk HK Hl Hpp Hls Hw
  ihave #HM2 := HM
  iunfold swift.syncMaps at HM2
  icases HM2 with ⟨%rep, %bl', %ph, %cm, %dp, %phM, %cmM, %dpM, #Hls, -, -, -, %Hf, -⟩
  have hnd := Hf.2.1
  have hbpos : 0 < b' := by have := Nat.zero_le w.2.1; omega
  have hblnn : 0 ≤ sint.Z bl := by
    have : sp.bal bl = bl.toInt.toNat := rfl
    have : 0 < bl.toInt := by omega
    exact Int.le_of_lt this
  isplitl [HL]
  · iexists (fun _ _ _ => False)
    unfold swift.hlogOwn swift.ldSound
    iframe HL
    isplitl
    · isplitl
      · iapply (BigSepM.bigSepM_eqv_empty (Φ := fun k l =>
          swift.hlogEnt (decide (sp.leaderOf N b' = r)) [] (swift.propsK pM)
            (fun _ _ _ => False) k l) rfl).2
        itrivial
      · ipureintro; intro k _; rfl
    · imodintro; iintro %k %s %P %h; exact h.elim
  isplitl [HPP]
  · unfold swift.pendOwnH
    iframe HPP
    iapply (BigSepM.bigSepM_eqv_empty (Φ := fun (x : swift.CommandId) (u : Loc) =>
      iprop(∃ (sl : GoSlice) (sq : w64) (H : swift.SHash) (P : List sp.CmdId),
        u ↦□ swift.UpdateEntry.mk sl sq ∗ sl ↦*□ [H] ∗ sp.startHash P H.H'.arr ∗
        sp.numIs γ (sp.leaderOf N (w.tookSync b' (sp.syncOrder M)).2.1)
          (w.tookSync b' (sp.syncOrder M)).2.1 (toCmdId x) sq ∗
        sp.pathIs γ (sp.leaderOf N (w.tookSync b' (sp.syncOrder M)).2.1)
          (w.tookSync b' (sp.syncOrder M)).2.1 (toCmdId x) P)) rfl).2
    itrivial
  have e1 : (w.tookSync b' (sp.syncOrder M)).1 = b' := rfl
  have e2 : (w.tookSync b' (sp.syncOrder M)).2.1 = b' := rfl
  have e3 : (w.tookSync b' (sp.syncOrder M)).2.2.1 = true := rfl
  rw [e2]
  isplitr
  · unfold swift.syncObj
    iexists ph, cm, dp, rep, bl'
    iframe Hls HMs HM HlbL
    ipureintro
    show sp.bal bl' = b'
    exact Hf.1
  isplitr
  · -- the base's `locLb`: the order's `locAt`s, with the commands' `cmdIs` (the leader's
    -- `HlbL` cleared first: `unfold`/`rw` act on the context too)
    iclear HlbL
    unfold sp.locLb
    rw [sp.syncSeq_eq, BigSepL.bigSepL_map]
    iapply BigSepL.bigSepL_sep_eqv.2
    isplitl []
    iframe Hloc
    iapply (BigSepL.bigSepL_intro (P := iprop(□ [∗list] p ∈ M, sp.cmdIs γ p.1 p.2.1)))
    · intro i x hx
      iintro #H
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (sp.syncOrder_mem M x (List.mem_of_getElem? hx))
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hp
      rw [sp.syncCmd_of_mem hnd hp]
      iapply (BigSepL.bigSepL_lookup hj) $$ H
    · iexact Hcmds
  ipureintro
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hok
  have hsucc : ∀ b, (w.tookSync b' (sp.syncOrder M)).locAt b = if b = b' then sp.syncOrder M
      else w.locAt b := swift.LView.tookSync_locAt w b' (sp.syncOrder M)
  refine ⟨⟨hblnn, hblnn, by rw [e1, hbl], by rw [e2, hbl], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    by simp, by rw [sp.syncSeq_fst]; rfl⟩
  · rw [e3]; simp
  · intro _; rw [e1, e2]
  · simp only [reduceCtorEq, false_iff]; omega
  · rw [e2, hsucc, if_pos rfl]; simp
  · intro y hy
    rw [e2, hsucc, if_pos rfl] at hy
    exact hprops y hy
  · intro b o hb hmem
    rw [e2] at hb
    change (b, o) ∈ (b', sp.syncOrder M) :: w.2.2.2 at hmem
    rcases List.mem_cons.mp hmem with e | e
    · have := congrArg Prod.fst e; simp only at this; omega
    · exact h10 b o (by omega) (by omega) e
  · rw [e2]; simp
  · rw [e2, hsucc, if_pos rfl]; exact sp.syncOrder_nodup M
  · intro y hy
    rw [e2, hsucc, if_pos rfl]
    exact hprops' y hy

end compose

/-! ## Rebuilding `keys` along the `MSync`'s sequence -/

section keys
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [swift.Assumptions]

/-- The keys' map along `s`, its contents only (`keysOwn` without the map's points-to), with the
keys that have no entry untouched by `s`. -/
def swift.keysIn (kM : GMap w64 GoInterface) (s : sp.Seq) : IProp netDistGF :=
  iprop(([∗map] k ↦ ki ∈ kM, swift.keyEnt s k ki) ∗
    ⌜∀ k, kM !! k = none → swift.lkOf s k = ([], [])⌝)

theorem swift.keysIn_nil : ⊢ swift.keysIn (∅ : GMap w64 GoInterface) [] := by
  unfold swift.keysIn
  isplitl
  · iapply (BigSepM.bigSepM_eqv_empty (Φ := fun k ki => swift.keyEnt [] k ki) rfl).2
    itrivial
  · ipureintro; intro k _; rfl

theorem swift.keysIn_own (km : Loc) (kM : GMap w64 GoInterface) (s : sp.Seq) :
    km ↦$ kM ∗ swift.keysIn kM s ⊢ swift.keysOwn km kM s := by
  unfold swift.keysIn swift.keysOwn
  iintro ⟨H, H2, %H3⟩
  iframe
  ipureintro; exact H3

/-- The key of `c` has an entry `ki`: its `lightKeyInfo`, and the way back after `add`. -/
theorem swift.keysIn_lookup (kM : GMap w64 GoInterface) (s : sp.Seq) (x : sp.CmdId) (c : sp.Cmd)
    (ki : GoInterface) (hki : kM !! c.key = some ki) :
    swift.keysIn kM s ⊢ ∃ kl : Loc,
      ⌜ki = interface.ok ⟨go.GoType.PointerType swift.lightKeyInfo.ty, #kl⟩⌝ ∗
      swift.lki.lkiOwn kl (swift.lkOf s c.key).1 (swift.lkOf s c.key).2 ∗
      (swift.lki.lkiOwn kl (swift.lki.addTo c.op (ofCmdId x) (swift.lkOf s c.key).1
          (swift.lkOf s c.key).2).1
        (swift.lki.addTo c.op (ofCmdId x) (swift.lkOf s c.key).1 (swift.lkOf s c.key).2).2 -∗
        swift.keysIn kM (s ++ [(x, c)])) := by
  unfold swift.keysIn swift.keyEnt
  iintro ⟨Hm, %Hnone⟩
  icases (BigSepM.bigSepM_delete (show Iris.Std.PartialMap.get? kM c.key = some ki from hki)).1
    $$ Hm with ⟨⟨%kl, %Hkl, Hl⟩, Hrest⟩
  iexists kl
  iframe Hl
  isplitr
  · ipureintro; exact Hkl
  iintro Hl
  isplitl
  · iapply (BigSepM.bigSepM_delete (show Iris.Std.PartialMap.get? kM c.key = some ki from hki)).2
    isplitl [Hl]
    · iexists kl
      isplitr
      · ipureintro; exact Hkl
      rw [swift.lkOf_snoc, if_pos rfl]
      iexact Hl
    · iapply BigSepM.bigSepM_mono _ $$ Hrest
      intro k v hk
      have hne : k ≠ c.key := by
        intro h; subst h
        rw [Iris.Std.LawfulPartialMap.get?_delete] at hk; simp at hk
      rw [swift.lkOf_snoc, if_neg (fun h => hne h.symm)]
  · ipureintro
    intro k hk
    have hne : c.key ≠ k := fun h => by rw [← h, hki] at hk; cases hk
    rw [swift.lkOf_snoc, if_neg hne]
    exact Hnone k hk

/-- The key of `c` has no entry: a new `lightKeyInfo` (after `add`) is inserted. -/
theorem swift.keysIn_new (kM : GMap w64 GoInterface) (s : sp.Seq) (x : sp.CmdId) (c : sp.Cmd)
    (kl : Loc) (hki : kM !! c.key = none) :
    swift.keysIn kM s ∗ swift.lki.lkiOwn kl (swift.lki.addTo c.op (ofCmdId x) [] []).1
        (swift.lki.addTo c.op (ofCmdId x) [] []).2 ⊢
      swift.keysIn (<[c.key := interface.ok ⟨go.GoType.PointerType swift.lightKeyInfo.ty, #kl⟩]> kM)
        (s ++ [(x, c)]) := by
  unfold swift.keysIn swift.keyEnt
  iintro ⟨⟨Hm, %Hnone⟩, Hl⟩
  have h0 := Hnone c.key hki
  isplitl
  · iapply (BigSepM.bigSepM_insert (show Iris.Std.PartialMap.get? kM c.key = none from hki)).2
    isplitl [Hl]
    · iexists kl
      isplitr
      · ipureintro; rfl
      rw [swift.lkOf_snoc, if_pos rfl, h0]
      iexact Hl
    · iapply BigSepM.bigSepM_mono _ $$ Hm
      intro k v hk
      have hne : c.key ≠ k := fun h => by
        subst h; simp [Iris.Std.PartialMap.get?] at hk; rw [hki] at hk; cases hk
      rw [swift.lkOf_snoc, if_neg hne]
  · ipureintro
    intro k hk
    have hne : c.key ≠ k := fun h => by subst h; rw [GMap.lookup_insert] at hk; cases hk
    rw [GMap.lookup_insert_ne _ _ hne] at hk
    rw [swift.lkOf_snoc, if_neg hne]
    exact Hnone k hk

end keys

end Perennial.github_com.imdea_software.swiftpaxos
