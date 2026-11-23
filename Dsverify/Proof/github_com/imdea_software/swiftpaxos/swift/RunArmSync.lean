/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/RunArmSync.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The run loop's `sync` arm (round 33, sv-swc; prove-swift.md §38): `r.handleSync(msg)` for an
`MSync` from the `syncChan` (a peer's, decoded by the codec: `swift.msgRepM … (.sync m)`, with its
witness `sp.msgOk (.sync m)`) over `swift.runInv` (RunInvD.lean), from `handleSync.specIR`
(SyncSpecs.lean; SW4 step 2: `specI = specIR`) at the descriptors' state (`descDS`, `descEpS`,
`descDFA`; SyncLinkD's `wp_handleSyncD` is an instance).

* `swift.syncMaps_of_wire`: the codec's owned `MSync` (`structOwn`) listing `M`
  (`sp.syncWireOk`, `M`'s ids distinct) is, after persisting it, `swift.syncMaps l (bal m.bal) M`
  (the Go maps as `↦$□` over `swift.gmapOfList` of their entries);
* `sp.syncIs_facts`: a ballot's `MSync` is of a positive ballot and has distinct ids
  (`sync_ok`: `M = recoverSync N reps`, `sp.recoverSync_nodup`);
* `swift.runArm_sync`: a later ballot than the run loop's: `specIR` (its row disjunct is
  `locAt b' = []`, `localOk`); an equal or older one: `handleSync`'s first `return`, proved here
  (its first lines: `r.ballot > msg.Ballot || (r.ballot == msg.Ballot && r.status == NORMAL)`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunArmReinit
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncFacts
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncAux
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.MsgRep
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DescFresh
import all Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Inv

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-! ## Pure: a recovered `MSync` has distinct ids -/

theorem sp.filterMap_fst_sublist {β : Type} (f : sp.CmdId → Option (sp.CmdId × β))
    (hf : ∀ c p, f c = some p → p.1 = c) :
    ∀ O : List sp.CmdId, ((O.filterMap f).map Prod.fst).Sublist O
  | [] => by simp
  | c :: O => by
    rw [List.filterMap_cons]
    cases h : f c with
    | none => exact (sp.filterMap_fst_sublist f hf O).cons c
    | some p =>
      simp only [List.map_cons]
      rw [hf c p h]
      exact (sp.filterMap_fst_sublist f hf O).cons_cons c

theorem sp.lkAlong_fst (cs : sp.Seq) : (sp.lkAlong cs).map Prod.fst = cs.map Prod.fst := by
  have h := congrArg (List.map Prod.fst) (sp.lkAlong_ids cs)
  simpa [List.map_map, Function.comp_def] using h

theorem sp.recoverSync_nodup (N : Nat) (reps : List (Nat × sp.Report)) :
    ((sp.recoverSync N reps).map Prod.fst).Nodup := by
  unfold sp.recoverSync
  simp only []
  rw [sp.lkAlong_fst]
  refine (sp.filterMap_fst_sublist _ ?_ _).nodup (sp.recOrder_nodup _ _)
  intro c p h
  cases hk : Kept.get _ c with
  | none => rw [hk] at h; cases h
  | some e => rw [hk] at h; cases h; rfl

/-! ## Ghost: a ballot's `MSync` -/

section ghost
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable {γ : sp.Names} {γc γm γl : GName}

/-- **A ballot's `MSync`**: its ballot is positive and its ids are distinct (`sync_ok`). -/
theorem sp.syncIs_facts (E : CoPset) (hE : ↑sp.spN ⊆ E) (b : Nat) (M : sp.SyncMsg) :
    sp.inv γ γc γm γl ∗ sp.syncIs γ b M ⊢ |={E}=> ⌜0 < b ∧ (M.map Prod.fst).Nodup⌝ := by
  unfold sp.inv sp.syncIs
  iintro ⟨#Hinv, #HM⟩
  iinv Hinv with Hi Hclose
  unfold sp.invBody
  icases Hi with ⟨%S, %mC, %mL, %mS, %mA, %mP, %mCo, %mR, %mN, %sh, %mD, %mQ, %mK, %mPa, HC, HL, >HS, HA, HP, HCo, HRp, HN, HH, HD, Hown, HQ, HK, HPa, >%Hrepr, Hnodes, Hproto, HQs, HCl, HDom, Hslots, Hconns⟩
  ihave %Hlk := ghost_map_lookup $$ HS HM
  have hS : S.sync b = some M := by rw [← Hrepr.sync]; exact Hlk
  icases Hproto with (>%Hemp | ⟨%N, %fr, %l, #Hcfg, >%HP⟩)
  · exact absurd (Hemp.1.2.1 b ▸ hS) (by simp)
  · obtain ⟨hb, -, -, reps, -, -, hM⟩ := HP.1.sync_ok b M hS
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
    exact ⟨hb, hM ▸ sp.recoverSync_nodup N reps⟩

/-- An `MSync`'s length bound (`cmdIs_list_len` over `syncIs_cmdIs`). -/
theorem sp.syncIs_len (E : CoPset) (hE : ↑sp.spN ⊆ E) (b : Nat) (M : sp.SyncMsg)
    (hnd : (M.map Prod.fst).Nodup) :
    sp.inv γ γc γm γl ∗ sp.syncIs γ b M ⊢ |={E}=> ⌜M.length ≤ 6 * 2 ^ 25⌝ := by
  iintro ⟨#Hinv, #HM⟩
  imod sp.syncIs_cmdIs E hE b M $$ [Hinv HM] with #Hl
  · iframe Hinv HM
  ihave #Hl2 : (□ [∗list] x ∈ M.map Prod.fst, ∃ c, sp.cmdIs γ x c) $$ [Hl]
  · imodintro
    iapply (BigSepL.bigSepL_intro (P := iprop(□ [∗list] p ∈ M, sp.cmdIs γ p.1 p.2.1)))
    · intro k y hy
      rw [List.getElem?_map] at hy
      cases hp : M[k]? with
      | none => rw [hp] at hy; cases hy
      | some p =>
        rw [hp] at hy
        cases hy
        iintro #H
        iexists p.2.1
        iapply (BigSepL.bigSepL_lookup (Φ := fun _ p => sp.cmdIs γ p.1 p.2.1) hp)
        iexact H
    iexact Hl
  imod sp.cmdIs_list_len E hE (M.map Prod.fst) hnd $$ [Hinv Hl2] with %Hb
  · iframe Hinv Hl2
  imodintro
  ipureintro
  simpa using Hb

end ghost

/-! ## The codec's `MSync` as `syncMaps` -/

section conv
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [swift.Assumptions] [examples.swiftnet.Assumptions]

/-- The Go map of a listing (first entry of a key wins, as `map.lookupL`). -/
def swift.gmapOfList {V : Type} (ps : List (swift.CommandId × V)) : GMap swift.CommandId V :=
  ps.foldr (fun p m => <[p.1 := p.2]> m) ∅

theorem swift.gmapOfList_lookup {V : Type} (ps : List (swift.CommandId × V)) (k : swift.CommandId) :
    (swift.gmapOfList ps) !! k = map.lookupL k ps := by
  induction ps with
  | nil => simp [swift.gmapOfList, map.lookupL]
  | cons p ps ih =>
    simp only [swift.gmapOfList, List.foldr_cons, map.lookupL] at ih ⊢
    by_cases h : k = p.1
    · subst h; simp [GMap.lookup_insert]
    · rw [if_neg h, GMap.lookup_insert_ne _ _ (Ne.symm h)]; exact ih

theorem swift.lookupL_isSome {V : Type} (ps : List (swift.CommandId × V)) (k : swift.CommandId) :
    (map.lookupL k ps).isSome = true ↔ k ∈ ps.map Prod.fst := by
  induction ps with
  | nil => simp [map.lookupL]
  | cons p ps ih =>
    simp only [map.lookupL, List.map_cons, List.mem_cons]
    by_cases h : k = p.1
    · simp [h]
    · simp [h, ih]

theorem swift.lookupL_mem {V : Type} (ps : List (swift.CommandId × V)) (q : swift.CommandId × V)
    (hnd : (ps.map Prod.fst).Nodup) (hq : q ∈ ps) : map.lookupL q.1 ps = some q.2 := by
  induction ps with
  | nil => cases hq
  | cons p ps ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [map.lookupL]
    rcases List.mem_cons.1 hq with rfl | hq'
    · simp
    · have hne : q.1 ≠ p.1 := fun h => hnd.1 (h ▸ List.mem_map_of_mem hq')
      rw [if_neg hne]; exact ih hnd.2 hq'

theorem swift.goCmdId_eq (c : swift.CommandId) : goCmdId c = toCmdId c := rfl

/-- `bupd` through a list's big separating conjunction. -/
theorem swift.bigSepL_bupd {A : Type} :
    ∀ (l : List A) (Φ Ψ : Nat → A → IProp netDistGF), (∀ k x, Φ k x ⊢ |==> Ψ k x) →
      ([∗list] k ↦ x ∈ l, Φ k x) ⊢ |==> [∗list] k ↦ x ∈ l, Ψ k x
  | [], _, _, _ => by
    iintro -
    imodintro
    iapply (BigSepL.bigSepL_nil_intro (P := iprop(True)))
    itrivial
  | a :: l, Φ, Ψ, h => by
    iintro H
    ihave ⟨H0, Hl⟩ := BigSepL.bigSepL_cons.1 $$ H
    imod h 0 a $$ H0 with H0
    imod swift.bigSepL_bupd l (fun k x => Φ (k + 1) x) (fun k x => Ψ (k + 1) x)
      (fun k x => h (k + 1) x) $$ Hl with Hl
    imodintro
    iapply BigSepL.bigSepL_cons.2
    iframe

/-- The codec's owned map listing as a map points-to (`gmapOfList` of the Go entries). -/
theorem swift.mapOwn_own {V A : Type} [ZeroVal V] (mp : Loc)
    (R : V → A → IProp netDistGF) (L : List (sp.CmdId × A)) :
    mapOwn mp (DFrac.own 1) R (some L) ⊢ ∃ ps : List (swift.CommandId × V),
      heapPointsto mp (DFrac.own 1) (map.mapV #(zero_val V) (ps.map map.toE)) ∗
      ⌜(ps.map Prod.fst).Nodup ∧ ps.map (fun p => goCmdId p.1) = L.map Prod.fst⌝ ∗
      [∗list] i ↦ e ∈ L, ∃ p : swift.CommandId × V, ⌜ps[i]? = some p⌝ ∗ R p.2 e.2 := by
  iintro H
  unfold mapOwn
  icases H with ⟨%mv, %ps, Hh, %Hr, HL⟩
  obtain ⟨hmv, hnd, hfst⟩ := Hr
  subst hmv
  iexists ps
  iframe
  ipureintro; exact ⟨hnd, hfst⟩

instance swift.cmdOwn_discard_persistent (c : state.Command) (y : sp.Cmd) :
    Persistent (cmdOwn (GF := netDistGF) c DFrac.discard y) := by
  unfold cmdOwn; infer_instance

/-- **The codec's `MSync` as `syncMaps`** (see the file header): its struct and maps persisted,
the maps as `↦$□` of `gmapOfList` of their Go entries. -/
theorem swift.syncMaps_of_wire (l : Loc) (m : sp.SyncWire) (M : sp.SyncMsg)
    (hok : sp.syncWireOk m M) (hnd : (M.map Prod.fst).Nodup) :
    structOwn (GF := netDistGF) swift.MSync.ty l (DFrac.own 1) (.msync m) ⊢
      |==> swift.syncMaps l (sp.bal m.bal) M := by
  haveI := swift.hlog.cmdId_intoValInj (sem := sem)
  obtain ⟨⟨psW, hpW, hpP⟩, ⟨csW, hcW, hcP⟩, ⟨dsW, hdW, hdP⟩⟩ := hok
  simp only [structOwn]
  rw [hpW, hcW, hdW]
  iintro ⟨-, %ph, %cm, %dp, Hl, Hph, Hcm, Hdp⟩
  ihave ⟨%psP, HhP, %HP, -⟩ := swift.mapOwn_own (V := w64) ph _ psW $$ Hph
  ihave ⟨%psC, HhC, %HC, HLC⟩ := swift.mapOwn_own (V := state.Command) cm _ csW $$ Hcm
  ihave ⟨%psD, HhD, %HD, HLD⟩ := swift.mapOwn_own (V := swift.Dep) dp _ dsW $$ Hdp
  imod heapPointsto_persist _ _ _ $$ HhP with #HhP
  imod heapPointsto_persist _ _ _ $$ HhC with #HhC
  imod heapPointsto_persist _ _ _ $$ HhD with #HhD
  imod (typedPointsto_dfractional _ _).dfractional_persist (DFrac.own 1) $$ Hl with #Hl
  imod swift.bigSepL_bupd csW
    (fun i e => iprop(∃ p : swift.CommandId × state.Command, ⌜psC[i]? = some p⌝ ∗
      cmdOwn p.2 (DFrac.own 1) e.2))
    (fun i e => iprop(∃ p : swift.CommandId × state.Command, ⌜psC[i]? = some p⌝ ∗
      cmdOwn p.2 DFrac.discard e.2))
    (fun i e => by
      iintro ⟨%p, %hp, Hc⟩
      unfold cmdOwn
      icases Hc with ⟨%h, Hv⟩
      imod ownSlice_persist _ _ _ $$ Hv with Hv
      imodintro
      iexists p
      iframe
      ipureintro; exact ⟨hp, h⟩) $$ HLC with #HLC
  imod swift.bigSepL_bupd dsW
    (fun i e => iprop(∃ p : swift.CommandId × swift.Dep, ⌜psD[i]? = some p⌝ ∗
      ∃ ids : List swift.CommandId, p.2 ↦*{DFrac.own 1} ids ∗ ⌜ids.map goCmdId = e.2⌝))
    (fun i e => iprop(∃ p : swift.CommandId × swift.Dep, ⌜psD[i]? = some p⌝ ∗
      ∃ ids : List swift.CommandId, p.2 ↦*□ ids ∗ ⌜ids.map goCmdId = e.2⌝))
    (fun i e => by
      iintro ⟨%p, %hp, %ids, Hv, %h⟩
      imod ownSlice_persist _ _ _ $$ Hv with Hv
      imodintro
      iexists p
      isplitr
      · ipureintro; exact hp
      iexists ids
      iframe
      ipureintro; exact h) $$ HLD with #HLD
  ihave #HmP : (ph ↦$□ (swift.gmapOfList psP : GMap swift.CommandId w64)) $$ [HhP]
  · rw [ownMap_unseal]; unfold ownMapDef
    iexists _, psP
    iframe HhP
    ipureintro
    exact ⟨rfl, HP.1, fun _ _ => trivial, fun k => swift.gmapOfList_lookup psP k⟩
  ihave #HmC : (cm ↦$□ (swift.gmapOfList psC : GMap swift.CommandId state.Command)) $$ [HhC]
  · rw [ownMap_unseal]; unfold ownMapDef
    iexists _, psC
    iframe HhC
    ipureintro
    exact ⟨rfl, HC.1, fun _ _ => trivial, fun k => swift.gmapOfList_lookup psC k⟩
  ihave #HmD : (dp ↦$□ (swift.gmapOfList psD : GMap swift.CommandId GoSlice)) $$ [HhD]
  · rw [ownMap_unseal]; unfold ownMapDef
    iexists _, psD
    iframe HhD
    ipureintro
    exact ⟨rfl, HD.1, fun _ _ => trivial, fun k => swift.gmapOfList_lookup psD k⟩
  -- the keys
  have hinj : ∀ (V : Type) (ps : List (swift.CommandId × V)) (y : swift.CommandId),
      toCmdId y ∈ ps.map (fun p => goCmdId p.1) ↔ y ∈ ps.map Prod.fst := by
    intro V ps y
    simp only [List.mem_map]
    constructor
    · rintro ⟨q, hq, he⟩
      refine ⟨q, hq, ?_⟩
      have := congrArg ofCmdId he
      simpa [swift.goCmdId_eq] using this
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q, hq, rfl⟩
  have hkeys : ∀ y, ((swift.gmapOfList psP : GMap swift.CommandId w64) !! y).isSome = true ↔
      toCmdId y ∈ M.map Prod.fst := by
    intro y
    rw [swift.gmapOfList_lookup, swift.lookupL_isSome, ← hinj, HP.2]
    have hperm := hpP.map Prod.fst
    rw [List.map_map] at hperm
    exact hperm.mem_iff
  imodintro
  iunfold swift.syncMaps
  iexists m.rep, m.bal, ph, cm, dp, swift.gmapOfList psP, swift.gmapOfList psC, swift.gmapOfList psD
  iframe Hl HmP HmC HmD
  isplitr
  · ipureintro; exact ⟨rfl, hnd, hkeys⟩
  iapply (BigSepL.bigSepL_intro (P := iprop(□ (([∗list] i ↦ e ∈ csW,
      ∃ p : swift.CommandId × state.Command, ⌜psC[i]? = some p⌝ ∗ cmdOwn p.2 DFrac.discard e.2) ∗
    ([∗list] i ↦ e ∈ dsW, ∃ p : swift.CommandId × swift.Dep, ⌜psD[i]? = some p⌝ ∗
      ∃ ids : List swift.CommandId, p.2 ↦*□ ids ∗ ⌜ids.map goCmdId = e.2⌝)))))
  · intro k p hp
    have hpm : p ∈ M := List.mem_of_getElem? hp
    have hc : (p.1, p.2.1) ∈ csW := hcP.mem_iff.2 (List.mem_map_of_mem hpm)
    have hd : (p.1, p.2.2) ∈ dsW := hdP.mem_iff.2 (List.mem_map_of_mem hpm)
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hc
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hd
    iintro #⟨HC', HD'⟩
    icases BigSepL.bigSepL_lookup (Φ := fun i e => iprop(∃ p : swift.CommandId × state.Command,
        ⌜psC[i]? = some p⌝ ∗ cmdOwn p.2 DFrac.discard e.2)) hi $$ HC' with ⟨%q, %hq, Hq⟩
    icases BigSepL.bigSepL_lookup (Φ := fun i e => iprop(∃ p : swift.CommandId × swift.Dep,
        ⌜psD[i]? = some p⌝ ∗ ∃ ids : List swift.CommandId, p.2 ↦*□ ids ∗
          ⌜ids.map goCmdId = e.2⌝)) hj $$ HD' with ⟨%q', %hq', %ids, #Hids, %hids⟩
    have hq1 : goCmdId q.1 = p.1 := by
      have h := congrArg (fun L : List sp.CmdId => L[i]?) HC.2
      simp only [List.getElem?_map, hq, hi, Option.map_some] at h
      exact Option.some.inj h
    have hq1' : goCmdId q'.1 = p.1 := by
      have h := congrArg (fun L : List sp.CmdId => L[j]?) HD.2
      simp only [List.getElem?_map, hq', hj, Option.map_some] at h
      exact Option.some.inj h
    have hlkC : (swift.gmapOfList psC : GMap swift.CommandId state.Command) !! ofCmdId p.1 = some q.2 := by
      rw [swift.gmapOfList_lookup, ← hq1, swift.goCmdId_eq, ofCmdId_toCmdId]
      exact swift.lookupL_mem psC q HC.1 (List.mem_of_getElem? hq)
    have hlkD : (swift.gmapOfList psD : GMap swift.CommandId GoSlice) !! ofCmdId p.1 = some q'.2 := by
      rw [swift.gmapOfList_lookup, ← hq1', swift.goCmdId_eq, ofCmdId_toCmdId]
      exact swift.lookupL_mem psD q' HD.1 (List.mem_of_getElem? hq')
    have hids' : ids = p.2.2.map ofCmdId := by
      rw [← hids, List.map_map]
      simp [Function.comp_def, swift.goCmdId_eq]
    unfold cmdOwn
    icases Hq with ⟨%hok, #Hv⟩
    obtain ⟨q1, ⟨o, kk, vv⟩⟩ := q
    simp only at hok hlkC
    obtain ⟨rfl, rfl⟩ := hok
    iexists vv, q'.2
    isplitr
    · ipureintro; exact ⟨hlkC, hlkD⟩
    rw [← hids']
    iframe Hv Hids
  iframe HLC HLD

end conv

/-! ## The arm -/

section arm
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions] [examples.swiftnet.Assumptions]

set_option goose.wp.extras true

/-- `runSt`'s relation of the run loop's values to its view. -/
theorem swift.runSt_localOk (γ : sp.Names) (γv : GName) (rp : Loc) (N r : Nat) (ld : Bool)
    (v : swift.RunV) (M : Option sp.SyncMsg) (bs hd : sp.Seq) (w : swift.LView) :
    swift.runSt γ γv rp N r ld v M bs hd w ⊢ ⌜swift.localOk N r ld v M w⌝ := by
  iintro H
  iunfold swift.runSt at H
  icases H with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, %Hok⟩
  ipureintro; exact Hok.1

/-- What `syncSendCtx` takes of `runLoopCtx` (persistent). -/
theorem swift.runLoopCtx_send (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX) :
    swift.runLoopCtx rp γ γc γm x ⊢ ∃ (s : Loc) (γs : ChanNames) (csv : swift.CommunicationSupply),
      swift.fld rp go!"sender" ↦□ s ∗ isChanBag γs s (replica.sendArgP x.rr γ γc γm x.N) ∗
      swift.fld rp go!"cs" ↦□ csv ∗ ⌜swift.csCodes csv⌝ := by
  iintro H
  iunfold swift.runLoopCtx at H
  icases H with ⟨%s, %b, %γs, %sq, %hsl, %fr2, %pl, %sam, %csv, %n, -, #Fsnd, #Hsbag, -, -,
      -, -, -, -, -, -, -, -, -, -, -, -, -, #Fcs, %Hcs, -, -, -, -, -, -, -⟩
  iexists s, γs, csv
  iframe #
  ipureintro; exact Hcs

set_option maxRecDepth 4096 in
/-- **The `sync` arm** (see the file header). -/
theorem swift.runArm_sync (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX)
    (wp_hs : swift.Replica.handleSync.specIR (hG := hG) (fun _ => swift.descDS γ γc γm x rp)
      (swift.descEpS γ γc γm x rp) (fun b => swift.descDF (x.DR γ b)) (swift.stopPS x) γ γc γm x.γl x.γw x.γv x.γd x.γe x.γo
      x.syncN rp x.rr (swift.descPC γ γc γm x rp))
    (l : Loc) (m : sp.SyncWire) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
        swift.runInv rp γ γc γm x ∗
        swift.msgRepM (interface.mkOk (go.GoType.PointerType swift.MSync.ty) #l) (.sync m) ∗
        sp.msgOk γ γc γm (.sync m) }}
      (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"handleSync")) (Val #l))
    {{ RET #(); swift.runInv rp γ γc γm x }} := by
  iintro %Φ ⟨#Hpkg, Hinv, Hrep, #Hok⟩ HΦ
  ihave ⟨#Hctx, Hinv⟩ := BI.persistent_entails_right (swift.runInv_ctx rp γ γc γm x) $$ Hinv
  iunfold swift.runInv at Hinv
  icases Hinv with ⟨#Hd, #Hsc, Hrl, ⟨%ld, %v, %M0, %bs, %hd, %w, Hrun, Hpd, %Hn⟩, Hseq, Hdr, Hrf, Hds⟩
  ihave #Hd2 := Hd
  iunfold swift.descCtxE at Hd2
  icases Hd2 with ⟨%me, %fr, %lg, %dm, %dc, %ex, %dr, %oe, %γa, %γrm, %rc0, %γrc, #HR, #HisR,
    %Hids, -, -, -, #Hspi, #Hcfgx, #HnI, -, -, -, -, -, -, -, -, -, -, -⟩
  -- the message and its witness
  iunfold sp.msgOk at Hok
  icases Hok with ⟨%M, %N', %fr', %l', #HsI, ⟨#Hcfg', #HlbL0⟩, %Hw⟩
  obtain ⟨-, hwok, hlead⟩ := Hw
  -- round 54 (D74 (2), 53-4): the sender is the ballot's leader (`msgOk (.sync)`), with its `locLb`
  ihave %Hag := sp.cfg_agree (γc := γc) (γm := γm) x.N N' fr fr' lg l' $$ [Hcfgx Hcfg']
  · isplitl []
    · iexact Hcfgx
    · iexact Hcfg'
  obtain ⟨hNN, -, -⟩ := Hag
  subst hNN
  ihave #HlbL : sp.locLb γ (sp.leaderOf x.N (sp.bal m.bal)) (sp.bal m.bal) (sp.syncSeq M) $$ []
  · rw [← hlead]; iexact HlbL0
  iapply fupd_wp
  imod sp.syncIs_facts ⊤ (fun _ _ => CoPset.mem_full) (sp.bal m.bal) M $$ [Hspi HsI] with %HMf
  · iframe Hspi HsI
  obtain ⟨hb0, hnd⟩ := HMf
  imod sp.syncIs_len ⊤ (fun _ _ => CoPset.mem_full) (sp.bal m.bal) M hnd $$ [Hspi HsI] with %Hlen
  · iframe Hspi HsI
  have hwf : sp.KitVal.wf (.msync m) := by
    obtain ⟨⟨ps, hp, hpp⟩, ⟨cs, hc, hcp⟩, ⟨ds, hd', hdp⟩⟩ := hwok
    simp only [sp.KitVal.wf, hp, hc, hd', Option.map_some, Option.getD_some]
    refine ⟨?_, ?_, ?_⟩
    · have h := hpp.map Prod.fst
      rw [List.map_map] at h
      exact h.nodup_iff.2 (by simpa [Function.comp_def] using hnd)
    · have h := hcp.map Prod.fst
      rw [List.map_map] at h
      exact h.nodup_iff.2 (by simpa [Function.comp_def] using hnd)
    · have h := hdp.map Prod.fst
      rw [List.map_map] at h
      exact h.nodup_iff.2 (by simpa [Function.comp_def] using hnd)
  iunfold swift.msgRepM at Hrep
  icases Hrep with ⟨%l1, %xv, %Hx, Hso⟩
  obtain ⟨hl1, hxv⟩ := Hx
  have hl : l1 = l := go.IntoValInj.intoVal_inj (V := Loc)
    (by simpa [interface_mkOk_inj] using hl1.symm)
  subst hl
  rw [hxv hwf]
  imod swift.syncMaps_of_wire l1 m M hwok hnd $$ Hso with #HMaps
  imodintro
  ihave ⟨%Hlok, Hrun⟩ := BI.persistent_entails_right
    (swift.runSt_localOk γ x.γv rp x.N x.r ld v M0 bs hd w) $$ Hrun
  by_cases hb : sp.bal m.bal ≤ w.1
  · -- an equal or older ballot: `handleSync` returns at once
    ihave #HM2 := HMaps
    iunfold swift.syncMaps at HM2
    icases HM2 with ⟨%rep, %bl, %ph, %cm, %dp, %phM, %cmM, %dpM, #Hls, -, -, -, %HMf2, -⟩
    iunfold swift.runSt at Hrun
    icases Hrun with ⟨Hbal, Hcb, Hstat, Hhd, Hhdl, Hhdc, Hpr, Hprs, Hk, Hks, Hhl, Hhls, Hpe,
      Hpes, Hls0, Hlso, Hw, #Hlb, %Hok2⟩
    ihave #Hls2 := Hls
    iStructNamedPrefix Hls2 "MS"
    obtain ⟨hvb0, hvc0, hw1, hw2, hst, hnc, -⟩ := Hlok
    have hbl := HMf2.1
    wp_method_call
    wp_auto
    try ipersist r
    try ipersist msg
    wp_if_destruct
    · ihave HI : swift.runInv rp γ γc γm x $$ [Hbal Hcb Hstat Hhd Hhdl Hhdc Hpr Hprs Hk Hks Hhl Hhls
          Hpe Hpes Hls0 Hlso Hw Hrl Hseq Hdr Hrf Hpd Hds]
      · iunfold swift.runInv
        iframe Hd Hsc Hrl Hseq Hdr Hrf Hds
        iexists ld, v, M0, bs, hd, w
        isplitr [Hpd]
        · iunfold swift.runSt
          iframe
          iframe Hlb
          ipureintro; exact Hok2
        iframe Hpd
        ipureintro; exact Hn
      try wp_auto
      iapply HΦ; iexact HI
    try wp_auto
    wp_if_destruct
    · wp_if_destruct
      · ihave HI : swift.runInv rp γ γc γm x $$ [Hbal Hcb Hstat Hhd Hhdl Hhdc Hpr Hprs Hk Hks Hhl Hhls
            Hpe Hpes Hls0 Hlso Hw Hrl Hseq Hdr Hrf Hpd Hds]
        · iunfold swift.runInv
          iframe Hd Hsc Hrl Hseq Hdr Hrf Hds
          iexists ld, v, M0, bs, hd, w
          isplitr [Hpd]
          · iunfold swift.runSt
            iframe
            iframe Hlb
            ipureintro; exact Hok2
          iframe Hpd
          ipureintro; exact Hn
        try wp_auto
        iapply HΦ; iexact HI
      · exfalso
        exact Hif (by rw [hst.1 Hn]; rfl)
    · exfalso
      have h1 : ¬ bl.toInt < v.ballot.toInt := ‹¬ sint.Z bl < sint.Z v.ballot›
      have h2 : v.ballot.toInt ≠ bl.toInt := fun h => Hif (BitVec.eq_of_toInt_eq h)
      have h4 : sp.bal bl ≤ sp.bal v.ballot := by rw [hbl, ← hw1]; exact hb
      have h5 : (0 : Int) ≤ v.ballot.toInt := hvb0
      unfold sp.bal at h4
      omega
  · -- a later ballot: `specIR`
    have hlt : w.1 < sp.bal m.bal := by omega
    have hw21 : w.2.1 = w.1 := Hlok.2.2.2.2.2.1 Hn
    have hloc : w.locAt (sp.bal m.bal) = [] :=
      swift.LView.locAt_nil_of_rows (fun o => Hlok.2.2.2.2.2.2.2.2.2.1 _ o (by omega))
    iunfold swift.runFields at Hrf
    icases Hrf with ⟨%t, %fq, %rc, %nl, %bsN, %ppsl, %pp, Ft, FFQ, Frc, Fnl, Fbs, Hnl, FPP, Hpp,
      %Hpp, %Hnlr⟩
    iunfold swift.propDepsOwn at Hpd
    icases Hpd with ⟨%pdm, %PD, Fpd, Hpdm, -⟩
    ihave Hst := swift.runSt_runStS γ x.γv rp x.N x.r ld v M0 bs hd w (sp.bal m.bal) $$ Hrun
    ihave ⟨⟨%s, %γs, %csv, #Fsnd, #Hsbag, #Fcs, %Hcs⟩, Hrl⟩ :=
      BI.persistent_entails_right (swift.runLoopCtx_send rp γ γc γm x) $$ Hrl
    -- round 47 (45-b, D61 (1)): `handleSync.specIR`'s `PC`, the descriptors' contexts
    ihave ⟨#HPCw, Hrl⟩ := BI.persistent_entails_right (swift.descPC_of rp γ γc γm x x.N x.r) $$ Hrl
    ihave #HPC := HPCw $$ Hsc [Hd]
    · unfold swift.DC.ctx; iexact Hd
    ihave #Hsc2 := Hsc
    iunfold swift.syncCtx at Hsc2
    icases Hsc2 with ⟨%dm2, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      ⟨%sqS, %szS, %memS, #FSQ, #HSQq⟩, -⟩
    ihave #Hssc : swift.syncSendCtx γ γc γm rp x.N $$ []
    · iunfold swift.syncSendCtx
      iexists me
      isplitr
      · iunfold swift.sendCtxN
        iexists x.rr, s, x.γw, γs, csv
        iframe #
        ipureintro; exact Hcs
      iexists sqS, szS, memS
      iframe #
    have e : x.syncN.γdl = x.γdl := rfl
    have esn : x.syncN.sn x.N x.r = x.sn := rfl  -- round 32 (sv-swb, framing)
    wp_apply (wp_hs l1 x.N x.r x.k ld v M0 bs hd w (sp.bal m.bal) M)
      $$ [Hdr Hst Hds Ft Frc FFQ Fpd Hpdm]
    · simp only [Hn, ↓reduceIte, e, esn]
      iframe #
      iframe Hdr Hst Hds
      isplitl [Ft Frc FFQ Fpd Hpdm]
      · iunfold swift.syncFieldsOwn
        iexists t, rc, fq, pdm, PD
        iframe
      isplitr
      · ileft; ipureintro; exact hloc
      ipureintro
      exact ⟨by omega, by omega, by omega, fun h => by cases h⟩
    rw [e]
    iintro ⟨Hdr, Hpost⟩
    icases Hpost with (⟨%Hc, -, -, -⟩ | ⟨%v', %w', Hrun', Hds', Hsf, %Hw'⟩)
    · exfalso; omega
    iapply HΦ
    iunfold swift.syncFieldsOwnE at Hsf
    icases Hsf with ⟨%t', %rc', %fq', %pd', Ft, Fpd, Hpdm, Frc, FFQ⟩
    iunfold swift.descEpS at Hds'
    icases Hds' with ⟨Hds', -⟩
    iunfold swift.runInv
    iframe Hd Hsc Hrl Hseq Hdr Hds'
    isplitl [Hrun' Fpd Hpdm]
    · iexists _, v', (some M), (sp.syncSeq M), [], w'
      iframe Hrun'
      -- round 38 (Round 33 request 1, plan R9.1 (8)): `proposeDeps` is a fresh empty map
      isplitl [Fpd Hpdm]
      · iapply swift.propDepsOwn_empty rp pd'; iframe
      ipureintro; exact Hw'.2.2
    iunfold swift.runFields
    iexists t', fq', rc', nl, bsN, ppsl, pp
    iframe
    isplitr
    · ipureintro; exact Hpp
    ipureintro; exact Hnlr

end arm

end Perennial.github_com.imdea_software.swiftpaxos

end
