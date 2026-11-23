/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/MarshalSync.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`(*MSync).Marshal` (swift/defs.go: `gob.NewEncoder(w).Encode(m)`), the hypothesis
`swift.MSync.marshalHG` (Proof/swift/SyncFits.lean) of `handleNewLeaderAckNs`: proved,
`swift.MSync.marshal_proofG`, over the real `encoding/gob`'s specs (`NewEncoder.spec`,
`Encoder.EncodeW.spec`; format `sp.GobFmt`).

The message is chosen at the write (`marshalOkP`): the encoder iterates Go's maps in the run
time's order, so it writes a gob stream `bs` of a listing `m'` of the maps (`GobFmt.bytes m' bs`),
a reordering of `M`'s (`syncWireOk_equiv`, MsgRep.lean). gob's size limit cannot be hit: every
reordering has the size measure of `M`'s listing (`cEnc_length_equiv`), which `syncFits` bounds
(`GobFmt.fits_of`). The sink is `marshalOkP`'s (`wire.sinkOkE`: dead after a failed `Write`).

**Port change.** The lab's gob model wrote one frame of the kit codec's bytes (`gobFrame`); the
lab's rounds 14-18 (C17, C18) are superseded where they were about that frame.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.NewLeaderAckNs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.Codec
public import Dsverify.Spec.encoding.gob.NewEncoder
public import Dsverify.Spec.encoding.gob.Encoder__EncodeW

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace sp

theorem cMapOpt_length {A : Type} (f : A → List w8) {o o' : Option (List A)}
    (hr : Option.Rel List.Perm o o') : (cMapOpt f o).length = (cMapOpt f o').length := by
  cases hr with
  | none => rfl
  | some h =>
    simp only [cMapOpt, cList, List.length_cons, List.length_append, h.length_eq,
      ((h.map f).flatten).length_eq]

/-- The size measure is the same for the encoder's reorderings. -/
theorem cEnc_length_equiv {m m' : SyncWire} (he : KitVal.equiv (.msync m) (.msync m')) :
    m.cEnc.length = m'.cEnc.length := by
  obtain ⟨hr, hb, h1, h2, h3⟩ := he
  simp only [SyncWire.cEnc, List.length_append]
  rw [hr, hb, cMapOpt_length _ h1, cMapOpt_length _ h2, cMapOpt_length _ h3]

end sp

/-! ## The codec's view of a sent `MSync` (pure) -/

section pure
variable [go_gctx : GoGlobalContext]

theorem swift.nodup_of_map {α β : Type} (f : α → β) {l : List α} (h : (l.map f).Nodup) :
    l.Nodup :=
  List.Pairwise.of_map f (fun _ _ hne e => hne (congrArg f e)) h

theorem swift.lookupL_some_iff {V : Type} (ps : List (swift.CommandId × V))
    (hnd : (ps.map Prod.fst).Nodup) (k : swift.CommandId) (v : V) :
    map.lookupL k ps = some v ↔ (k, v) ∈ ps := by
  induction ps with
  | nil => simp [map.lookupL]
  | cons p ps ih =>
    obtain ⟨pk, pv⟩ := p
    simp only [List.map_cons, List.nodup_cons] at hnd
    by_cases h : k = pk
    · subst h
      simp only [map.lookupL, ↓reduceIte, Option.some.injEq, List.mem_cons, Prod.mk.injEq,
        true_and]
      constructor
      · intro e; left; exact e.symm
      · rintro (e | hm)
        · exact e.symm
        · exact absurd (List.mem_map.2 ⟨_, hm, rfl⟩) hnd.1
    · simp only [map.lookupL, h, ↓reduceIte, List.mem_cons, Prod.mk.injEq, false_and, false_or]
      exact ih hnd.2

theorem swift.toCmdId_injM : Function.Injective toCmdId := by
  intro a b h
  have := congrArg ofCmdId h
  simpa using this

/-- A listing of a Go map's entries `ps` (distinct keys), whose keys are `M`'s, each mapped to
`M`'s data by `g`, is a permutation of `M`. -/
theorem swift.listing_perm {V B : Type} (M : List (sp.CmdId × B)) (hM : (M.map Prod.fst).Nodup)
    (ps : List (swift.CommandId × V)) (hnd : (ps.map Prod.fst).Nodup)
    (hdom : ∀ x, (∃ v, (x, v) ∈ ps) ↔ toCmdId x ∈ M.map Prod.fst)
    (g : swift.CommandId × V → B) (hg : ∀ q ∈ ps, ∀ p ∈ M, p.1 = toCmdId q.1 → g q = p.2) :
    (ps.map (fun q => (goCmdId q.1, g q))).Perm M := by
  have hnd1 : (ps.map (fun q => (goCmdId q.1, g q))).Nodup := by
    apply swift.nodup_of_map Prod.fst
    rw [List.map_map]
    have : (Prod.fst ∘ fun q : swift.CommandId × V => (goCmdId q.1, g q)) =
        toCmdId ∘ Prod.fst := rfl
    rw [this, ← List.map_map]
    exact List.Pairwise.map toCmdId (fun _ _ h e => h (swift.toCmdId_injM e)) hnd
  have hnd2 : M.Nodup := swift.nodup_of_map Prod.fst hM
  apply (List.perm_ext_iff_of_nodup hnd1 hnd2).2
  intro a
  constructor
  · intro ha
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ha
    obtain ⟨p, hp, hpe⟩ := List.mem_map.1 ((hdom q.1).1 ⟨q.2, hq⟩)
    rw [hg q hq p hp hpe]
    have : (goCmdId q.1, p.2) = p := by
      rw [show goCmdId q.1 = toCmdId q.1 from rfl, ← hpe]
    rw [this]; exact hp
  · intro ha
    obtain ⟨v, hv⟩ := (hdom (ofCmdId a.1)).2 (by
      rw [toCmdId_ofCmdId]; exact List.mem_map.2 ⟨a, ha, rfl⟩)
    apply List.mem_map.2
    refine ⟨(ofCmdId a.1, v), hv, ?_⟩
    rw [hg _ hv a ha (by simp)]
    rfl

/-- `M`'s entry of `a` (none if absent). -/
def swift.syncLook (M : sp.SyncMsg) (a : sp.CmdId) : Option (sp.Cmd × List sp.CmdId) :=
  (M.find? (fun p => p.1 = a)).map Prod.snd

theorem swift.syncLook_of_mem (M : sp.SyncMsg) (hM : (M.map Prod.fst).Nodup)
    (p : sp.CmdId × sp.Cmd × List sp.CmdId) (hp : p ∈ M) : swift.syncLook M p.1 = some p.2 := by
  unfold swift.syncLook
  induction M with
  | nil => cases hp
  | cons q M ih =>
    simp only [List.map_cons, List.nodup_cons] at hM
    rcases List.mem_cons.1 hp with e | hp'
    · subst e; simp
    · have hne : q.1 ≠ p.1 := fun e => hM.1 (e ▸ List.mem_map.2 ⟨p, hp', rfl⟩)
      simp only [List.find?_cons, decide_eq_true_eq, hne, ↓reduceIte]
      exact ih hM.2 hp'

end pure

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [examples.swiftnet.Assumptions] [net.Assumptions] [net.FieldAssumptions]
  [net.rpc.Assumptions] [net.rpc.RpcKit]

/-- A Go map's listing as the codec sees it (`mapOwn`), from its read-only points-to. -/
theorem swift.mapOwn_intro {V A : Type} [ZeroVal V] (mp : Loc) (mv : val)
    (ps : List (swift.CommandId × V)) (g : swift.CommandId × V → A)
    (R : V → A → IProp netDistGF)
    (hmv : mv = map.mapV #(zero_val V) (ps.map map.toE)) (hnd : (ps.map Prod.fst).Nodup) :
    heapPointsto mp DFrac.discard mv ∗ □ (∀ q, ⌜q ∈ ps⌝ -∗ R q.2 (g q)) ⊢
      mapOwn mp DFrac.discard R (some (ps.map (fun q => (goCmdId q.1, g q)))) := by
  have key : iprop(□ (∀ q, ⌜q ∈ ps⌝ -∗ R q.2 (g q))) ⊢
      [∗list] i ↦ e ∈ ps.map (fun q => (goCmdId q.1, g q)),
        ∃ p : swift.CommandId × V, ⌜ps[i]? = some p⌝ ∗ R p.2 e.2 := by
    apply BigSepL.bigSepL_intro
    intro k x hx
    rw [List.getElem?_map] at hx
    cases hq : ps[k]? with
    | none => rw [hq] at hx; cases hx
    | some q =>
      rw [hq] at hx
      cases hx
      iintro #H
      iexists q
      isplitr
      · ipureintro; rfl
      iapply H
      ipureintro; exact List.mem_of_getElem? hq
  iintro ⟨Hh, #HR⟩
  unfold mapOwn
  iexists mv, ps
  iframe Hh
  isplitr
  · ipureintro
    refine ⟨hmv, hnd, ?_⟩
    simp [List.map_map, Function.comp_def]
  iapply key $$ HR

/-- **gob's view of a sent `MSync`**: `syncSent` gives the `MSync` (read-only) holding a wire
`MSync` listing `M` (`syncOwn`). -/
theorem swift.syncSent_syncOwn (ls : Loc) (me bl : w32) (M : sp.SyncMsg) :
    swift.syncSent ls me bl M ⊢ ∃ m0 : sp.SyncWire,
      encoding.gob.syncOwn (GF := netDistGF) ls DFrac.discard m0 ∗
      ⌜m0.rep = me ∧ m0.bal = bl ∧ sp.syncWireOk m0 M⌝ := by
  haveI := swift.hlog.cmdId_intoValInj (sem := sem)
  iintro #Hs
  unfold swift.syncSent
  icases Hs with ⟨-, %ph, %cm, %dp, %phM, %cmM, %dpM, #Hls, #Hph, #Hcm, #Hdp, %Hk, #Hents⟩
  obtain ⟨hPV, hMnd, hPH, hCD⟩ := Hk
  iunfold swift.syncEnts at Hents
  ihave %Hnn := typedPointsto_not_null $$ Hls
  rw [ownMap_unseal]
  unfold ownMapDef
  icases Hph with ⟨%mvP, %psP, #HhP, %HrP⟩
  icases Hcm with ⟨%mvC, %psC, #HhC, %HrC⟩
  icases Hdp with ⟨%mvD, %psD, #HhD, %HrD⟩
  obtain ⟨hmvP, hndP, -, hlkP⟩ := HrP
  obtain ⟨hmvC, hndC, -, hlkC⟩ := HrC
  obtain ⟨hmvD, hndD, -, hlkD⟩ := HrD
  -- membership in a listing is the map's lookup
  have memP : ∀ k v, (k, v) ∈ psP ↔ phM !! k = some v := fun k v => by
    rw [hlkP, swift.lookupL_some_iff psP hndP]
  have memC : ∀ k v, (k, v) ∈ psC ↔ cmM !! k = some v := fun k v => by
    rw [hlkC, swift.lookupL_some_iff psC hndC]
  have memD : ∀ k v, (k, v) ∈ psD ↔ dpM !! k = some v := fun k v => by
    rw [hlkD, swift.lookupL_some_iff psD hndD]
  have domP : ∀ x, (∃ v, (x, v) ∈ psP) ↔ toCmdId x ∈ M.map Prod.fst := fun x => by
    rw [← hPH x]
    constructor
    · rintro ⟨v, hv⟩; rw [(memP x v).1 hv]; rfl
    · intro h
      cases e : phM !! x with
      | none => rw [e] at h; cases h
      | some v => exact ⟨v, (memP x v).2 e⟩
  have domC : ∀ x, (∃ v, (x, v) ∈ psC) ↔ toCmdId x ∈ M.map Prod.fst := fun x => by
    rw [← hPH x, ← (hCD x).1]
    constructor
    · rintro ⟨v, hv⟩; rw [(memC x v).1 hv]; rfl
    · intro h
      cases e : cmM !! x with
      | none => rw [e] at h; cases h
      | some v => exact ⟨v, (memC x v).2 e⟩
  have domD : ∀ x, (∃ v, (x, v) ∈ psD) ↔ toCmdId x ∈ M.map Prod.fst := fun x => by
    rw [← hPH x, ← (hCD x).2]
    constructor
    · rintro ⟨v, hv⟩; rw [(memD x v).1 hv]; rfl
    · intro h
      cases e : dpM !! x with
      | none => rw [e] at h; cases h
      | some v => exact ⟨v, (memD x v).2 e⟩
  let gC : swift.CommandId × state.Command → sp.Cmd := fun q =>
    ((swift.syncLook M (toCmdId q.1)).map Prod.fst).getD default
  let gD : swift.CommandId × GoSlice → List sp.CmdId := fun q =>
    ((swift.syncLook M (toCmdId q.1)).map Prod.snd).getD []
  have hgC : ∀ q ∈ psC, ∀ p ∈ M, p.1 = toCmdId q.1 → gC q = p.2.1 := by
    intro q _ p hp he
    simp only [gC, ← he, swift.syncLook_of_mem M hMnd p hp, Option.map_some, Option.getD_some]
  have hgD : ∀ q ∈ psD, ∀ p ∈ M, p.1 = toCmdId q.1 → gD q = p.2.2 := by
    intro q _ p hp he
    simp only [gD, ← he, swift.syncLook_of_mem M hMnd p hp, Option.map_some, Option.getD_some]
  have hMnd' : ∀ (B : Type) (f : sp.CmdId × sp.Cmd × List sp.CmdId → B),
      ((M.map (fun p => (p.1, f p))).map Prod.fst).Nodup := by
    intro B f; rw [List.map_map]; exact hMnd
  have permP : (psP.map (fun q => (goCmdId q.1, q.2))).Perm
      (M.map (fun p => (p.1, sp.phCOMMIT))) := by
    apply swift.listing_perm _ (hMnd' _ _) psP hndP
    · intro x; rw [domP x, List.map_map]; rfl
    · intro q hq p hp _
      obtain ⟨p', -, rfl⟩ := List.mem_map.1 hp
      exact hPV q.1 q.2 ((memP q.1 q.2).1 hq)
  have permC : (psC.map (fun q => (goCmdId q.1, gC q))).Perm
      (M.map (fun p => (p.1, p.2.1))) := by
    apply swift.listing_perm _ (hMnd' _ _) psC hndC
    · intro x; rw [domC x, List.map_map]; rfl
    · intro q hq p hp he
      obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hp
      exact hgC q hq p' hp' he
  have permD : (psD.map (fun q => (goCmdId q.1, gD q))).Perm
      (M.map (fun p => (p.1, p.2.2))) := by
    apply swift.listing_perm _ (hMnd' _ _) psD hndD
    · intro x; rw [domD x, List.map_map]; rfl
    · intro q hq p hp he
      obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hp
      exact hgD q hq p' hp' he
  -- the entry of `M` behind a listed key
  have entC : ∀ q ∈ psC, ∃ p ∈ M, p.1 = toCmdId q.1 := fun q hq =>
    List.mem_map.1 ((domC q.1).1 ⟨q.2, hq⟩)
  have entD : ∀ q ∈ psD, ∃ p ∈ M, p.1 = toCmdId q.1 := fun q hq =>
    List.mem_map.1 ((domD q.1).1 ⟨q.2, hq⟩)
  iexists ⟨me, bl, some (psP.map (fun q => (goCmdId q.1, q.2))),
    some (psC.map (fun q => (goCmdId q.1, gC q))), some (psD.map (fun q => (goCmdId q.1, gD q)))⟩
  isplitl
  · unfold encoding.gob.syncOwn structOwn
    isplitr
    · ipureintro; rfl
    iexists ph, cm, dp
    iframe Hls
    isplitr
    · iapply swift.mapOwn_intro ph mvP psP (fun q => q.2) _ hmvP hndP
      iframe HhP
      imodintro
      iintro %q %_
      ipureintro; rfl
    isplitr
    · iapply swift.mapOwn_intro cm mvC psC gC _ hmvC hndC
      iframe HhC
      imodintro
      iintro %q %hq
      obtain ⟨p, hp, he⟩ := entC q hq
      icases BigSepL.bigSepL_mem (Φ := fun p => iprop(∃ (vs dsl : GoSlice),
          ⌜cmM !! ofCmdId p.1 = some (state.Command.mk p.2.1.op p.2.1.key vs) ∧
            dpM !! ofCmdId p.1 = some dsl⌝ ∗
          vs ↦*□ p.2.1.val ∗ dsl ↦*□ (p.2.2.map ofCmdId))) hp $$ Hents
        with ⟨%vs, %dsl, %Hl, #Hvs, -⟩
      have hq' : cmM !! q.1 = some q.2 := (memC q.1 q.2).1 hq
      rw [he, ofCmdId_toCmdId, hq'] at Hl
      obtain ⟨e1, -⟩ := Hl
      rw [hgC q hq p hp he]
      unfold cmdOwn
      rw [Option.some.inj e1]
      iframe Hvs
      ipureintro; exact ⟨rfl, rfl⟩
    · iapply swift.mapOwn_intro dp mvD psD gD _ hmvD hndD
      iframe HhD
      imodintro
      iintro %q %hq
      obtain ⟨p, hp, he⟩ := entD q hq
      icases BigSepL.bigSepL_mem (Φ := fun p => iprop(∃ (vs dsl : GoSlice),
          ⌜cmM !! ofCmdId p.1 = some (state.Command.mk p.2.1.op p.2.1.key vs) ∧
            dpM !! ofCmdId p.1 = some dsl⌝ ∗
          vs ↦*□ p.2.1.val ∗ dsl ↦*□ (p.2.2.map ofCmdId))) hp $$ Hents
        with ⟨%vs, %dsl, %Hl, -, #Hdsl⟩
      have hq' : dpM !! q.1 = some q.2 := (memD q.1 q.2).1 hq
      rw [he, ofCmdId_toCmdId, hq'] at Hl
      obtain ⟨-, e2⟩ := Hl
      cases e2
      rw [hgD q hq p hp he]
      iexists p.2.2.map ofCmdId
      iframe Hdsl
      ipureintro
      rw [List.map_map]
      exact List.map_id'' (fun _ => rfl) _
  · ipureintro
    exact ⟨rfl, rfl, ⟨_, rfl, permP⟩, ⟨_, rfl, permC⟩, ⟨_, rfl, permD⟩⟩

/-- **`swift.MSync.marshalHG`** (SyncFits.lean; `handleNewLeaderAckNs`'s hypothesis), over the
real gob's `NewEncoder` and `Encode` (see the file header). -/
theorem swift.MSync.marshal_proofG
    (wp_NewEnc : encoding.gob.NewEncoder.spec (GF := netDistGF))
    (wp_EncW : encoding.gob.Encoder.EncodeW.spec (GF := netDistGF)) :
    swift.MSync.marshalHG (hG := hG) := by
  intro ls me bl M
  iintro ⟨#Hgob, #Hss, %Hfits⟩
  unfold sp.marshalOkP
  iexists ⟨go.GoType.PointerType swift.MSync.ty, #ls⟩
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %wr %S %Q %W %Φ - #Hsink HS #Hpc #HQ HΦ
  ihave ⟨%m0, Hown, %Hm0⟩ := swift.syncSent_syncOwn ls me bl M $$ Hss
  obtain ⟨hrep, hbal, hok⟩ := Hm0
  -- `m0` is a reordering of `M`'s listing, and so is every reordering of it: they fit
  have h0 : sp.KitVal.equiv (.msync (swift.syncWireOf me bl M)) (.msync m0) := by
    obtain ⟨⟨ps, hp, hpp⟩, ⟨cs, hc, hcp⟩, ⟨ds, hd, hdp⟩⟩ := hok
    refine ⟨hrep.symm, hbal.symm, ?_, ?_, ?_⟩
    · rw [hp]; exact Option.Rel.some hpp.symm
    · rw [hc]; exact Option.Rel.some hcp.symm
    · rw [hd]; exact Option.Rel.some hdp.symm
  have hfit : ∀ m', sp.KitVal.equiv (.msync m0) (.msync m') → sp.GobFmt.fits m' := by
    intro m' he
    apply sp.GobFmt.fits_of
    rw [← sp.cEnc_length_equiv he, ← sp.cEnc_length_equiv h0]
    exact Hfits
  wp_method_call
  wp_call
  iunfold wire.sinkOkE at Hsink
  icases Hsink with ⟨%e, %He, #Hw⟩
  subst He
  wp_auto
  wp_apply wp_NewEnc (interface.ok e) as %enc Henc
  try wp_auto
  wp_apply wp_EncW enc e S Q W ls DFrac.discard m0 hfit $$ [Henc HS Hown]
    as %err ⟨%m', %bs, ⟨%Heq, %Hb⟩, Hown, HS⟩
  · iframe Hw Hpc Henc HS Hown
    imodintro
    iintro %m' %bs ⟨%Heq, %Hb⟩
    have hc : swift.syncCands me bl M (.sync m' bs) :=
      ⟨m', bs, rfl, Heq.1 ▸ hrep, Heq.2.1 ▸ hbal, sp.syncWireOk_equiv hok Heq, Hb⟩
    rw [show bs = (sp.Msg.sync m' bs).body from rfl]
    iapply HQ $$ %(.sync m' bs) %hc
  have hc : swift.syncCands me bl M (.sync m' bs) :=
    ⟨m', bs, rfl, Heq.1 ▸ hrep, Heq.2.1 ▸ hbal, sp.syncWireOk_equiv hok Heq, Hb⟩
  try wp_auto
  iapply HΦ $$ %(.sync m' bs) %hc []
  · itrivial
  iExactEq HS
  rfl

end proof

end Perennial.github_com.imdea_software.swiftpaxos
