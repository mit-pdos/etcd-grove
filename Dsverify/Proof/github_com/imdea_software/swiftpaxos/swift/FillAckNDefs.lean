/-
The definitions, specs and lemmas of `FillAckN.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.NewLeaderReqs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.FillOrder
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecSync
public import Dsverify.Proof.github_com.orcaman.concurrent_map.IterCbNDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.FillFacts
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.GhostSteps2

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions]

/-- **The report so far** (see the file header): the entries `E` (in append order) in the four
local slices `cmdIds`, `phases`, `cmds`, `deps` (at `ci ph cm dp`), each with its objects and
its witness; `seen` (at `sn`) holds exactly the ids of `E`'s first `ns` entries (the
pending proposals, the last collection, are not added to it). -/
def swift.fillAcc (γ : sp.Names) (N r c : Nat) (ci ph cm dp sn : Loc) (E : List sp.RepEntry)
    (ns : Nat) : IProp netDistGF :=
  iprop(∃ (s1 s2 s3 s4 : GoSlice) (cmL : List state.Command) (dpL : List swift.SDep) (sm : Loc)
      (sM : GMap swift.CommandId Unit),
    ci ↦ s1 ∗ s1 ↦* (E.map (fun e => ofCmdId e.id)) ∗ ownSliceCap swift.CommandId s1 (DFrac.own 1) ∗
    ph ↦ s2 ∗ s2 ↦* (E.map (·.phase)) ∗ ownSliceCap w64 s2 (DFrac.own 1) ∗
    cm ↦ s3 ∗ s3 ↦* cmL ∗ ownSliceCap state.Command s3 (DFrac.own 1) ∗
    dp ↦ s4 ∗ s4 ↦* dpL ∗ ownSliceCap swift.SDep s4 (DFrac.own 1) ∗
    sn ↦ sm ∗ sm ↦$ sM ∗
    ⌜cmL.length = E.length ∧ dpL.length = E.length ∧ (E.map (·.id)).Nodup ∧ ns ≤ E.length ∧
      ∀ y, (sM !! y).isSome = true ↔ toCmdId y ∈ (E.take ns).map (·.id)⌝ ∗
    [∗list] i ↦ e ∈ E, ∃ (cv : state.Command) (sd : swift.SDep),
      ⌜cmL[i]? = some cv ∧ dpL[i]? = some sd⌝ ∗ swift.repEntryObj cv sd e ∗ swift.repEntW γ N r c e)

/-- Where a report entry of the first three collections comes from (`fillNewLeaderAckN`): the
execution log's `XS`, the stopped descriptors' `S` (N1-R1), or the last `MSync` `M0` (in
`COMMIT`, with its command and dependencies). Round N6: the pending proposals' entries (in
`START`) are `swift.startOk`'s (FillFacts.lean), kept apart. -/
def swift.fillSrc (XS S : List sp.RepEntry) (M0 : Option sp.SyncMsg)
    (_pM : GMap swift.CommandId Loc) (e : sp.RepEntry) : Prop :=
  e ∈ XS ∨ e ∈ S ∨ (∃ M, M0 = some M ∧ e.phase = swift.phCOMMIT ∧ (e.id, e.cmd, e.dep) ∈ M)

theorem swift.fillSrc_mono (XS S S' : List sp.RepEntry) (M0 : Option sp.SyncMsg)
    (pM : GMap swift.CommandId Loc) (e : sp.RepEntry) (h : ∀ e ∈ S, e ∈ S') :
    swift.fillSrc XS S M0 pM e → swift.fillSrc XS S' M0 pM e := by
  rintro (h1 | h1 | h1)
  · exact Or.inl h1
  · exact Or.inr (Or.inl (h _ h1))
  · exact Or.inr (Or.inr h1)

theorem swift.fillLt_swo (H ids : List swift.CommandId) :
    slices.StrictWeakOrder (swift.FillLt H ids) where
  strict_weak_order_irrefl _ := by unfold swift.FillLt; omega
  strict_weak_order_trans _ _ _ h1 h2 := by unfold swift.FillLt at *; omega
  strict_weak_order_equiv := by
    refine ⟨fun x => ?_, fun h => ⟨h.2, h.1⟩, fun {x y z} h1 h2 => ?_⟩
    · unfold swift.FillLt; omega
    · unfold swift.FillLt at *; omega

end defs

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions]

/-- One more entry `e` in the report: the four slices appended, `seen` as given. -/
theorem swift.fillAcc_snoc (γ : sp.Names) (N r c : Nat) (ci ph cm dp sn : Loc)
    (E : List sp.RepEntry) (e : sp.RepEntry) (ns : Nat) (s1 s2 s3 s4 : GoSlice)
    (cmL : List state.Command) (dpL : List swift.SDep) (cv : state.Command) (sd : swift.SDep)
    (sm : Loc) (sM : GMap swift.CommandId Unit)
    (hlen : cmL.length = E.length ∧ dpL.length = E.length)
    (hnd : ((E ++ [e]).map (·.id)).Nodup) (hns : ns ≤ E.length + 1)
    (hseen : ∀ y, (sM !! y).isSome = true ↔ toCmdId y ∈ ((E ++ [e]).take ns).map (·.id)) :
    ci ↦ s1 ∗ s1 ↦* (E.map (fun e => ofCmdId e.id) ++ [ofCmdId e.id]) ∗
      ownSliceCap swift.CommandId s1 (DFrac.own 1) ∗
    ph ↦ s2 ∗ s2 ↦* (E.map (·.phase) ++ [e.phase]) ∗ ownSliceCap w64 s2 (DFrac.own 1) ∗
    cm ↦ s3 ∗ s3 ↦* (cmL ++ [cv]) ∗ ownSliceCap state.Command s3 (DFrac.own 1) ∗
    dp ↦ s4 ∗ s4 ↦* (dpL ++ [sd]) ∗ ownSliceCap swift.SDep s4 (DFrac.own 1) ∗
    sn ↦ sm ∗ sm ↦$ sM ∗
    ([∗list] i ↦ e' ∈ E, ∃ (cv' : state.Command) (sd' : swift.SDep),
      ⌜cmL[i]? = some cv' ∧ dpL[i]? = some sd'⌝ ∗ swift.repEntryObj cv' sd' e' ∗
        swift.repEntW γ N r c e') ∗
    swift.repEntryObj cv sd e ∗ swift.repEntW γ N r c e ⊢
    swift.fillAcc γ N r c ci ph cm dp sn (E ++ [e]) ns := by
  iintro ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, HB, Ho, Hw⟩
  iunfold swift.fillAcc
  iexists s1, s2, s3, s4, cmL ++ [cv], dpL ++ [sd], sm, sM
  simp only [List.map_append, List.map_cons, List.map_nil]
  iframe H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14
  isplitr
  · ipureintro
    refine ⟨by simp [hlen.1], by simp [hlen.2], by simpa using hnd, by simpa using hns, hseen⟩
  iapply BigSepL.bigSepL_snoc.2
  isplitl [HB]
  · iapply (BigSepL.bigSepL_mono ?_) $$ HB
    intro k e' hk
    have hk' : k < E.length := (List.getElem?_eq_some_iff.mp hk).1
    iintro ⟨%cv', %sd', %Hk, Ho', Hw'⟩
    iexists cv', sd'
    iframe Ho' Hw'
    ipureintro
    exact ⟨by rw [List.getElem?_append_left (by omega)]; exact Hk.1,
      by rw [List.getElem?_append_left (by omega)]; exact Hk.2⟩
  · iexists cv, sd
    iframe Ho Hw
    ipureintro
    exact ⟨by rw [List.getElem?_append_right (by omega), hlen.1]; simp,
      by rw [List.getElem?_append_right (by omega), hlen.2]; simp⟩

/-- The first occurrence of `z` at `n`: its index is `n`. -/
theorem swift.idxOf_first {α : Type} [DecidableEq α] :
    ∀ (H : List α) (n : Nat) (z : α), H[n]? = some z → z ∉ H.take n → H.idxOf z = n
  | [], n, z, hz, _ => by simp at hz
  | a :: t, 0, z, hz, _ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hz
    subst hz; exact List.idxOf_cons_self
  | a :: t, n + 1, z, hz, hn => by
    simp only [List.getElem?_cons_succ] at hz
    simp only [List.take_succ_cons, List.mem_cons, not_or] at hn
    rw [List.idxOf_cons]
    have : (a == z) = false := by simpa using (Ne.symm hn.1)
    rw [this]
    simp only [Bool.false_eq_true, ↓reduceIte, cond_false]
    rw [swift.idxOf_first t n z hz hn.2]

/-- `idx[j] = j` on `0, …, j-1, 0, …`. -/
theorem swift.idx_set (n j : Nat) (hj : j < n) :
    ((List.range j).map (fun (k : Nat) => W64 (k : Int)) ++ List.replicate (n - j) (W64 0)).set j
        (W64 (j : Int)) =
      (List.range (j + 1)).map (fun (k : Nat) => W64 (k : Int)) ++ List.replicate (n - (j + 1)) (W64 0) := by
  obtain ⟨m, hm⟩ : ∃ m, n - j = m + 1 := ⟨n - j - 1, by omega⟩
  rw [hm, show n - (j + 1) = m by omega, List.replicate_succ]
  rw [List.set_append_right _ _ (by simp)]
  simp [List.range_succ]

/-- `m.Get(key)` with the view owned (`GetV`'s atomic update at the caller's `cmapView`). -/
theorem swift.wp_GetOwn
    (wp_GetV : github_com.orcaman.concurrent_map.ConcurrentMap.GetV.spec (GF := netDistGF))
    (m : GoSlice) (γm : GName) (R : GoString → GoInterface → IProp netDistGF) (key : GoString)
    (M : GMap GoString GoInterface) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.orcaman.concurrent_map ∗
        github_com.orcaman.concurrent_map.readerV m γm R ∗
        github_com.orcaman.concurrent_map.cmapView γm M }}
      (App (Val #(methods github_com.orcaman.concurrent_map.ConcurrentMap.ty go!"Get" #m))
        (Val #key))
    {{ (v : GoInterface) (ok : Bool), RET (PairV #v #ok);
        github_com.orcaman.concurrent_map.readerV m γm R ∗
        github_com.orcaman.concurrent_map.cmapView γm M ∗
        ⌜v = (M !! key).getD interface.nil ∧ ok = (M !! key).isSome⌝ }} := by
  iintro %Φ ⟨#Hpkg, Hr, Hv⟩ HΦ
  iapply (wp_GetV m γm R key) $$ [Hr] [Hv HΦ]
  · iframe Hpkg Hr
  · inext
    iapply github_com.orcaman.concurrent_map.cmapView_au γm M (fun M => M)
    iframe Hv
    iintro Hv %v %ok ⟨Hr, %Hok, -⟩
    iapply HΦ
    iframe
    ipureintro; exact Hok

/-- The report's entries' commands are registered (`repEntW`'s `cmdIs`; for
`sp.cmdIs_list_len`). -/
theorem swift.fillB_cmdIs (γ : sp.Names) (N r c : Nat) (E : List sp.RepEntry)
    (cmL : List state.Command) (dpL : List swift.SDep) :
    ([∗list] i ↦ e ∈ E, ∃ (cv : state.Command) (sd : swift.SDep),
      ⌜cmL[i]? = some cv ∧ dpL[i]? = some sd⌝ ∗ swift.repEntryObj cv sd e ∗
        swift.repEntW γ N r c e) ⊢
      ([∗list] i ↦ e ∈ E, ∃ (cv : state.Command) (sd : swift.SDep),
        ⌜cmL[i]? = some cv ∧ dpL[i]? = some sd⌝ ∗ swift.repEntryObj cv sd e ∗
          swift.repEntW γ N r c e) ∗
      □ ([∗list] y ∈ E.map (·.id), ∃ c', sp.cmdIs γ y c') := by
  haveI : Persistent (iprop([∗list] i ↦ e ∈ E, ∃ (cv : state.Command) (sd : swift.SDep),
      ⌜cmL[i]? = some cv ∧ dpL[i]? = some sd⌝ ∗ swift.repEntryObj cv sd e ∗
        swift.repEntW γ N r c e) : IProp netDistGF) :=
    BigSepL.bigSepL_persistent (fun _ _ _ => by infer_instance)
  iintro #H
  iframe H
  imodintro
  rw [BigSepL.bigSepL_map]
  iapply (BigSepL.bigSepL_mono ?_) $$ H
  intro k e _
  iintro ⟨%cv, %sd, -, -, Hw⟩
  iunfold swift.repEntW at Hw
  icases Hw with ⟨Hc, -⟩
  iexists e.cmd
  iexact Hc

/-- `filterMap` of a list whose elements all map to `some`: its length. -/
theorem swift.filterMap_len {α β : Type} (f : α → Option β) :
    ∀ xs : List α, (∀ a ∈ xs, (f a).isSome) → (xs.filterMap f).length = xs.length
  | [], _ => rfl
  | a :: t, h => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h a (List.mem_cons_self))
    rw [List.filterMap_cons, hb]
    simp only [List.length_cons]
    rw [swift.filterMap_len f t (fun a' ha' => h a' (List.mem_cons_of_mem _ ha'))]

/-- **The ack's entries along the sorted indices** (`ackObj`'s per-entry part, and the entries'
witnesses): the accumulated entries `E` read at the indices `xs`. -/
theorem swift.fill_ackEnts (γ : sp.Names) (N r c : Nat) (E : List sp.RepEntry)
    (cmL : List state.Command) (dpL : List swift.SDep) :
    ∀ xs : List w64, (∀ a ∈ xs, (sint.Z a).toNat < E.length) →
    ([∗list] i ↦ e ∈ E, ∃ (cv : state.Command) (sd : swift.SDep),
      ⌜cmL[i]? = some cv ∧ dpL[i]? = some sd⌝ ∗ swift.repEntryObj cv sd e ∗
        swift.repEntW γ N r c e) ⊢
      ([∗list] i ↦ e ∈ xs.filterMap (fun a => E[(sint.Z a).toNat]?),
        ∃ (cv : state.Command) (sd : swift.SDep),
        ⌜(xs.filterMap (fun a => cmL[(sint.Z a).toNat]?))[i]? = some cv ∧
          (xs.filterMap (fun a => dpL[(sint.Z a).toNat]?))[i]? = some sd⌝ ∗
        swift.repEntryObj cv sd e) ∗
      ([∗list] e ∈ xs.filterMap (fun a => E[(sint.Z a).toNat]?), swift.repEntW γ N r c e) := by
  haveI : Persistent (iprop([∗list] i ↦ e ∈ E, ∃ (cv : state.Command) (sd : swift.SDep),
      ⌜cmL[i]? = some cv ∧ dpL[i]? = some sd⌝ ∗ swift.repEntryObj cv sd e ∗
        swift.repEntW γ N r c e) : IProp netDistGF) :=
    BigSepL.bigSepL_persistent (fun _ _ _ => by infer_instance)
  intro xs
  induction xs with
  | nil =>
    intro _
    iintro -
    simp only [List.filterMap_nil]
    isplitl
    · iapply BigSepL.bigSepL_nil.2; iempintro
    · iapply BigSepL.bigSepL_nil.2; iempintro
  | cons a t ih =>
    intro hin
    have ha := hin a List.mem_cons_self
    obtain ⟨e, he⟩ : ∃ e, E[(sint.Z a).toNat]? = some e := ⟨_, List.getElem?_eq_getElem ha⟩
    iintro #H
    ihave #Ha := (BigSepL.bigSepL_lookup he) $$ H
    icases Ha with ⟨%cv, %sd, %hcs, #Ho, #Hw⟩
    ihave ⟨Ht1, Ht2⟩ := ih (fun a' ha' => hin a' (List.mem_cons_of_mem _ ha')) $$ H
    simp only [List.filterMap_cons, he, hcs.1, hcs.2]
    isplitl [Ht1]
    · iapply BigSepL.bigSepL_cons.2
      isplitr
      · iexists cv, sd; iframe Ho; ipureintro; exact ⟨rfl, rfl⟩
      · simp only [List.getElem?_cons_succ]; iexact Ht1
    · iapply BigSepL.bigSepL_cons.2
      iframe Hw Ht2

/-- `repEntW` of a list of entries as `sp.entryWit` at the node state (`swift.repEntW_entryWit`
for each). -/
theorem swift.repEntWs_entryWit (E : CoPset) (hE : ↑sp.spN ⊆ E) (γ : sp.Names) (γc γm γl : GName)
    (N : Nat) (fr : Bool) (l : List GoString) (r k c : Nat) (st : sp.RState)
    (hr : r < N) (hk : nodeOf l r = some k) :
    ∀ L : List sp.RepEntry,
    sp.inv γ γc γm γl ∗ sp.cfg γc γm N fr l ∗ sp.nodeSt γ k (1 : Iris.Qp).half st ∗
      ([∗list] e ∈ L, swift.repEntW γ N r c e) ⊢
      |={E}=> sp.nodeSt γ k (1 : Iris.Qp).half st ∗ [∗list] e ∈ L, sp.entryWit γ N r c st e := by
  intro L
  induction L with
  | nil =>
    iintro ⟨-, -, Hst, -⟩
    imodintro
    iframe Hst
    iapply BigSepL.bigSepL_nil.2; iempintro
  | cons e L ih =>
    iintro ⟨#Hinv, #Hcfg, Hst, Hws⟩
    icases BigSepL.bigSepL_cons.1 $$ Hws with ⟨Hw, Hws⟩
    imod swift.repEntW_entryWit E hE γ γc γm γl N fr l r k c st e hr hk $$ [Hst Hw]
      with ⟨Hst, Hew⟩
    · iframe Hinv Hcfg Hst Hw
    imod ih $$ [Hst Hws] with ⟨Hst, Hews⟩
    · iframe Hinv Hcfg Hst Hws
    imodintro
    iframe Hst
    iapply BigSepL.bigSepL_cons.2
    iframe

/-- A replica's pre-acceptances and commits are of its own sequences (`PInv`'s `pre_ok`,
`com_ok`, through an identity step of `node_step`; `upd_report`'s h4). -/
theorem sp.rows_loc {γ : sp.Names} {γc γm γl : GName} (E : CoPset) (hE : ↑sp.spN ⊆ E) (N : Nat)
    (fr : Bool) (l : List GoString) (r k : Nat) (st : sp.RState) (hr : r < N)
    (hk : nodeOf l r = some k) :
    sp.inv γ γc γm γl ∗ sp.cfg γc γm N fr l ∗ sp.nodeSt γ k (1 : Iris.Qp).half st ⊢
    |={E}=> sp.nodeSt γ k (1 : Iris.Qp).half st ∗
      ⌜(∀ b x, (st.preAt b x).isSome → x ∈ st.locAt b) ∧
        (∀ b x, (b, x) ∈ st.comR → x ∈ st.locAt b)⌝ := by
  iintro ⟨#Hinv, #Hcfg, Hst⟩
  imod sp.node_step E hE N fr l r k st none
    (fun s' => iprop(⌜s' = st ∧ (∀ b x, (st.preAt b x).isSome → x ∈ st.locAt b) ∧
      (∀ b x, (b, x) ∈ st.comR → x ∈ st.locAt b)⌝)) hr hk $$ [Hst]
    with ⟨%st', Hst, -, %Heq⟩
  · iframe Hinv Hcfg Hst
    isplitl []
    · iunfold sp.predPre; itrivial
    unfold sp.stepUpd
    iintro %S %mC %mL %mS %mA %mP %mCo %mR %mPa %HH HC HL HS HA HP HCo HRp HPa
    obtain ⟨HI, Hsr, Hrs, Hrepr⟩ := HH
    imodintro
    iexists S, mL, mS, mA, mP, mCo, mR, mPa
    iframe
    ipureintro
    refine ⟨⟨HI, Hsr, Hrepr, rfl, rfl, sp.PState.le_refl S, fun _ _ => rfl, rfl⟩, Hrs, ?_, ?_⟩
    · intro b x hx
      have hrow := HI.rows_ok r b
      rw [Hrs] at hrow
      obtain ⟨D, hD⟩ := Option.isSome_iff_exists.mp hx
      have := (HI.pre_ok r b x D (by rw [hrow.2.2.1 x]; exact hD)).2.2.1
      rw [hrow.1] at this; exact this
    · intro b x hx
      have hrow := HI.rows_ok r b
      rw [Hrs] at hrow
      have := (HI.com_ok r b x ((hrow.2.2.2.2.1 x).2 hx)).2.2.1
      rw [hrow.1] at this; exact this
  obtain ⟨rfl, h⟩ := Heq
  imodintro
  iframe Hst
  ipureintro; exact h

end lemmas

section reqs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

/-- The execution log's entries are at least `PRE_ACCEPT` (N1-R1 `exec`'s per-entry phase fact;
D76 (2)). -/
theorem swift.XS_phase (XS : List sp.RepEntry) (es : List swift.commandStaticDesc)
    (hlen : XS.length = es.length) :
    ([∗list] i ↦ esi ∈ es, ∃ (e : sp.RepEntry) (vs : GoSlice),
      ⌜XS[i]? = some e ∧ toCmdId esi.cmdId' = e.id ∧
        (if sint.Z esi.phase' < 1 then 1 else (sint.Z esi.phase').toNat) = e.phase.toNat ∧
        esi.cmd' = state.Command.mk e.cmd.op e.cmd.key vs⌝ ∗ vs ↦*□ e.cmd.val ∗
      ∃ D : List swift.CommandId, esi.dep' ↦*□ D ∗ ⌜D.map toCmdId = e.dep⌝) ⊢
      (⌜∀ e ∈ XS, e.phase.toNat ≠ 0⌝ : IProp netDistGF) := by
  refine (BigSepL.bigSepL_mono_of_forall (Ψ := fun i (_ : swift.commandStaticDesc) =>
    iprop(⌜∃ e : sp.RepEntry, XS[i]? = some e ∧ e.phase.toNat ≠ 0⌝)) (fun {i esi} => ?_)).trans
    (BigSepL.bigSepL_pure_intro.trans ?_)
  · iintro ⟨%e, %vs, %He, -⟩
    ipureintro
    refine ⟨e, He.1, ?_⟩
    rw [← He.2.2.1]
    split <;> omega
  iintro %H
  ipureintro
  intro e he
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
  obtain ⟨e', he', hph⟩ := H i es[i] (List.getElem?_eq_getElem (by omega))
  rw [List.getElem?_eq_getElem hi] at he'
  cases he'
  exact hph

/-- **A read's `proposeDep` facts, persistent** (I1, round 51's R1-c): `descReadOk`'s second
conjunct with its wand taken at the key's command, if the key has one (`str` is injective, so at
most one command has the key). -/
def swift.rdPd (str : swift.CommandId → GoString) (Wd : sp.CmdId → List sp.CmdId → IProp netDistGF)
    (r : swift.DescRead) : IProp netDistGF :=
  iprop(⌜r.pdsl = slice.nil⌝ ∨ ⌜∀ z : sp.CmdId, str (ofCmdId z) ≠ r.k⌝ ∨
    ∃ z : sp.CmdId, ⌜str (ofCmdId z) = r.k⌝ ∗ Wd z (r.PD.map toCmdId))

instance swift.rdPd_persistent (str : swift.CommandId → GoString)
    (Wd : sp.CmdId → List sp.CmdId → IProp netDistGF) [hW : ∀ z D, Persistent (Wd z D)]
    (r : swift.DescRead) : Persistent (swift.rdPd str Wd r) := by
  unfold swift.rdPd; infer_instance

/-- **A held read** (I1, round 51 (51-3)): the read's fields, kept from `IterCb` until after the
report (they pin the read values), the wand back to the descriptor, and its `proposeDep` facts.
Round 59 (D84 (2)): with the read's claim (`swift.rdCl`), which the wand takes back. -/
def swift.rdHeld (γ : sp.Names) (x : swift.RunX) (b : Nat) (Wd : sp.CmdId → List sp.CmdId → IProp netDistGF)
    (r : swift.DescRead) : IProp netDistGF :=
  iprop(⌜r.p ≠ null → x.str (ofCmdId r.y) = r.k⌝ ∗
    r.fields ∗ (swift.rdCl x.sn.γcl b r ∗
      (r.fields -∗ swift.rdCl x.sn.γcl b r -∗ swift.descFree (swift.descDF (x.DR γ b)) r.d)) ∗
    swift.rdPd x.str Wd r)

/-- The held reads' fields and claims (round 59), and the descriptors back from them. -/
theorem swift.rdHeld_fields (γ : sp.Names) (x : swift.RunX) (b : Nat)
    (Wd : sp.CmdId → List sp.CmdId → IProp netDistGF) (SR : List swift.DescRead) :
    ([∗list] r ∈ SR, swift.rdHeld γ x b Wd r) ⊢
      ([∗list] r ∈ SR, r.fields) ∗ ([∗list] r ∈ SR, swift.rdCl x.sn.γcl b r) ∗
        (([∗list] r ∈ SR, r.fields) -∗ ([∗list] r ∈ SR, swift.rdCl x.sn.γcl b r) -∗
        [∗list] r ∈ SR, swift.descFree (swift.descDF (x.DR γ b)) r.d) := by
  have hm : ([∗list] r ∈ SR, swift.rdHeld γ x b Wd r) ⊢ ([∗list] r ∈ SR, r.fields ∗
      (swift.rdCl x.sn.γcl b r ∗
        (r.fields ∗ swift.rdCl x.sn.γcl b r -∗ swift.descFree (swift.descDF (x.DR γ b)) r.d))) :=
    BigSepL.bigSepL_mono_of_forall (fun {_ r} => by
      iintro H
      iunfold swift.rdHeld at H
      icases H with ⟨-, Hf, ⟨Hc, Hb⟩, -⟩
      iframe Hf Hc
      iintro ⟨Hf, Hc⟩
      iapply Hb $$ Hf Hc)
  refine hm.trans ?_
  iintro H
  icases BigSepL.bigSepL_sep_eqv.1 $$ H with ⟨Hf, H⟩
  icases BigSepL.bigSepL_sep_eqv.1 $$ H with ⟨Hc, Hb⟩
  iframe Hf Hc
  iintro Hf Hc
  ihave Hfc := BigSepL.bigSepL_sep_eqv.2 $$ [Hf Hc]
  · iframe Hf Hc
  iapply (BigSepL.bigSepL_wand) $$ Hfc Hb

/-- A pure consequence of `P`, keeping `P` (round 56). -/
theorem swift.keep_pureF {P : IProp netDistGF} {φ : Prop} (h : P ⊢ ⌜φ⌝) : P ⊢ P ∗ ⌜φ⌝ :=
  (BI.and_intro .rfl h).trans BI.persistent_and_sep_mp

/-- The held reads' key facts (round 56: N1-R2's rest records). -/
theorem swift.rdHeld_keys (γ : sp.Names) (x : swift.RunX) (b : Nat)
    (Wd : sp.CmdId → List sp.CmdId → IProp netDistGF) (SR : List swift.DescRead) :
    ([∗list] r ∈ SR, swift.rdHeld γ x b Wd r) ⊢
      ⌜∀ r ∈ SR, r.p ≠ null → x.str (ofCmdId r.y) = r.k⌝ := by
  induction SR with
  | nil => iintro -; ipureintro; intro r hr; cases hr
  | cons r SR ih =>
    iintro H
    icases (BigSepL.bigSepL_cons (PROP := IProp netDistGF)).1 $$ H with ⟨Hr, H⟩
    iunfold swift.rdHeld at Hr
    icases Hr with ⟨%h, -⟩
    ihave %h2 := ih $$ H
    ipureintro
    intro r' hr'
    rcases List.mem_cons.mp hr' with rfl | hr'
    · exact h
    · exact h2 r' hr'

/-- The descriptors of the reads, as the stopped view's map (the reads cover the view's entries,
`IterCb`'s `vis`). -/
theorem swift.held_map (Mc : GMap GoString GoInterface) (SR : List swift.DescRead)
    (Φ : Loc → IProp netDistGF)
    (hp : (SR.map (fun r => (r.k,
      interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #r.d))).Perm Mc.toList) :
    ([∗list] r ∈ SR, Φ r.d) ⊢ [∗map] k ↦ vv ∈ Mc, ∃ d : Loc,
      ⌜vv = interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d⌝ ∗ Φ d := by
  have hm : ([∗list] r ∈ SR, Φ r.d) ⊢ ([∗list] r ∈ SR, ∃ d : Loc,
      ⌜interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #r.d =
        interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d⌝ ∗ Φ d) :=
    BigSepL.bigSepL_mono_of_forall (fun {_ r} => by
      iintro H
      iexists r.d
      iframe H
      ipureintro; rfl)
  refine hm.trans ?_
  refine (BigSepL.bigSepL_map (fun r : swift.DescRead => (r.k,
    interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #r.d))
    (Φ := fun _ kv => iprop(∃ d : Loc,
      ⌜kv.2 = interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d⌝ ∗ Φ d))) ▸ ?_
  exact (BigSepL.bigSepL_perm hp).1.trans (BigSepM.bigSepM_toList (m := Mc) (Φ := fun (_ : GoString) vv =>
    iprop(∃ d : Loc, ⌜vv = interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d⌝ ∗
      Φ d))).2

/-- `IterCb`'s entries, none visited. -/
theorem swift.visMap_init (Mc : GMap GoString GoInterface)
    (Φ : GoString → GoInterface → IProp netDistGF) :
    ([∗map] k ↦ vv ∈ Mc, Φ k vv) ⊢
      [∗map] k ↦ vv ∈ Mc, ⌜k ∈ ([] : List (GoString × GoInterface)).map Prod.fst⌝ ∨ Φ k vv :=
  BigSepM.bigSepM_mono_of_forall (fun {_ _} => by iintro H; iright; iexact H)

/-- A held read's `proposeDep` facts at the key's command. -/
theorem swift.rdPd_wd (str : swift.CommandId → GoString)
    (Wd : sp.CmdId → List sp.CmdId → IProp netDistGF) (r : swift.DescRead) (key : swift.CommandId)
    (hinj : Function.Injective str) (hkz : str (ofCmdId (toCmdId key)) = r.k) :
    swift.rdPd str Wd r ⊢ ⌜r.pdsl = slice.nil⌝ ∨ Wd (toCmdId key) (r.PD.map toCmdId) := by
  iintro H
  iunfold swift.rdPd at H
  icases H with (%Hnil | %Hnz | ⟨%z, %hz, HW⟩)
  · ileft; ipureintro; exact Hnil
  · exact absurd hkz (Hnz _)
  · have hzk : z = toCmdId key := by
      have h := hinj (hz.trans hkz.symm)
      have h2 := congrArg toCmdId h
      first | simpa using h2 | exact h2
    subst hzk
    iright; iexact HW

/-- A held read's `proposeDep` against the run loop's sequence (N1-R1 `Wd_seq`, round 54). -/
theorem swift.rdPd_seq (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX)
    (R1 : swift.N1R1 (hG := hG) rp γ γc γm x) (c : Nat) (key : swift.CommandId)
    (r : swift.DescRead) (s : sp.Seq) (hinj : Function.Injective x.str)
    (hkz : x.str (ofCmdId (toCmdId key)) = r.k) :
    swift.descCtxX γ γc γm x rp ∗ swift.rdPd x.str (R1.Wd c) r ∗ sp.locLb γ x.r c s ⊢
      |={⊤}=> ⌜r.pdsl ≠ slice.nil → toCmdId key ∈ s.map Prod.fst →
        (∀ d ∈ r.PD.map toCmdId, d ∈ sp.depsIn s (toCmdId key)) ∧
          (r.PD.map toCmdId).length < 2 ^ 62⌝ := by
  iintro ⟨#Hctx, Hr, #Hlb⟩
  ihave Hr2 := swift.rdPd_wd x.str (R1.Wd c) r key hinj hkz $$ Hr
  icases Hr2 with (%Hnil | HW)
  · imodintro; ipureintro; intro h; exact absurd Hnil h
  · imod R1.Wd_seq c (toCmdId key) (r.PD.map toCmdId) s $$ [HW] with %H
    · iframe Hctx HW Hlb
    imodintro; ipureintro; intro _ hk; exact H hk

/-- `IterCb`'s unvisited entries: a key visited, or its descriptor. -/
theorem swift.visMap_mono (Mc : GMap GoString GoInterface) (vis vis' : List (GoString × GoInterface))
    (Φ : GoString → GoInterface → IProp netDistGF)
    (h : ∀ k, k ∈ vis.map Prod.fst → k ∈ vis'.map Prod.fst) :
    ([∗map] k ↦ vv ∈ Mc, ⌜k ∈ vis.map Prod.fst⌝ ∨ Φ k vv) ⊢
      [∗map] k ↦ vv ∈ Mc, ⌜k ∈ vis'.map Prod.fst⌝ ∨ Φ k vv := by
  refine BigSepM.bigSepM_mono_of_forall (fun {k _} => ?_)
  iintro (%h' | H)
  · ileft; ipureintro; exact h k h'
  · iright; iexact H

/-- **The report step** (`fillNewLeaderAckN`'s end; ghost): in recovery at ballot `b'` (the
view `w`, `cballot` `R.cbal < b'`), with `b'`'s report token, the run loop's `locLb` of its
sequence `s` of `cballot`, the base fact and the entries' witnesses: open `nodeInvD`, the
descriptor side's coverage (N1-R2, round 51: over the frozen record `Fz`, the held reads `SR` of
the stopped view `Mc`, the entries' facts `W`/`Wd`), `sp.upd_report` (`hnone` from the token, h4
from the view and `sp.rows_loc`, h5-h9 from `hF`), the token spent. -/
theorem swift.fill_report (E : CoPset) (hE : ↑swift.nodeN ⊆ E) (hE' : ↑sp.spN ⊆ E \ ↑swift.nodeN) (hD : ↑swift.delivN ⊆ E \ ↑swift.nodeN)
    (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX)
    (R1 : swift.N1R1 (hG := hG) rp γ γc γm x) (R2 : swift.N1R2 (hG := hG) rp γ γc γm x R1)
    (fr : Bool) (lg : List GoString) (w : swift.LView) (b' : Nat) (R : sp.Report) (s : sp.Seq)
    (B : List sp.CmdId) (X : List swift.ExE) (XS S : List sp.RepEntry) (SR : List swift.DescRead)
    (γdc : GName) (Mc : GMap GoString GoInterface) (dl : List sp.CmdId)
    (Pd : List (sp.CmdId × List sp.CmdId)) (M0 : Option sp.SyncMsg)
    (hr : x.r < x.N) (hk : nodeOf lg x.r = some x.k) (hb : w.1 = b') (hc : w.2.1 = R.cbal)
    (hcb : R.cbal < b') (hrows : ∀ b o, w.2.1 < b → (b, o) ∉ w.2.2.2)
    (hs : s.map Prod.fst = w.locAt R.cbal) (hB : B <+: w.locAt R.cbal)
    (hXS : XS.map (·.id) = X.map (fun e => toCmdId e.1))
    (hS : ∀ e ∈ S, ∃ r ∈ SR, r.entry = some e)
    (hMc : ∀ k v, Mc !! k = some v → ∃ r ∈ SR, r.k = k ∧
      v = interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #r.d)
    (hPd : ∀ p ∈ Pd, ∃ r ∈ SR, x.str (ofCmdId p.1) = r.k ∧ r.pdsl ≠ slice.nil ∧
      p.2 = r.PD.map toCmdId)
    (hdl : ∀ y ∈ dl, y ∈ X.map (fun e => toCmdId e.1))
    (hrep : ∀ r ∈ SR, ∀ e, r.entry = some e → e.id ∈ (XS ++ S).map (·.id) ∨ e.id ∈ B)
    (hkey : ∀ r ∈ SR, r.p ≠ null → x.str (ofCmdId r.y) = r.k) (hinj : Function.Injective x.str)
    (hF : ∀ st : sp.RState, swift.viewOf st = w →
      swift.coverOk x.N x.r R.cbal st s B XS S dl Pd → (∀ y ∈ B, (R.cbal, y) ∈ st.accR) →
      swift.fillFacts x.N x.r b' st R s B) (W' : List w64) :
    sp.inv γ γc γm x.γl ∗ sp.cfg γc γm x.N fr lg ∗
      inv swift.nodeN (swift.nodeInvD γ x.γv x.γe x.γo x.sn x.k) ∗
      swift.descCtxX γ γc γm x rp ∗
      ghostVar x.γv (1 : Iris.Qp).half w ∗ swift.repTok x.γrp b' ∗ sp.locLb γ x.r R.cbal s ∗
      (⌜R.cbal = 0 ∧ B = []⌝ ∨ ⌜0 < R.cbal⌝ ∗ ∃ M, ⌜M0 = some M⌝ ∗ sp.syncIs γ R.cbal M ∗
        ⌜B = sp.syncOrder M ∧ (M.map Prod.fst).Nodup ∧ ∀ p ∈ M,
          (∃ e ∈ R.entries, e.id = p.1 ∧ e.phase.toNat = 3 ∧ e.dep.Perm p.2.2) ∨
          (∃ e ∈ XS, e ∈ R.entries ∧ e.id = p.1 ∧ e.id ∈ B)⌝) ∗
      (⌜R.cbal = 0 ∧ B = [] ∧ M0 = none⌝ ∨
        ∃ M : sp.SyncMsg, ⌜M0 = some M⌝ ∗ sp.syncIs γ R.cbal M ∗
          sp.locLb γ (sp.leaderOf x.N R.cbal) R.cbal (sp.syncSeq M) ∗ ⌜B = sp.syncOrder M⌝) ∗
      R1.Fz R.cbal X ∗
      (▷ ∃ g : swift.DescG, swift.incInv g Mc ∗ ⌜g.ev.b = R.cbal⌝ ∗ swift.cgG x g) ∗
      swift.freeP x.γcg R.cbal ∗
      ghostMapAuth x.γout (1 : Iris.Qp).half (∅ : GMap (Nat × sp.CmdId) (Nat × Iris.Qp)) ∗
      github_com.orcaman.concurrent_map.cmapView γdc Mc ∗ ([∗list] r ∈ SR, r.fields) ∗
      ([∗list] r ∈ SR, swift.rdCl x.sn.γcl R.cbal r) ∗
      ([∗list] e ∈ XS ++ S, R1.W R.cbal e) ∗ ([∗list] e ∈ XS, R1.WX R.cbal e) ∗
      ([∗list] p ∈ Pd, R1.Wd R.cbal p.1 p.2) ∗
      ([∗list] e ∈ R.entries, swift.repEntW γ x.N x.r R.cbal e) ∗
      sp.predPre γ x.k (some (sp.PEv.report b' R, W')) ⊢
    |={E}=> ghostVar x.γv (1 : Iris.Qp).half w ∗ R1.Fz R.cbal X ∗
      (▷ ∃ g : swift.DescG, swift.incInv g Mc ∗ ⌜g.ev.b = R.cbal⌝ ∗ swift.cgG x g) ∗
      swift.freeP x.γcg R.cbal ∗
      ghostMapAuth x.γout (1 : Iris.Qp).half (∅ : GMap (Nat × sp.CmdId) (Nat × Iris.Qp)) ∗
      github_com.orcaman.concurrent_map.cmapView γdc Mc ∗ ([∗list] r ∈ SR, r.fields) ∗
      ([∗list] r ∈ SR, swift.rdCl x.sn.γcl R.cbal r) ∗
      sp.reported γ x.r b' R ∗ sp.predPost γ x.k (some (sp.PEv.report b' R, W')) := by
  iintro ⟨#Hinv, #Hcfg, #Hninv, #Hctx, Hw, Htk, #Hlb, #HB, #HB0, HFz, HPS, Hfp, Hout, Hview, Hf, Hcls,
    HW, HWX, HWd, Hws, Hpre⟩
  iinv Hninv with Hi Hclose
  iunfold swift.nodeInvD at Hi
  imod Hi
  icases Hi with ⟨%st, %O, Hst, Hw2, He, HO, HS, HX, %Hacc, %Hok⟩
  ihave %Heq := ghostVar_agree x.γv w (1 : Iris.Qp).half (swift.viewOf st) (1 : Iris.Qp).half
    $$ Hw Hw2
  subst Heq
  have hcst : st.cballot = R.cbal := hc
  have hbst : st.ballot = b' := hb
  -- `hnone`: the token (D72 (1))
  ihave ⟨HX, Htk, %Hnone⟩ := swift.nodeX_none γ x.sn st b' $$ [HX Htk]
  · iframe
  -- the base's acceptances (D72 (2)) and R2's base fact
  ihave ⟨HX, %Hbase⟩ : swift.nodeX γ x.sn st ∗ ⌜∀ y ∈ B, (R.cbal, y) ∈ st.accR⌝ $$ [HX]
  · icases HB with (⟨%h0, %hB0⟩ | ⟨%hpos, %M, %-, #HM, %hM⟩)
    · iframe HX; ipureintro; rw [hB0]; intro y hy; cases hy
    · ihave ⟨HX, %hba⟩ := swift.nodeX_base γ x.sn st M (by omega) $$ [HX]
      · iframe HX; rw [hcst]; iexact HM
      iframe HX; ipureintro; rw [hM.1, ← hcst]; exact hba
  -- the descriptor side's coverage (N1-R2)
  imod R2 E hE hE' hD R.cbal X XS S SR γdc Mc dl Pd st O s B M0 hcst hs hB hXS hS hMc hPd hdl hrep hkey hinj
    $$ [HFz HPS Hfp Hout Hview Hf Hcls HW HWX HWd Hst Hw2 He HO HS]
    with ⟨HFz, HPS, Hfp, Hout, Hview, Hf, Hcls, Hbody, %Hcov⟩
  · iframe Hctx HFz HPS Hfp Hout Hview Hf Hcls HW HWX HWd HB0 Hlb
    iunfold swift.nodeBody
    iframe
    ipureintro; exact ⟨Hacc, Hok⟩
  iunfold swift.nodeBody at Hbody
  icases Hbody with ⟨Hst, Hw2, He, HO, HS, -⟩
  -- h4: nothing between `cballot` and `b'` (the view's rows, `sp.rows_loc`)
  imod sp.rows_loc (E \ ↑swift.nodeN) hE' x.N fr lg x.r x.k st hr hk
    $$ [Hst] with ⟨Hst, %Hrl⟩
  · iframe Hinv Hcfg Hst
  have h4 : ∀ c' y, R.cbal < c' → c' < b' → (c', y) ∉ st.accR ∧ st.preAt c' y = none ∧
      (c', y) ∉ st.comR ∧ st.locAt c' = [] := by
    intro c' y h1 _
    have hnil : st.locAt c' = [] :=
      swift.LView.locAt_nil_of_rows (w := swift.viewOf st) (fun o => hrows c' o (by omega))
    have hcom : (c', y) ∉ st.comR := fun h => by
      have := Hrl.2 c' y h; rw [hnil] at this; cases this
    refine ⟨fun h => by have := Hacc c' y h; omega, ?_, hcom, hnil⟩
    cases h : st.preAt c' y with
    | none => rfl
    | some D => have := Hrl.1 c' y (by rw [h]; rfl); rw [hnil] at this; cases this
  obtain ⟨h5, h6, h7, h8, h9⟩ := hF st rfl Hcov.1 Hbase
  -- the witnesses at the node state
  imod swift.repEntWs_entryWit (E \ ↑swift.nodeN) hE' γ γc γm x.γl x.N fr lg x.r x.k
    R.cbal st hr hk R.entries $$ [Hst Hws] with ⟨Hst, Hents⟩
  · iframe Hinv Hcfg Hst Hws
  -- the report
  imod sp.upd_report (E \ ↑swift.nodeN) hE' x.N fr lg x.r x.k st b' R s B hr hk
    (by rw [hs]; rfl) Hnone (by omega) hcb h4 h5 h6 h7 h8 h9 W' $$ [Hst Hents Hpre] with ⟨Hst, Hpost, #Hrep⟩
  · iframe Hinv Hcfg Hst Hlb Hents Hpre
    icases HB with (%h0 | ⟨%hpos, %M, %hMM0, #HM, %hM⟩)
    · ileft; ipureintro; exact h0
    · -- round N7 (`N5: R2-a`): a base command that is a log entry, by N1-R2's R2-a (`Hcov.2`)
      iright; iexists M; iframe HM; ipureintro
      refine ⟨hM.1, fun p hp => ?_⟩
      rcases hM.2.2 p hp with h | ⟨e, heX, heR, hid, heB⟩
      · exact h
      · obtain ⟨hph, p', hp', hid', hperm⟩ := Hcov.2 M hMM0 e heX heB
        obtain rfl : p' = p := sp.mem_eq_of_fst hM.2.1 hp' hp (by rw [hid', hid])
        exact ⟨e, heR, hid, hph, hperm⟩
  -- the token spent
  ihave HX := swift.nodeX_report γ x.sn st b' R $$ [HX Htk]
  · iframe
  imod Hclose $$ [Hst Hw2 He HO HS HX] with -
  · inext
    iunfold swift.nodeInvD
    iexists st.reportedAs b' R, O
    iframe
    ipureintro; exact ⟨Hacc, Hok⟩
  imodintro
  iframe Hw HFz HPS Hfp Hout Hview Hf Hcls Hrep Hpost

end reqs

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

end proof

end Perennial.github_com.imdea_software.swiftpaxos

end
