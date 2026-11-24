/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/N/Boot.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit N: the generic replica's construction (`NewReplicaDurable`) and `monitorPings`

`monitorPings` receives from `pingChan`, on which nothing is ever sent (the client stream protocol
has no `GEN_PING`, so `serveClient` never dispatches to it): a bag of `False`.
-/
module

public import Dsverify.Proof.gryff.N.Stats
public import Dsverify.Proof.gryff.N.SpecsDefs
public import Dsverify.Proof.gryff.N.Build
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]

theorem set_app_rep {α : Type} (l : List α) (a b : α) (n : Nat) (h : l.length < n) :
    (l ++ List.replicate (n - l.length) a).set l.length b =
      (l ++ [b]) ++ List.replicate (n - (l ++ [b]).length) a := by
  obtain ⟨k, hk⟩ : ∃ k, n - l.length = k + 1 := ⟨n - l.length - 1, by omega⟩
  have hk' : n - (l ++ [b]).length = k := by simp; omega
  rw [hk, hk', List.replicate_succ, List.set_append_right _ _ (Nat.le_refl _)]
  simp

/-- The client-table law of `genericBuilt` for no registrations is vacuous. -/
theorem genericBuiltB_forget (gR : Loc) (id : w64) (nodes : List GoString)
    (regs : List (w8 × GoInterface × Loc)) (cregs : List (w8 × Loc)) :
    netN.genericBuiltB (GF := GF) gR id nodes regs cregs ⊢ netN.genericBuiltB gR id nodes regs [] := by
  unfold netN.genericBuiltB
  iintro ⟨%rt, %ct, %M, %CM, #Hrt, HM, Hcode, %Hregs, Hent, #Hct, HCM, -, Hrest⟩
  iexists rt, ct, M, CM
  iframe Hrt HM Hcode Hent Hct HCM Hrest
  isplitr
  · ipureintro; exact Hregs
  iintro !> %op %ch %hl
  simp [netN.lastReg] at hl

/-- A receive case of a `select` on a bag channel (unit B's `clause_bag`, `B/Loop.lean`). -/
theorem clause_bagN {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.GoType}
    [IntoValTyped (GF := GF) V t] [Pos.Countable V] (ch : Loc) (γc : ChanNames)
    (P : V → IProp GF) (body : Expr) (Ψ : val → IProp GF) :
    £ 1 ∗ £ 1 ∗ isChanBag γc ch P ∗ (▷ ∀ v, P v -∗ WP (App body (Val (PairV #v #true))) {{ Ψ }}) ⊢
      chan.blockingClausePre (.CommClause (.RecvCase t (Val #ch)) body) Ψ := by
  iintro ⟨Hlc1, Hlc2, #Hb, Hk⟩
  simp only [chan.blockingClausePre]
  iexists V, inferInstance, inferInstance, inferInstance, inferInstance, ch, γc
  isplitr
  · ipureintro; rfl
  isplitr
  · iapply is_bag_is_chan $$ Hb
  iapply bag_recv_au γc ch P (fun v ok => iprop(WP (App body (Val (PairV #v #ok))) {{ Ψ }})) $$
    [Hlc1 Hlc2] Hb Hk
  iframe

set_option goose.wp.extras true

/-- `monitorPings()`: blocks for good on `pingChan` (nothing is sent on it). -/
theorem monitorPings_wp (gR pc : Loc) (γp : ChanNames) :
    {{ gR.[src.genericsmr.Replica, go!"Shutdown"] ↦□ false ∗
        gR.[src.genericsmr.Replica, go!"pingChan"] ↦□ pc ∗
        isChanBag γp pc (fun _ : Loc => (iprop(False) : IProp GF)) }}
      (App (Val (gR @!! go.GoType.PointerType src.genericsmr.Replica.ty @!! go!"monitorPings"))
        (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#HSh, #Hpc, #Hbag⟩
  wp_auto_lc 2
  ihave IH : iprop(£ 1 ∗ £ 1) $$ [Hlc1 Hlc2]
  · iframe
  wp_for IH
  icases IH with ⟨Hlc1, Hlc2⟩
  try wp_auto
  wp_bind (App (Val (GoInstruction SelectStmt)) _)
  iapply chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2; isplit
  · iapply clause_bagN
    iframe Hlc1 Hlc2 Hbag
    inext
    iintro %v Hf
    iexfalso; iexact Hf
  iapply BigAndL.bigAndL_nil.2
  itrivial

/-- `state.NewState()`: a store with no entries. -/
theorem wp_NewState :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.state }}
      (App (Val (@! src.state.NewState)) (Val #()))
    {{ (s : Loc), RET #s; ∃ smR : Loc, s.[src.state.State, go!"Store"] ↦ smR ∗
        smR ↦$ (∅ : GMap w64 w64) }} := by
  wp_start
  wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := w64) _ _) as %smR Hm
  try wp_auto
  iStructNamedPrefix «$r0» "f"
  iapply HΦ
  iexists smR
  iframe
  done

/-- `stats.NewStatsMap()`: an empty stats map with its mutex (`statsOk`'s body). -/
theorem wp_NewStatsMap :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.stats }}
      (App (Val (@! src.stats.NewStatsMap)) (Val #()))
    {{ (st : Loc), RET #st; netN.statsOkB st }} := by
  wp_start
  iapply wp_fupd
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface) _ _) as %smR Hm
  try wp_auto
  imod sync.init_Mutex (iprop(∃ M : GMap GoString GoInterface, smR ↦$ M ∗
      [∗map] k ↦ v ∈ M, netN.statValB k v)) ⊤ «$v1_ptr» $$ [«$v1»] [Hm] with #Hmu
  · iexact «$v1»
  · inext
    iexists ∅
    iframe Hm
    iapply BigSepM.bigSepM_empty.2; itrivial
  ipersist «$r0»
  imodintro
  iapply HΦ
  iunfold netN.statsOkB
  imodintro
  iexists _
  iframe #

theorem NewReplicaDurable_wp (id : w64) (sl : GoSlice) (nodes : List GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr ∗ sl ↦* nodes }}
      (App (App (App (App (App (App (App (App (Val (@! src.genericsmr.NewReplicaDurable))
        (Val #id)) (Val #sl)) (Val #false)) (Val #true)) (Val #true)) (Val #false))
        (Val #(go!""))) (Val #false))
    {{ (gR : Loc), RET #gR; netN.genericBuiltB gR id nodes [] [] }} := by
  wp_start as Hsl
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  ihave #Hstate : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.state $$ []
  · iPkgInit
  ihave #Hstats : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.stats $$ []
  · iPkgInit
  iapply wp_fupd
  try wp_auto
  have hl0 : 0 ≤ sint.Z sl.len := Hlen.2
  wp_apply (wp_slice_make2 (V := GoInterface) sl.len) as %pS ⟨HpS, -⟩
  · ipureintro; exact hl0
  try wp_auto
  wp_apply (wp_slice_make2 (V := Loc) sl.len) as %rS ⟨HrS, -⟩
  · ipureintro; exact hl0
  try wp_auto
  wp_apply (wp_slice_make2 (V := Loc) sl.len) as %wS ⟨HwS, -⟩
  · ipureintro; exact hl0
  try wp_auto
  wp_apply (wp_slice_make2 (V := Bool) sl.len) as %aS ⟨HaS, -⟩
  · ipureintro; exact hl0
  try wp_auto
  wp_apply wp_NewState $$ [Hstate] as %stl ⟨%smR, HstS, Hsm⟩
  try wp_auto
  wp_apply (chan.wp_make2 (V := Loc) (W64 200000)) $$ [] as %propC %γprop ⟨#HpropC, -, HpropO⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (chan.wp_make2 (V := Loc) (W64 200000)) $$ [] as %beaC %γbea ⟨#HbeaC, -, HbeaO⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (wp_slice_make2 (V := w32) sl.len) as %ppoS ⟨HppoS, -⟩
  · ipureintro; exact hl0
  try wp_auto
  wp_apply (wp_map_make1 (K := w8) (V := Loc) _ _) as %rt Hrt
  try wp_auto
  wp_apply (wp_map_make1 (K := w8) (V := Loc) _ _) as %ct Hct
  try wp_auto
  wp_apply (wp_slice_make2 (V := w64) sl.len) as %ewS ⟨HewS, -⟩
  · ipureintro; exact hl0
  try wp_auto
  wp_apply (chan.wp_make2 (V := Bool) (W64 100)) $$ [] as %occ %γocc ⟨#HoccC, -, HoccO⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (chan.wp_make2 (V := Loc) (W64 200000)) $$ [] as %pc %γp ⟨#HpcC, -, HpcO⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (wp_map_make1 (K := w32) (V := Loc) _ _) as %crm Hcrm
  try wp_auto
  wp_apply (wp_map_make1 (K := w32) (V := Loc) _ _) as %cwm Hcwm
  try wp_auto
  wp_apply wp_NewStatsMap $$ [Hstats] as %st Hsto
  try wp_auto
  wp_apply (chan.wp_make2 (V := Bool) (W64 1)) $$ [] as %dac %γda ⟨#HdaC, -, HdaO⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (wp_slice_make2 (V := Loc) (W64 0)) as %d0 ⟨Hd0, -⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (wp_slice_make2 (V := Loc) (W64 0)) as %dl0 ⟨Hdl0, -⟩
  · ipureintro; decide
  try wp_auto
  simp only [src.genericsmr.Replica.fieldsUnsealed, List.zip_cons_cons,
    List.zip_nil_right, List.foldl_cons, List.foldl_nil]
  try wp_auto
  iStructNamedPrefix «$r0» "f"
  ipersist fN; ipersist fId; ipersist fPeerAddrList; ipersist fPeers; ipersist fPeerReaders
  ipersist fPeerWriters; ipersist fAlive; ipersist fState; ipersist fProposeChan; ipersist fBeaconChan
  ipersist fShutdown; ipersist fThrifty; ipersist fExec; ipersist fDreply
  ipersist fPreferredPeerOrder; ipersist frpcTable; ipersist fclientRpcTable
  ipersist fEwma; ipersist fOnClientConnect; ipersist fclientConnect; ipersist fpingChan
  ipersist fclientReaders; ipersist fclientWriters; ipersist fclientIdMapsLock; ipersist fstatsFile
  ipersist fStats; ipersist fDoneAdaptingChan
  have hn : sint.nat sl.len = nodes.length := Hlen.1.symm
  have hsl : (nodes.length : Int) = sint.Z sl.len := by
    rw [Hlen.1]; exact Int.toNat_of_nonneg Hlen.2
  -- PreferredPeerOrder and Ewma
  ihave IH : iprop(∃ (j : w64) (ps : List w32),
      "i" ∷ i_ptr ↦ j ∗ "HppoS" ∷ ppoS ↦* ps ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len ∧ ps.length = nodes.length ∧
        ∀ m : Nat, (m : Int) < sint.Z j → ps[m]? = some (netN.ppoVal id sl.len m)⌝) $$ [i HppoS]
  · iexists _, _; iframe; ipureintro; simp [hn]
    refine ⟨by omega, fun m hm => ?_⟩
    have : sint.Z (W64 0) = 0 := rfl
    omega
  wp_for IH
  wp_if_destruct
  · try wp_auto
    rw [if_neg (show ¬ sint.Z sl.len = 0 by omega)]
    try wp_auto
    ihave %Hpl := ownSlice_len _ _ _ $$ HppoS
    have hpl : (ps.length : Int) = sint.Z ppoS.len := by
      rw [Hpl.1]; exact Int.toNat_of_nonneg Hpl.2
    rw [if_pos ⟨Hj.1, by omega⟩]
    wp_apply wp_store_slice_index ppoS (sint.Z j) ps _ $$ [HppoS] as HppoS
    · iframe; ipureintro; omega
    try wp_auto
    ihave %Hel := ownSlice_len _ _ _ $$ HewS
    have hel : ((List.replicate (sint.nat sl.len) (zero_val w64)).length : Int) = sint.Z ewS.len := by
      rw [Hel.1]; exact Int.toNat_of_nonneg Hel.2
    simp only [List.length_replicate, hn] at hel
    rw [if_pos ⟨Hj.1, by omega⟩]
    wp_apply wp_store_slice_index ewS (sint.Z j) _ _ $$ [HewS] as HewS
    · iframe; ipureintro; simp only [List.length_replicate, hn]; omega
    rw [show (W64 0 : w64) = zero_val w64 from rfl, List.set_replicate_self]
    wp_for_post
    iframe
    iexists _, _
    iframe
    ipureintro
    simp only [List.length_set]
    refine ⟨by word, by word, Hj.2.2.1, fun m hm => ?_⟩
    have hj1 : sint.Z (j + W64 1) = sint.Z j + 1 := by word
    rw [hj1] at hm
    have hjl : (sint.Z j).toNat < ps.length := by have := Hj.2.2.1; omega
    by_cases hmj : (m : Int) = sint.Z j
    · have hm' : m = (sint.Z j).toNat := by omega
      subst hm'
      rw [List.getElem?_set_self hjl]
      unfold netN.ppoVal
      have e : (((sint.Z j).toNat : Nat) : Int) = sint.Z j := Int.toNat_of_nonneg Hj.1
      rw [e]
      have e2 : W64 (sint.Z j) = j := by word
      rw [e2]
    · rw [List.getElem?_set_ne (by omega)]
      exact Hj.2.2.2 m (by omega)
  have hps : ps.length = nodes.length := Hj.2.2.1
  have hpsv : ∀ m : Nat, m < nodes.length → ps[m]? = some (netN.ppoVal id sl.len m) := by
    intro m hm
    exact Hj.2.2.2 m (by omega)
  try wp_auto
  wp_apply (wp_slice_make2 (V := Loc) sl.len) as %dS ⟨HdS, -⟩
  · ipureintro; exact hl0
  try wp_auto
  wp_apply (wp_slice_make2 (V := Loc) sl.len) as %dlS ⟨HdlS, -⟩
  · ipureintro; exact hl0
  try wp_auto
  ihave IH2 : iprop(∃ (j : w64) (ms mls : List Loc),
      "i" ∷ i_ptr ↦ j ∗ "HdS" ∷ dS ↦* (ms ++ List.replicate (nodes.length - ms.length) null) ∗
      "HdlS" ∷ dlS ↦* (mls ++ List.replicate (nodes.length - mls.length) null) ∗
      "Hms" ∷ ([∗list] mp ∈ ms, mp ↦$ (∅ : GMap w8 Bool)) ∗
      "Hmls" ∷ ([∗list] mp ∈ mls, mp ↦$ (∅ : GMap w8 Loc)) ∗
      "%Hj" ∷ ⌜sint.Z j = ms.length ∧ sint.Z j = mls.length ∧ sint.Z j ≤ sint.Z sl.len⌝) $$ [i HdS HdlS]
  · iexists _, [], []
    simp only [List.length_nil, List.nil_append, Nat.sub_zero, hn]
    iframe
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    ipureintro; simp; omega
  wp_for IH2
  wp_if_destruct
  · try wp_auto
    wp_apply (wp_map_make1 (K := w8) (V := Bool) _ _) as %m1 Hm1
    try wp_auto
    ihave %Hdl := ownSlice_len _ _ _ $$ HdS
    have hms : ms.length < nodes.length := by omega
    have hdl : (nodes.length : Int) = sint.Z dS.len := by
      have := Hdl.1; simp only [List.length_append, List.length_replicate] at this
      rw [show ms.length + (nodes.length - ms.length) = nodes.length by omega] at this
      rw [this]; exact Int.toNat_of_nonneg Hdl.2
    rw [if_pos ⟨by omega, by omega⟩]
    wp_apply wp_store_slice_index dS (sint.Z j) _ m1 $$ [HdS] as HdS
    · iframe; ipureintro; simp; omega
    try wp_auto
    wp_apply (wp_map_make1 (K := w8) (V := Loc) _ _) as %m2 Hm2
    try wp_auto
    ihave %Hdll := ownSlice_len _ _ _ $$ HdlS
    have hmls : mls.length < nodes.length := by omega
    have hdll : (nodes.length : Int) = sint.Z dlS.len := by
      have := Hdll.1; simp only [List.length_append, List.length_replicate] at this
      rw [show mls.length + (nodes.length - mls.length) = nodes.length by omega] at this
      rw [this]; exact Int.toNat_of_nonneg Hdll.2
    rw [if_pos ⟨by omega, by omega⟩]
    wp_apply wp_store_slice_index dlS (sint.Z j) _ m2 $$ [HdlS] as HdlS
    · iframe; ipureintro; simp; omega
    rw [show (sint.Z j).toNat = ms.length by omega]
    rw [set_app_rep ms null m1 _ hms]
    rw [show ms.length = mls.length by omega, set_app_rep mls null m2 _ hmls]
    wp_for_post
    iframe
    iexists _, ms ++ [m1], mls ++ [m2]
    iframe
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    ipureintro
    simp only [List.length_append, List.length_singleton]
    refine ⟨by word, by word, by word⟩
  have hms : ms.length = nodes.length := by omega
  have hmls : mls.length = nodes.length := by omega
  simp only [hms, hmls, Nat.sub_self, List.replicate_zero, List.append_nil]
  rw [hn]
  ipersist fdelayRPC; ipersist fdelayedRPC
  imod start_bag (fun _ : Loc => iprop(False)) _ pc γp (by simp) $$ HpcC HpcO with #Hpbag
  ihave Hgb : netN.genericBuiltB «$r0_ptr» id nodes [] [] $$ [Hrt Hct frpcCode Hsl HpS HrS HwS HaS
      fListener HstS Hsm HpropO HbeaO HppoS HewS HoccO Hcrm Hcwm «$v28» Hsto HdaO HdS HdlS Hms Hmls
      fBeacon fDurable]
  · iunfold netN.genericBuiltB
    iexists rt, ct, ∅, ∅
    iframe frpcTable Hrt
    isplitl [frpcCode]
    · have e : (W8 7 + W8 1 : w8) = W8 (8 + (([] : List (w8 × GoInterface × Loc)).length : Int)) := by
        simp only [List.length_nil]; rfl
      rw [← e]
      iexact frpcCode
    isplitr
    · ipureintro; simp
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    iframe fclientRpcTable Hct
    isplitr
    · iintro !> %op %ch %hl
      simp [netN.lastReg] at hl
    iunfold netN.builtRest
    iexists sl, pS, rS, wS, aS, ppoS, ewS, dS, dlS, stl, smR, propC, beaC, occ, pc, crm, cwm,
      «$v28_ptr», st, dac, γprop, γbea, γocc, γp, γda, ps, ms, mls
    iframe
    iframe #
    ipureintro; exact ⟨Hlen.1, Hlen.2, hps, hms, hmls, hpsv⟩
  try wp_auto
  wp_alloc ping as Hping
  try wp_auto
  wp_apply (netN.RegisterClientRPC_wp «$r0_ptr» id nodes [] [] _ _ pc) $$ [Hgb] as Hgb
  · iframe
  try wp_auto
  wp_apply wp_fork $$ []
  · wp_apply (monitorPings_wp «$r0_ptr» pc γp) $$ []
    · iframe #
    itrivial
  try wp_auto
  imodintro
  iapply HΦ
  iapply genericBuiltB_forget $$ Hgb

end

end Perennial.gryff.replica2
