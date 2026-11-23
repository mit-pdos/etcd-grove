/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `Init0`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Init0
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem Init0_set {α : Type} (a z : α) (n k : Nat) (hk : k < n) :
    (List.replicate k a ++ List.replicate (n - k) z).set k a =
      List.replicate (k + 1) a ++ List.replicate (n - (k + 1)) z := by
  obtain ⟨m, hm⟩ : ∃ m, n - k = m + 1 := ⟨n - k - 1, by omega⟩
  rw [hm, show n - (k + 1) = m by omega, List.set_append_right _ _ (by simp), List.length_replicate,
    Nat.sub_self, List.replicate_succ, List.set_cons_zero, List.replicate_succ', List.append_assoc]
  rfl

theorem Init0_rep {A B : Type} (Φ : A → B → IProp GF) [∀ a b, Persistent (Φ a b)] (a : A) (b : B) :
    ∀ N : Nat, Φ a b ⊢ [∗list] x;y ∈ List.replicate N a;List.replicate N b, Φ x y
  | 0 => by simp only [List.replicate_zero]; exact BigSepL2.bigSepL2_nil_affine
  | N + 1 => by
    iintro #H
    simp only [List.replicate_succ]
    iapply BigSepL2.bigSepL2_cons.2
    isplit
    · iexact H
    iapply Init0_rep Φ a b N
    iexact H

theorem Init0_rel {A B : Type} (R : A → B → Prop) (a : A) (b : B) (h : R a b) :
    ∀ N : Nat, List.Forall₂ R (List.replicate N a) (List.replicate N b)
  | 0 => .nil
  | N + 1 => .cons h (Init0_rel R a b h N)

theorem Init0_ints (sl : GoSlice) (N : Nat) (w : w64) (x : Int) (h : sint.Z w = x) :
    sl ↦*□ List.replicate N w ⊢ intsRO (GF := GF) sl (List.replicate N x) := by
  iintro #H
  iunfold intsRO
  iexists _
  isplit
  · iexact H
  ipureintro; simp [List.map_replicate, h]

theorem Init0_strsNil : ⊢ strsRO (GF := GF) slice.nil [] := by
  iunfold strsRO; iapply ownSlice_nil

theorem Init0_logNil : ⊢ logRO (GF := GF) slice.nil [] := by
  iunfold logRO; iexists []; isplit
  · iapply ownSlice_nil
  iapply BigSepL2.bigSepL2_nil.2; iempintro

theorem Init0_msgsNil : ⊢ msgsRO (GF := GF) slice.nil [] := by
  iunfold msgsRO; iexists []; isplit
  · iapply ownSlice_nil
  iapply BigSepL2.bigSepL2_nil.2; iempintro

theorem Init0_qitemsNil : ⊢ qitemsRO (GF := GF) slice.nil [] := by
  iunfold qitemsRO; iexists []; isplit
  · iapply ownSlice_nil
  iapply BigSepL2.bigSepL2_nil.2; iempintro

theorem Init0_readRecsNil : ⊢ readRecsRO (GF := GF) slice.nil [] := by
  iunfold readRecsRO; iexists []; isplit
  · iapply ownSlice_nil
  ipureintro; exact .nil

theorem Init0_factsNil : ⊢ factsRO (GF := GF) slice.nil [] := by
  iunfold factsRO; iexists []; isplit
  · iapply ownSlice_nil
  ipureintro; exact .nil

theorem Init0_votesNil : ⊢ votesRO (GF := GF) slice.nil [] := by
  iunfold votesRO; iexists []; isplit
  · iapply ownSlice_nil
  ipureintro; exact .nil

theorem Init0_leadersNil : ⊢ leadersRO (GF := GF) slice.nil [] := by
  iunfold leadersRO; iexists []; isplit
  · iapply ownSlice_nil
  ipureintro; exact .nil

theorem Init0_termLogsNil : ⊢ termLogsRO (GF := GF) slice.nil [] := by
  iunfold termLogsRO; iexists []; isplit
  · iapply ownSlice_nil
  iapply BigSepL2.bigSepL2_nil.2; iempintro

theorem Init0_termConfsNil : ⊢ termConfsRO (GF := GF) slice.nil [] := by
  iunfold termConfsRO; iexists []; isplit
  · iapply ownSlice_nil
  iapply BigSepL2.bigSepL2_nil.2; iempintro

theorem Init0_termIntsNil : ⊢ termIntsRO (GF := GF) slice.nil [] := by
  iunfold termIntsRO; iexists []; isplit
  · iapply ownSlice_nil
  ipureintro; exact .nil

theorem Init0_preNone : ⊢ preRO (GF := GF) (zero_val Loc) none := by
  unfold preRO; ipureintro; rfl

theorem Init0.wp_proof : Init0.spec (GF := GF) (hG := hG) := by
  intro cp cfg s
  wp_start as ⟨#Hc, %Hs⟩
  iapply wp_fupd
  iunfold configRO at Hc
  icases Hc with ⟨%gc, #Hcp, #Hsrv, #Hiv, %Hb⟩
  iunfold strsRO at Hsrv Hiv
  ihave %Hlen := ownSlice_len $$ Hsrv
  iStructNamed Hcp
  wp_auto
  wp_apply wp_slice_make2 (V := w64) gc.Server'.len $$ [] as %slCT ⟨HCT, -⟩
  · ipureintro; exact Hlen.2
  try wp_auto
  wp_apply wp_slice_make2 (V := w64) gc.Server'.len $$ [] as %slVT ⟨HVT, -⟩
  · ipureintro; exact Hlen.2
  try wp_auto
  wp_apply wp_slice_make2 (V := GoString) gc.Server'.len $$ [] as %slVF ⟨HVF, -⟩
  · ipureintro; exact Hlen.2
  try wp_auto
  wp_apply wp_slice_make2 (V := GoSlice) gc.Server'.len $$ [] as %slLog ⟨HLog, -⟩
  · ipureintro; exact Hlen.2
  try wp_auto
  wp_apply wp_slice_make2 (V := w64) gc.Server'.len $$ [] as %slCI ⟨HCI, -⟩
  · ipureintro; exact Hlen.2
  try wp_auto
  wp_apply wp_slice_make2 (V := GoString) gc.Server'.len $$ [] as %slRole ⟨HRole, -⟩
  · ipureintro; exact Hlen.2
  try wp_auto
  wp_apply wp_slice_make2 (V := w64) gc.Server'.len $$ [] as %slLA ⟨HLA, -⟩
  · ipureintro; exact Hlen.2
  try wp_auto
  wp_apply wp_slice_make2 (V := G.Conf) gc.Server'.len $$ [] as %slConfig ⟨HConfig, -⟩
  · ipureintro; exact Hlen.2
  try wp_auto
  wp_apply wp_slice_make2 (V := w64) gc.Server'.len $$ [] as %slCA ⟨HCA, -⟩
  · ipureintro; exact Hlen.2
  try wp_auto
  wp_apply wp_slice_make2 (V := G.Confirmed) gc.Server'.len $$ [] as %slCf ⟨HCf, -⟩
  · ipureintro; exact Hlen.2
  try wp_auto
  wp_apply wp_slice_make2 (V := Loc) gc.Server'.len $$ [] as %slUndo ⟨HUndo, -⟩
  · ipureintro; exact Hlen.2
  try wp_auto
  wp_apply wp_slice_make2 (V := GoSlice) gc.Server'.len $$ [] as %slPend ⟨HPend, -⟩
  · ipureintro; exact Hlen.2
  try wp_auto
  wp_apply wp_slice_make2 (V := GoSlice) gc.Server'.len $$ [] as %slQueue ⟨HQueue, -⟩
  · ipureintro; exact Hlen.2
  try wp_auto
  wp_apply wp_slice_make2 (V := GoSlice) gc.Server'.len $$ [] as %slReads ⟨HReads, -⟩
  · ipureintro; exact Hlen.2
  try wp_auto
  dsimp only
  ipersist HCI; ipersist HLA; ipersist HCA; ipersist HUndo; ipersist HPend; ipersist HQueue; ipersist HReads
  ihave IH : iprop(∃ (kk : w64), "k" ∷ k_ptr ↦ kk ∗
      "HRole" ∷ slRole ↦* (List.replicate (sint.nat kk) follower ++
        List.replicate (sint.nat gc.Server'.len - sint.nat kk) (zero_val GoString)) ∗
      "HConfig" ∷ slConfig ↦* (List.replicate (sint.nat kk) ({ In' := gc.InitVoters', Out' := slice.nil } : G.Conf) ++
        List.replicate (sint.nat gc.Server'.len - sint.nat kk) (zero_val G.Conf)) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z kk ∧ sint.Z kk ≤ sint.Z gc.Server'.len⌝) $$ [k HRole HConfig]
  · iexists _
    rw [show sint.nat (W64 0) = 0 from rfl]
    simp only [List.replicate_zero, List.nil_append, Nat.sub_zero]
    iframe
    ipureintro; word
  wp_for IH
  wp_if_destruct
  · have hlt : sint.Z kk < sint.Z gc.Server'.len := by simpa using Hif
    ihave %HlR := ownSlice_len $$ HRole
    ihave %HlC := ownSlice_len $$ HConfig
    simp only [List.length_append, List.length_replicate] at HlR HlC
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z kk ∧ sint.Z kk < sint.Z slRole.len by constructor <;> word))]
    rw [show github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Follower = #follower from rfl]
    wp_apply wp_store_slice_index slRole (sint.Z kk) _ follower $$ [HRole] as HRole
    · iframe HRole; ipureintro; simp only [List.length_append, List.length_replicate]; word
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z kk ∧ sint.Z kk < sint.Z slConfig.len by constructor <;> word))]
    wp_apply wp_store_slice_index slConfig (sint.Z kk) _ ({ In' := gc.InitVoters', Out' := slice.nil } : G.Conf) $$ [HConfig] as HConfig
    · iframe HConfig; ipureintro; simp only [List.length_append, List.length_replicate]; word
    try wp_auto
    wp_for_post
    iframe
    iexists (kk + W64 1)
    have hn : sint.nat (kk + W64 1) = sint.nat kk + 1 := by word
    have hz : (sint.Z kk).toNat = sint.nat kk := rfl
    have hkn : sint.nat kk < sint.nat gc.Server'.len := by word
    rw [hz, hn]; simp only [Init0_set _ _ _ _ hkn]
    iframe; ipureintro; word
  · have hkk : sint.nat kk = sint.nat gc.Server'.len := by word
    rw [hkk, Nat.sub_self]; simp only [List.replicate_zero, List.append_nil]
    ipersist HRole; ipersist HConfig
    obtain ⟨hs, hbd⟩ := Hs
    cases hc : cfg.bootstrapped
    · rw [Hb, hc]
      wp_auto
      ipersist «$r0»; ipersist HCT; ipersist HVT; ipersist HVF; ipersist HLog; ipersist HCf
      imodintro
      simp [init0, hc] at hs
      have hs' := Except.ok.inj hs
      subst hs'
      iapply HΦ
      iunfold stateRO
      iexists _
      isplit
      · iexact «$r0»
      iunfold stateFields
      dsimp only
      rw [Hlen.1]
      isplit
      · iunfold configRO; iexists gc; isplit
        · iexact Hcp
        iunfold strsRO; isplit
        · iexact Hsrv
        isplit
        · iexact Hiv
        ipureintro; exact Hb
      isplit
      · iapply Init0_ints _ _ (zero_val w64) 0 rfl; iexact HCT
      isplit
      · iapply Init0_ints _ _ (zero_val w64) 0 rfl; iexact HVT
      isplit
      · iunfold strsRO; iexact HVF
      isplit
      · iunfold logsRO; iexists _; isplit
        · iexact HLog
        iapply Init0_rep; iapply Init0_logNil
      isplit
      · iapply Init0_ints _ _ (zero_val w64) 0 rfl; iexact HCI
      isplit
      · iunfold strsRO; iexact HRole
      isplit
      · iapply Init0_ints _ _ (zero_val w64) 0 rfl; iexact HLA
      isplit
      · iunfold confsRO; iexists _; isplit
        · iexact HConfig
        iapply Init0_rep; iunfold confRO; simp only [Config.initConf]; isplit
        · iunfold strsRO; iexact Hiv
        iapply Init0_strsNil
      isplit
      · iapply Init0_ints _ _ (zero_val w64) 0 rfl; iexact HCA
      isplit
      · iunfold confirmedsRO; iexists _; isplit
        · iexact HCf
        ipureintro; exact Init0_rel _ _ _ ⟨rfl, rfl⟩ _
      isplit
      · iapply Init0_factsNil
      isplit
      · iapply Init0_votesNil
      isplit
      · iapply Init0_leadersNil
      isplit
      · iapply Init0_termLogsNil
      isplit
      · iapply Init0_termConfsNil
      isplit
      · iapply Init0_termIntsNil
      isplit
      · iapply Init0_termIntsNil
      isplit
      · ipureintro; rfl
      isplit
      · iunfold undoRO; iexists _; isplit
        · iexact HUndo
        iapply Init0_rep; iapply Init0_preNone
      isplit
      · iunfold pendingRO; iexists _; isplit
        · iexact HPend
        iapply Init0_rep; iapply Init0_msgsNil
      isplit
      · iunfold queueRO; iexists _; isplit
        · iexact HQueue
        iapply Init0_rep; iapply Init0_qitemsNil
      isplit
      · iunfold readsRO; iexists _; isplit
        · iexact HReads
        iapply Init0_rep; iapply Init0_readRecsNil
      isplit
      · iapply Init0_logNil
      isplit
      · iapply Init0_termIntsNil
      isplit
      · iapply Init0_strsNil
      ipureintro; simp [State.Wf, Hlen.1]
    · rw [Hb, hc]
      wp_auto
      cases hv : cfg.initVoters with
      | nil => simp [init0, hc, hv, evalError] at hs
      | cons first rest =>
      have h0 : (0 : Int) ≤ sint.Z (W64 0) := by word
      have hf : (first :: rest)[sint.nat (W64 0)]? = some first := by
        rw [show sint.nat (W64 0) = 0 from rfl]; rfl
      wp_apply wp_load_index gc.InitVoters' (W64 0) (first :: rest) first h0 hf $$ [Hiv]
      · iexact Hiv
      try wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %bp ⟨Hboot, -⟩
      generalize hbs : slice.mk bp _ _ = boot
      clear hbs
      ipersist Hboot
      try wp_auto
      ihave IH2 : iprop(∃ (kk : w64), "k" ∷ k_ptr ↦ kk ∗
          "HCT" ∷ slCT ↦* (List.replicate (sint.nat kk) (W64 1) ++
            List.replicate (sint.nat gc.Server'.len - sint.nat kk) (zero_val w64)) ∗
          "HVT" ∷ slVT ↦* (List.replicate (sint.nat kk) (W64 1) ++
            List.replicate (sint.nat gc.Server'.len - sint.nat kk) (zero_val w64)) ∗
          "HVF" ∷ slVF ↦* (List.replicate (sint.nat kk) first ++
            List.replicate (sint.nat gc.Server'.len - sint.nat kk) (zero_val GoString)) ∗
          "HLog" ∷ slLog ↦* (List.replicate (sint.nat kk) boot ++
            List.replicate (sint.nat gc.Server'.len - sint.nat kk) (zero_val GoSlice)) ∗
          "HCf" ∷ slCf ↦* (List.replicate (sint.nat kk) ({ Term' := W64 1, Index' := W64 1 } : G.Confirmed) ++
            List.replicate (sint.nat gc.Server'.len - sint.nat kk) (zero_val G.Confirmed)) ∗
          "%Hk" ∷ ⌜0 ≤ sint.Z kk ∧ sint.Z kk ≤ sint.Z gc.Server'.len⌝) $$ [k HCT HVT HVF HLog HCf]
      · iexists _
        rw [show sint.nat (W64 0) = 0 from rfl]
        simp only [List.replicate_zero, List.nil_append, Nat.sub_zero]
        iframe
        ipureintro; word
      wp_for IH2
      simp only [decide_eq_true_eq]
      by_cases hlt : sint.Z kk < sint.Z gc.Server'.len
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hlt)]
        wp_auto
        ihave %LHCT := ownSlice_len $$ HCT
        ihave %LHVT := ownSlice_len $$ HVT
        ihave %LHVF := ownSlice_len $$ HVF
        ihave %LHLog := ownSlice_len $$ HLog
        ihave %LHCf := ownSlice_len $$ HCf
        simp only [List.length_append, List.length_replicate] at LHCT LHVT LHVF LHLog LHCf
        rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z kk ∧ sint.Z kk < sint.Z slCT.len by constructor <;> word))]
        wp_apply wp_store_slice_index slCT (sint.Z kk) _ (W64 1) $$ [HCT] as HCT
        · iframe HCT; ipureintro; simp only [List.length_append, List.length_replicate]; word
        try wp_auto
        rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z kk ∧ sint.Z kk < sint.Z slVT.len by constructor <;> word))]
        wp_apply wp_store_slice_index slVT (sint.Z kk) _ (W64 1) $$ [HVT] as HVT
        · iframe HVT; ipureintro; simp only [List.length_append, List.length_replicate]; word
        try wp_auto
        rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z kk ∧ sint.Z kk < sint.Z slVF.len by constructor <;> word))]
        wp_apply wp_store_slice_index slVF (sint.Z kk) _ first $$ [HVF] as HVF
        · iframe HVF; ipureintro; simp only [List.length_append, List.length_replicate]; word
        try wp_auto
        rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z kk ∧ sint.Z kk < sint.Z slLog.len by constructor <;> word))]
        wp_apply wp_store_slice_index slLog (sint.Z kk) _ boot $$ [HLog] as HLog
        · iframe HLog; ipureintro; simp only [List.length_append, List.length_replicate]; word
        try wp_auto
        rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z kk ∧ sint.Z kk < sint.Z slCf.len by constructor <;> word))]
        wp_apply wp_store_slice_index slCf (sint.Z kk) _ ({ Term' := W64 1, Index' := W64 1 } : G.Confirmed) $$ [HCf] as HCf
        · iframe HCf; ipureintro; simp only [List.length_append, List.length_replicate]; word
        try wp_auto
        wp_for_post
        iframe
        iexists (kk + W64 1)
        have hn : sint.nat (kk + W64 1) = sint.nat kk + 1 := by word
        have hz : (sint.Z kk).toNat = sint.nat kk := rfl
        have hkn : sint.nat kk < sint.nat gc.Server'.len := by word
        rw [hz, hn]; simp only [Init0_set _ _ _ _ hkn]
        iframe; ipureintro; word
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hlt)]
        try wp_auto
        rw [ite_eq_right_of_eq_false _ _ (eq_false hlt)]
        try wp_auto
        have hkk : sint.nat kk = sint.nat gc.Server'.len := by word
        rw [hkk, Nat.sub_self]; simp only [List.replicate_zero, List.append_nil]
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %Leadersp ⟨HLeaders, -⟩
        generalize hLeaderss : slice.mk Leadersp _ _ = slLeaders
        clear hLeaderss
        ipersist HLeaders
        try wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %LedLogp ⟨HLedLog, -⟩
        generalize hLedLogs : slice.mk LedLogp _ _ = slLedLog
        clear hLedLogs
        ipersist HLedLog
        try wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %LedConfp ⟨HLedConf, -⟩
        generalize hLedConfs : slice.mk LedConfp _ _ = slLedConf
        clear hLedConfs
        ipersist HLedConf
        try wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %LedAtp ⟨HLedAt, -⟩
        generalize hLedAts : slice.mk LedAtp _ _ = slLedAt
        clear hLedAts
        ipersist HLedAt
        try wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %ElAtp ⟨HElAt, -⟩
        generalize hElAts : slice.mk ElAtp _ _ = slElAt
        clear hElAts
        ipersist HElAt
        try wp_auto
        dsimp only
        ipersist «$r0»; ipersist HCT; ipersist HVT; ipersist HVF; ipersist HLog; ipersist HCf
        imodintro
        simp [init0, hc, hv] at hs
        have hs' := Except.ok.inj hs
        subst hs'
        ihave #HbL : iprop(logRO boot [{ term := 1, type := go!"config", value := { str := [] } }]) $$ []
        · iunfold logRO; iexists _; isplit
          · iexact Hboot
          iapply BigSepL2.bigSepL2_cons.2; isplit
          · iunfold entryRO; isplit
            · ipureintro; exact ⟨rfl, rfl⟩
            iunfold valueRO; isplit
            · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
            isplit
            · iapply Init0_strsNil
            iapply Init0_strsNil
          iapply BigSepL2.bigSepL2_nil.2; iempintro
        ihave #HiC : iprop(confRO { In' := gc.InitVoters', Out' := slice.nil } cfg.initConf) $$ []
        · iunfold confRO; simp only [Config.initConf, hv]; isplit
          · iunfold strsRO; iexact Hiv
          iapply Init0_strsNil
        iapply HΦ
        iunfold stateRO
        iexists _
        isplit
        · iexact «$r0»
        iunfold stateFields
        dsimp only
        rw [Hlen.1]
        isplit
        · iunfold configRO; iexists gc; isplit
          · iexact Hcp
          iunfold strsRO; rw [hv]; isplit
          · iexact Hsrv
          isplit
          · iexact Hiv
          ipureintro; rw [Hb, hc]
        isplit
        · iapply Init0_ints _ _ (W64 1) 1 rfl; iexact HCT
        isplit
        · iapply Init0_ints _ _ (W64 1) 1 rfl; iexact HVT
        isplit
        · iunfold strsRO; iexact HVF
        isplit
        · iunfold logsRO; iexists _; isplit
          · iexact HLog
          iapply Init0_rep; iexact HbL
        isplit
        · iapply Init0_ints _ _ (zero_val w64) 0 rfl; iexact HCI
        isplit
        · iunfold strsRO; iexact HRole
        isplit
        · iapply Init0_ints _ _ (zero_val w64) 0 rfl; iexact HLA
        isplit
        · iunfold confsRO; iexists _; isplit
          · iexact HConfig
          iapply Init0_rep; iexact HiC
        isplit
        · iapply Init0_ints _ _ (zero_val w64) 0 rfl; iexact HCA
        isplit
        · iunfold confirmedsRO; iexists _; isplit
          · iexact HCf
          ipureintro; exact Init0_rel _ _ _ ⟨rfl, rfl⟩ _
        isplit
        · iapply Init0_factsNil
        isplit
        · iapply Init0_votesNil
        isplit
        · iunfold leadersRO; iexists _; isplit
          · iexact HLeaders
          ipureintro; exact .cons ⟨rfl, rfl⟩ .nil
        isplit
        · iunfold termLogsRO; iexists _; isplit
          · iexact HLedLog
          iapply BigSepL2.bigSepL2_cons.2; isplit
          · isplit
            · ipureintro; rfl
            iexact HbL
          iapply BigSepL2.bigSepL2_nil.2; iempintro
        isplit
        · iunfold termConfsRO; iexists _; isplit
          · iexact HLedConf
          iapply BigSepL2.bigSepL2_cons.2; isplit
          · isplit
            · ipureintro; rfl
            iexact HiC
          iapply BigSepL2.bigSepL2_nil.2; iempintro
        isplit
        · iunfold termIntsRO; iexists _; isplit
          · iexact HLedAt
          ipureintro; exact .cons ⟨rfl, rfl⟩ .nil
        isplit
        · iunfold termIntsRO; iexists _; isplit
          · iexact HElAt
          ipureintro; exact .cons ⟨rfl, rfl⟩ .nil
        isplit
        · ipureintro; rfl
        isplit
        · iunfold undoRO; iexists _; isplit
          · iexact HUndo
          iapply Init0_rep; iapply Init0_preNone
        isplit
        · iunfold pendingRO; iexists _; isplit
          · iexact HPend
          iapply Init0_rep; iapply Init0_msgsNil
        isplit
        · iunfold queueRO; iexists _; isplit
          · iexact HQueue
          iapply Init0_rep; iapply Init0_qitemsNil
        isplit
        · iunfold readsRO; iexists _; isplit
          · iexact HReads
          iapply Init0_rep; iapply Init0_readRecsNil
        isplit
        · iapply Init0_logNil
        isplit
        · iapply Init0_termIntsNil
        isplit
        · iapply Init0_strsNil
        ipureintro; simp [State.Wf, Hlen.1]

end proof

end AntCheck
end EtcdGrove
end Perennial
