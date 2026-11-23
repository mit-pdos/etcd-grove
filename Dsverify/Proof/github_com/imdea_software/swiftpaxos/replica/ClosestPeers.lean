/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/ClosestPeers.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`r.UpdatePreferredPeerOrder(quorum)` and `r.ComputeClosestPeers()` (`replica/replica.go`),
proved over their callees' specs.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.Conn
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.ClosestPure
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.WriterSpecs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [dlog.Assumptions] [time.Assumptions]
variable [bufio.Assumptions] [net.Assumptions] [net.FieldAssumptions] [io.Assumptions]
  [io.ExtraAssumptions] [errors.Assumptions] [strings.Assumptions] [encoding.binary.Assumptions]

set_option goose.wp.extras true

theorem replica.Replica.UpdatePreferredPeerOrder.wp_proof :
    replica.Replica.UpdatePreferredPeerOrder.spec (hG := hG) := by
  intro r γ γc γm γw N me qsl Q ppsl pp
  wp_start as ⟨#Hrep, Hq, HPP, Hpp, %Hpre⟩
  obtain ⟨hQN, hme, hpp⟩ := Hpre
  ihave #Hr := Hrep
  iunfold replica.isReplica at Hr
  icases Hr with ⟨%lg, %cfgp, %tbl, %pc, %fr, %nid, %ents, %γpc, %pwsl, %alsl, %latsl,
    %pws, %cwm, #Hlg, #Hquiet, #HN, #HId, #HCfg, #Hplain, #HRPC, #Htbl, #HtOk, #HPC, #Hpcbag,
    #HSd, #HLR, #HDt, #HPW, #Hpws, #HAl, #HLat, #HCW, %Hlens, #Hmu⟩
  have hNz : sint.Z (W64 (N : Int)) = N := by
    simp only [W64, sint.Z]; rw [BitVec.toInt_ofInt]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  wp_auto
  wp_apply (wp_slice_make2 (V := w32) (W64 (N : Int))) as %aux ⟨Haux, -⟩
  · ipureintro; omega
  have hNn : sint.nat (W64 (N : Int)) = N := by
    have : sint.nat (W64 (N : Int)) = (sint.Z (W64 (N : Int))).toNat := rfl
    omega
  rw [hNn]
  ihave %HQl := ownSlice_len _ _ _ $$ Hq
  try wp_auto
  rename_i gi_ptr
  irename : (gi_ptr ↦ W64 0) => gi
  have hqn : sint.Z qsl.len = N := by
    have e1 : sint.nat qsl.len = (sint.Z qsl.len).toNat := rfl; omega
  ihave HL : (∃ (k g : w64) (al : List w32) (pv : w32), "i" ∷ i_ptr ↦ k ∗ "gi" ∷ gi_ptr ↦ g ∗
      "p" ∷ p_ptr ↦ pv ∗ "Haux" ∷ aux ↦* al ∗ "Hq" ∷ qsl ↦* Q ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ N ∧ al.length = N ∧
        sint.Z g = ((Q.take (sint.nat k)).filter (fun x => decide (x ≠ me))).length ∧
        al.take (sint.nat g) = (Q.take (sint.nat k)).filter (fun x => decide (x ≠ me)) ∧
        ∀ x ∈ al, x ∈ Q ∨ x = W32 0⌝ : IProp netDistGF) $$ [i gi p Haux Hq]
  · iexists _, _, _, _
    iframe
    ipureintro
    have z0 : sint.Z (W64 0) = 0 := rfl
    have n0 : sint.nat (W64 0) = 0 := rfl
    simp only [z0, n0, List.take_zero, List.filter_nil, List.length_nil, List.length_replicate]
    refine ⟨?_, ?_, ?_, ?_, ?_, fun x hx => Or.inr (List.eq_of_mem_replicate hx)⟩ <;>
      first | omega | simp | rfl
  wp_for HL
  wp_if_destruct
  · obtain ⟨hk0, hkN, hal, hg, htk, hin⟩ := Hk
    cleanup_bool_decide
    have hk : sint.Z k < N := by omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hk0, by omega⟩)]
    obtain ⟨q, hq⟩ : ∃ q, Q[(sint.Z k).toNat]? = some q :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    wp_apply wp_load_slice_index _ _ _ _ q hk0 $$ [Hq] as Hq
    · iframe Hq; ipureintro; exact hq
    have hkn : (sint.Z k).toNat = sint.nat k := rfl
    have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    have hk1z : sint.Z (k + W64 1) = sint.Z k + 1 := by word
    have hstep := cp.take_filter_succ Q (sint.nat k) q (fun x => decide (x ≠ me)) (by rw [← hkn]; exact hq)
    try wp_auto
    wp_if_destruct
    · wp_for_post
      iframe
      iexists _, _, _, _
      iframe
      ipureintro
      rw [hk1, hstep]
      refine ⟨by omega, by omega, hal, ?_, ?_, hin⟩ <;> simp [Hif, hg, htk]
    · ihave %Hauxl := ownSlice_len _ _ _ $$ Haux
      have hauxn : sint.Z aux.len = N := by
        have e1 : sint.nat aux.len = (sint.Z aux.len).toNat := rfl; omega
      have hflen : ((Q.take (sint.nat k)).filter (fun x => decide (x ≠ me))).length ≤ sint.nat k := by
        have := List.length_filter_le (fun x => decide (x ≠ me)) (Q.take (sint.nat k))
        simp at this ⊢; omega
      have hg0 : 0 ≤ sint.Z g := by omega
      have hgN : sint.Z g < N := by
        have : (sint.nat k : Int) = sint.Z k := by
          have : sint.nat k = (sint.Z k).toNat := rfl; omega
        omega
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hg0, by omega⟩)]
      wp_apply wp_store_slice_index _ _ _ _ $$ [Haux] as Haux
      · iframe Haux; ipureintro; exact ⟨hg0, by omega⟩
      have hgn : (sint.Z g).toNat = sint.nat g := rfl
      have hg1 : sint.nat (g + W64 1) = sint.nat g + 1 := by word
      have hg1z : sint.Z (g + W64 1) = sint.Z g + 1 := by word
      try wp_auto
      wp_for_post
      iframe
      iexists _, _, _, _
      iframe
      ipureintro
      rw [hk1, hstep, hg1, hgn, cp.take_set_succ _ _ _ (by omega), htk]
      refine ⟨by omega, by omega, by simp [hal], ?_, ?_, ?_⟩
      · rw [hg1z, hg, List.length_append]; simp [Hif]
      · simp [Hif]
      · intro x hx
        rcases List.mem_or_eq_of_mem_set hx with hx | rfl
        · exact hin x hx
        · left; exact List.mem_of_getElem? hq
  · -- the order's entries not in `aux` yet
    obtain ⟨hk0, hkN, hal, hg, htk, hin⟩ := Hk
    have hkq : sint.nat k = N := by
      have : sint.nat k = (sint.Z k).toNat := rfl; omega
    rw [hkq, ← hQN, List.take_length] at hg htk
    have hflt : (Q.filter (fun x => decide (x ≠ me))).length < Q.length :=
      List.length_filter_lt_length_iff_exists.2 ⟨me, hme, by simp⟩
    have hgn : (sint.Z g).toNat = sint.nat g := rfl
    ihave %Hppl := ownSlice_len _ _ _ $$ Hpp
    ihave HL2 : (∃ (k2 g2 : w64) (al2 : List w32) (pv : w32), "i" ∷ i_ptr ↦ k2 ∗
        "gi" ∷ gi_ptr ↦ g2 ∗ "p" ∷ p_ptr ↦ pv ∗ "Haux" ∷ aux ↦* al2 ∗ "Hpp" ∷ ppsl ↦* pp ∗
        "%Hk2" ∷ ⌜0 ≤ sint.Z k2 ∧ sint.Z k2 ≤ sint.Z ppsl.len ∧ al2.length = N ∧
          0 ≤ sint.Z g2 ∧ sint.Z g2 ≤ N ∧
          (∀ q ∈ Q, q ≠ me → q ∈ al2.take (sint.nat g2)) ∧
          (sint.Z g2 = N → me ∈ al2.take (sint.nat g2)) ∧
          ∀ x ∈ al2, x ∈ Q ∨ x = W32 0⌝ : IProp netDistGF) $$ [i gi p Haux Hpp]
    · iexists _, _, _, _
      iframe
      ipureintro
      refine ⟨by decide, by rw [show sint.Z (W64 0) = 0 from rfl]; omega, hal, by omega,
        by omega, ?_, ?_, hin⟩
      · intro q hq hne; rw [htk]; simp [hq, hne]
      · intro h; omega
    wp_for HL2
    wp_if_destruct
    · cleanup_bool_decide
      obtain ⟨h0, h1, hal2, hg0, hgN, hall2, hgme, hin2⟩ := Hk2
      have hpplen : pp.length = (sint.Z ppsl.len).toNat := by
        have : sint.nat ppsl.len = (sint.Z ppsl.len).toNat := rfl; omega
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨h0, Hif⟩)]
      obtain ⟨q, hq⟩ : ∃ q, pp[(sint.Z k2).toNat]? = some q :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      wp_apply wp_load_slice_index _ _ _ _ q h0 $$ [Hpp] as Hpp
      · iframe Hpp; ipureintro; exact hq
      have hqQ : q ∈ Q := hpp q (List.mem_of_getElem? hq)
      ihave %Hauxl := ownSlice_len _ _ _ $$ Haux
      have hauxn : sint.Z aux.len = N := by
        have e1 : sint.nat aux.len = (sint.Z aux.len).toNat := rfl; omega
      have hk21 : sint.Z (k2 + W64 1) = sint.Z k2 + 1 := by word
      try wp_auto
      ihave HL3 : (∃ (jv : w64), "j" ∷ j_ptr ↦ jv ∗ "found" ∷ found_ptr ↦ false ∗
          "%Hj" ∷ ⌜0 ≤ sint.Z jv ∧ sint.Z jv ≤ sint.Z g2 ∧ q ∉ al2.take (sint.nat jv)⌝ :
          IProp netDistGF) $$ [j found]
      · iexists _; iframe; ipureintro
        exact ⟨by decide, by rw [show sint.Z (W64 0) = 0 from rfl]; omega,
          by rw [show sint.nat (W64 0) = 0 from rfl]; simp⟩
      wp_for HL3
      wp_if_destruct
      · cleanup_bool_decide
        obtain ⟨hj0, hjg, hjq⟩ := Hj
        have hjlt : sint.Z jv < sint.Z g2 := by simpa using Hif
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hj0, by omega⟩)]
        obtain ⟨y, hy⟩ : ∃ y, al2[(sint.Z jv).toNat]? = some y :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        wp_apply wp_load_slice_index _ _ _ _ y hj0 $$ [Haux] as Haux
        · iframe Haux; ipureintro; exact hy
        try wp_auto
        wp_if_destruct
        · -- found
          try wp_auto
          wp_for_post
          wp_for_post
          iframe
          iexists _, _, _, _
          iframe
          ipureintro
          exact ⟨by omega, by omega, hal2, hg0, hgN, hall2, hgme, hin2⟩
        · try wp_auto
          wp_for_post
          iframe
          iexists _
          iframe
          ipureintro
          have hj1 : sint.nat (jv + W64 1) = sint.nat jv + 1 := by word
          have hj1z : sint.Z (jv + W64 1) = sint.Z jv + 1 := by word
          have hjn : (sint.Z jv).toNat = sint.nat jv := rfl
          refine ⟨by omega, by omega, ?_⟩
          rw [hj1, List.take_add_one, ← hjn, hy]
          simp only [Option.toList_some, List.mem_append, List.mem_singleton, not_or]
          exact ⟨by rw [hjn]; exact hjq, fun h => Hif (h ▸ rfl)⟩
      · -- not found: `q` is `me`
        cleanup_bool_decide
        obtain ⟨hj0, hjg, hjq⟩ := Hj
        have hjge : ¬ sint.Z jv < sint.Z g2 := by simpa using Hif
        have hjeq : sint.nat jv = sint.nat g2 := by
          have : sint.nat jv = (sint.Z jv).toNat := rfl
          have : sint.nat g2 = (sint.Z g2).toNat := rfl
          omega
        rw [hjeq] at hjq
        have hqme : q = me :=
          Classical.byContradiction fun hne => hjq (hall2 q hqQ hne)
        subst hqme
        have hgN' : sint.Z g2 < N := by
          rcases Int.lt_or_eq_of_le hgN with h | h
          · exact h
          · exact absurd (hgme h) hjq
        try wp_auto
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hg0, by omega⟩)]
        wp_apply wp_store_slice_index _ _ _ _ $$ [Haux] as Haux
        · iframe Haux; ipureintro; exact ⟨hg0, by omega⟩
        have hg2n : (sint.Z g2).toNat = sint.nat g2 := rfl
        have hg1 : sint.nat (g2 + W64 1) = sint.nat g2 + 1 := by word
        have hg1z : sint.Z (g2 + W64 1) = sint.Z g2 + 1 := by word
        try wp_auto
        wp_for_post
        iframe
        iexists _, _, _, _
        iframe
        ipureintro
        rw [hg1, hg2n, cp.take_set_succ _ _ _ (by omega)]
        refine ⟨by omega, by omega, by simp [hal2], by omega, by omega, ?_, ?_, ?_⟩
        · intro x hx hne; exact List.mem_append_left _ (hall2 x hx hne)
        · intro _; simp
        · intro x hx
          rcases List.mem_or_eq_of_mem_set hx with hx | rfl
          · exact hin2 x hx
          · left; exact hqQ
    · obtain ⟨h0, h1, hal2, hg0, hgN, hall2, hgme, hin2⟩ := Hk2
      wp_apply sync.Mutex.wp_Lock $$ [] as ⟨Hlocked, HR⟩
      · iexact Hmu
      try wp_auto
      wp_apply sync.Mutex.wp_Unlock $$ [Hlocked HR]
      · iframe Hmu Hlocked
        inext; iexact HR
      try wp_auto
      iapply HΦ
      iexists aux, al2
      iframe
      ipureintro; exact ⟨hal2, hin2⟩

theorem cp_add1_w64 (k : w64) (h0 : 0 ≤ sint.Z k) (h1 : sint.Z k < 1000) :
    sint.Z (k + W64 1) = sint.Z k + 1 := by word

theorem cp_add1_w32 (k : w32) (h0 : 0 ≤ sint.Z k) (h1 : sint.Z k < 1000) :
    sint.Z (k + W32 1) = sint.Z k + 1 := by word

theorem cp_sub1 (N : Nat) (h : 1 ≤ N) (h2 : N ≤ 7) :
    sint.Z (W64 (N : Int) - W64 1) = (N : Int) - 1 := by word

/-! The facts about `W64 N`, `W32 (sint.Z (W64 N))`, `W64 N - W64 1` are kept out of the main
proof's context: `omega` expands every `BitVec.toInt (BitVec.ofInt ..)` it finds there into
`Int.bmod` problems over `2^64`, and with several of them in scope each of the proof's many
`omega` calls cost seconds and GBs (the file grew past 24 GB). -/
theorem cp_Nz (N : Nat) (h : N ≤ 7) : sint.Z (W64 (N : Int)) = N := by
  simp only [W64, sint.Z]; rw [BitVec.toInt_ofInt]
  exact Int.bmod_eq_of_le (by omega) (by omega)

theorem cp_N32 (N : Nat) (h : N ≤ 7) : sint.Z (W32 (sint.Z (W64 (N : Int)))) = N := by
  rw [cp_Nz N h]; simp only [W32, sint.Z]; rw [BitVec.toInt_ofInt]
  exact Int.bmod_eq_of_le (by omega) (by omega)

theorem cp_Nn (N : Nat) (h : N ≤ 7) : sint.nat (W64 (N : Int)) = N := by
  have := cp_Nz N h
  have : sint.nat (W64 (N : Int)) = (sint.Z (W64 (N : Int))).toNat := rfl
  omega

theorem cp_N1n (N : Nat) (h : 1 ≤ N) (h2 : N ≤ 7) : sint.nat (W64 (N : Int) - W64 1) = N - 1 := by
  have := cp_sub1 N h h2
  have : sint.nat (W64 (N : Int) - W64 1) = (sint.Z (W64 (N : Int) - W64 1)).toNat := rfl
  omega

set_option maxHeartbeats 2000000 in
theorem replica.Replica.ComputeClosestPeers.wp_proof
    (wp_SendBeacon : replica.Replica.SendBeacon.spec (hG := hG))
    (wp_Update : replica.Replica.UpdatePreferredPeerOrder.spec (hG := hG))
    (wp_Println : dlog.Logger.Println.spec (GF := netDistGF) (hG := hG)) :
    replica.Replica.ComputeClosestPeers.spec (hG := hG) := by
  intro r γ γc γm γw N me ppsl pp
  wp_start as ⟨#Hrep, HPP, Hpp, %Hpp0⟩
  ihave #Hr := Hrep
  iunfold replica.isReplica at Hr
  icases Hr with ⟨%lg, %cfgp, %tbl, %pc, %fr, %nid, %ents, %γpc, %pwsl, %alsl, %latsl,
    %pws, %cwm, #Hlg, #Hquiet, #HN, #HId, #HCfg, #Hplain, #HRPC, #Htbl, #HtOk, #HPC, #Hpcbag,
    #HSd, #HLR, #HDt, #HPW, #Hpws, #HAl, #HLat, #HCW, %Hlens, #Hmu⟩
  obtain ⟨hpws, hme0, hmeN, hN7⟩ := Hlens
  iclear Hplain Htbl HtOk HPC Hpcbag HCfg HRPC HSd HLR HPW Hpws HCW
  wp_auto
  -- 20 rounds of beacons
  ihave HL : (∃ jv : w64, "j" ∷ j_ptr ↦ jv : IProp netDistGF) $$ [j]
  · iexists _; iexact j
  wp_for HL
  wp_if_destruct
  · ihave HL2 : (∃ iv : w32, "i" ∷ i_ptr ↦ iv ∗ "%Hiv" ∷ ⌜0 ≤ sint.Z iv⌝ : IProp netDistGF) $$ [i]
    · iexists _; iframe; ipureintro; decide
    wp_for HL2
    wp_if_destruct
    · cleanup_bool_decide
      rw [cp_N32 N hN7] at Hif
      wp_if_destruct
      · wp_for_post
        iframe; iexists _; iframe; ipureintro
        have : sint.Z (iv + W32 1) = sint.Z iv + 1 := cp_add1_w32 iv Hiv (by omega)
        omega
      · wp_apply sync.Mutex.wp_Lock $$ [] as ⟨Hlocked, HR⟩
        · iexact Hmu
        iunfold replica.lockInv at HR
        icases HR with ⟨%alive, %lats, Hal, Hlat, %Hl, Hpw, Hcw⟩
        ihave %Hall := ownSlice_len _ _ _ $$ Hal
        ihave %Hlatl := ownSlice_len _ _ _ $$ Hlat
        have hlen : sint.Z alsl.len = N := by
          obtain ⟨h1, h2⟩ := Hall; rw [Hl.1] at h1
          have e1 : sint.nat alsl.len = (sint.Z alsl.len).toNat := rfl
          omega
        have hlen2 : sint.Z latsl.len = N := by
          obtain ⟨h1, h2⟩ := Hlatl; rw [Hl.2] at h1
          have e1 : sint.nat latsl.len = (sint.Z latsl.len).toNat := rfl
          omega
        have hivz : sint.Z (W64 (sint.Z iv)) = sint.Z iv := by
          simp only [W64, sint.Z]; rw [BitVec.toInt_ofInt]
          have : sint.Z iv = iv.toInt := rfl
          exact Int.bmod_eq_of_le (by omega) (by omega)
        try wp_auto
        rw [hivz, ite_eq_left_of_eq_true _ _ (eq_true ⟨Hiv, by omega⟩)]
        have hivn : (sint.Z iv).toNat < alive.length := by omega
        wp_apply wp_load_slice_index _ _ _ _ alive[(sint.Z iv).toNat] Hiv $$ [Hal] as Hal
        · iframe Hal; ipureintro; exact List.getElem?_eq_getElem hivn
        have hiv1 : sint.Z (iv + W32 1) = sint.Z iv + 1 := cp_add1_w32 iv Hiv (by omega)
        cases hb : alive[(sint.Z iv).toNat]
        · try wp_pures
          try wp_auto
          rw [hivz, ite_eq_left_of_eq_true _ _ (eq_true ⟨Hiv, by omega⟩)]
          wp_apply wp_store_slice_index _ _ _ _ $$ [Hlat] as Hlat
          · iframe Hlat; ipureintro; exact ⟨Hiv, by omega⟩
          try wp_auto
          wp_apply sync.Mutex.wp_Unlock $$ [Hlocked Hal Hlat Hpw Hcw]
          · iframe Hmu Hlocked
            inext; unfold replica.lockInv
            iexists alive, _
            iframe
            ipureintro; simp; omega
          try wp_auto
          wp_for_post
          iframe; iexists _; iframe; ipureintro; omega
        · try wp_pures
          try wp_auto
          wp_apply sync.Mutex.wp_Unlock $$ [Hlocked Hal Hlat Hpw Hcw]
          · iframe Hmu Hlocked
            inext; unfold replica.lockInv
            iexists alive, lats
            iframe
            ipureintro; exact Hl
          try wp_auto
          wp_apply wp_SendBeacon r γ γc γm γw N me iv $$ [$Hrep]
          · ipureintro; exact ⟨Hiv, by omega⟩
          wp_for_post
          iframe; iexists _; iframe; ipureintro; omega
    · try wp_auto
      wp_apply time.wp_Sleep
      try wp_auto
      wp_for_post
      iframe; iexists _; iframe
  · -- the ranking, on a copy of the latencies taken under `r.M`
    clear Hif
    try wp_auto
    wp_apply (wp_slice_make2 (V := w32) (W64 (N : Int))) as %qsl ⟨Hqs, -⟩
    · ipureintro; have := cp_Nz N hN7; omega
    rw [cp_Nn N hN7]
    try wp_auto
    wp_apply (wp_slice_make2 (V := w64) (W64 (N : Int))) as %lsl ⟨Hls, -⟩
    · ipureintro; have := cp_Nz N hN7; omega
    rw [cp_Nn N hN7]
    try wp_auto
    wp_apply sync.Mutex.wp_Lock $$ [] as ⟨Hlocked, HR⟩
    · iexact Hmu
    iunfold replica.lockInv at HR
    icases HR with ⟨%alive, %lats, Hal, Hlat, %Hl, Hpw, Hcw⟩
    try wp_auto
    wp_apply (wp_slice_copy (V := w64)) $$ [Hls Hlat] as %n ⟨-, Hls, Hlat⟩
    · iframe
    have hcp : lats.take (List.replicate N (Perennial.zero_val w64)).length ++
        (List.replicate N (Perennial.zero_val w64)).drop lats.length = lats := by
      rw [List.length_replicate, ← Hl.2, List.take_length, List.drop_replicate, Nat.sub_self,
        List.replicate_zero, List.append_nil]
    rw [hcp]
    ihave %Hlsl := ownSlice_len _ _ _ $$ Hls
    ihave %Hqsl := ownSlice_len _ _ _ $$ Hqs
    have hlsn : sint.Z lsl.len = N := by
      have e1 : sint.nat lsl.len = (sint.Z lsl.len).toNat := rfl; omega
    have hqsn : sint.Z qsl.len = N := by
      have e1 : sint.nat qsl.len = (sint.Z qsl.len).toNat := rfl; simp at Hqsl; omega
    try wp_auto
    obtain ⟨v, hv⟩ : ∃ v : Nat → Int, v = fun j => sint.Z (lats.getD j 0) := ⟨_, rfl⟩
    have hlatsN : lats.length = N := Hl.2
    ihave HRk : (∃ (iv : w32) (qs : List w32), "i" ∷ i_ptr ↦ iv ∗ "Hqs" ∷ qsl ↦* qs ∗
        "%Hq" ∷ ⌜0 ≤ sint.Z iv ∧ sint.Z iv ≤ N ∧ qs.length = N ∧
          (∀ i' < (sint.Z iv).toNat, qs[cp.rank v N i']? = some (W32 (i' : Int))) ∧
          ∀ x ∈ qs, x = W32 0 ∨ ∃ k < N, x = W32 (k : Int)⌝ : IProp netDistGF) $$ [i Hqs]
    · iexists _, _; iframe; ipureintro
      refine ⟨by decide, by rw [show sint.Z (W32 0) = 0 from rfl]; omega, by simp, ?_, ?_⟩
      · intro i' hi'; rw [show sint.Z (W32 0) = 0 from rfl] at hi'; omega
      · intro x hx; left; exact List.eq_of_mem_replicate hx
    wp_for HRk
    wp_if_destruct
    · cleanup_bool_decide
      rw [cp_N32 N hN7] at Hif
      obtain ⟨hi0, hiN, hqlen, hqrank, hqin⟩ := Hq
      try wp_auto
      ihave HJ : (∃ (jv : w32) (pv : w64), "j" ∷ j_ptr ↦ jv ∗ "pos" ∷ pos_ptr ↦ pv ∗
          "%Hj" ∷ ⌜0 ≤ sint.Z jv ∧ sint.Z jv ≤ N ∧ sint.Z pv = ((List.range (sint.Z jv).toNat).filter
            (fun k => cp.before v k (sint.Z iv).toNat)).length⌝ : IProp netDistGF) $$ [j pos]
      · iexists _, _; iframe; ipureintro
        refine ⟨by decide, by rw [show sint.Z (W32 0) = 0 from rfl]; omega, ?_⟩
        rw [show sint.Z (W32 0) = 0 from rfl]; simp
      wp_for HJ
      wp_if_destruct
      · cleanup_bool_decide
        rw [cp_N32 N hN7] at Hif
        obtain ⟨hj0, hjN, hpv⟩ := Hj
        have hjz : sint.Z (W64 (sint.Z jv)) = sint.Z jv := by
          simp only [W64, sint.Z]; rw [BitVec.toInt_ofInt]
          have : sint.Z jv = jv.toInt := rfl
          exact Int.bmod_eq_of_le (by omega) (by omega)
        have hiz : sint.Z (W64 (sint.Z iv)) = sint.Z iv := by
          simp only [W64, sint.Z]; rw [BitVec.toInt_ofInt]
          have : sint.Z iv = iv.toInt := rfl
          exact Int.bmod_eq_of_le (by omega) (by omega)
        obtain ⟨a, ha⟩ : ∃ a, lats[(sint.Z jv).toNat]? = some a :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        obtain ⟨b, hb⟩ : ∃ b, lats[(sint.Z iv).toNat]? = some b :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have hva : v (sint.Z jv).toNat = sint.Z a := by rw [hv]; simp [List.getD_eq_getElem?_getD, ha]
        have hvb : v (sint.Z iv).toNat = sint.Z b := by rw [hv]; simp [List.getD_eq_getElem?_getD, hb]
        have hstep := cp.rank_step v (sint.Z jv).toNat (sint.Z iv).toNat
        have hj1 : sint.Z (jv + W32 1) = sint.Z jv + 1 := cp_add1_w32 jv hj0 (by omega)
        have hj1n : (sint.Z (jv + W32 1)).toNat = (sint.Z jv).toNat + 1 := by omega
        have hrl := cp.rank_le v (sint.Z jv).toNat (sint.Z iv).toNat
        rw [hjz, ite_eq_left_of_eq_true _ _ (eq_true ⟨hj0, by omega⟩)]
        wp_apply wp_load_slice_index _ _ _ _ a hj0 $$ [Hls] as Hls
        · iframe Hls; ipureintro; exact ha
        try wp_auto
        rw [hiz, ite_eq_left_of_eq_true _ _ (eq_true ⟨hi0, by omega⟩)]
        wp_apply wp_load_slice_index _ _ _ _ b hi0 $$ [Hls] as Hls
        · iframe Hls; ipureintro; exact hb
        try wp_auto
        have hpv1 : sint.Z (pv + W64 1) = sint.Z pv + 1 := cp_add1_w64 pv (by omega) (by omega)
        have hza : ∀ x y : w64, x ≠ y → sint.Z x ≠ sint.Z y :=
          fun x y h h' => h (BitVec.eq_of_toInt_eq h')
        wp_if_destruct
        · -- `lats[j] < lats[i]`
          have hbt : cp.before v (sint.Z jv).toNat (sint.Z iv).toNat = true := by
            simp only [cp.before, hva, hvb, Bool.or_eq_true, decide_eq_true_eq]; left; exact Hif
          try wp_auto
          wp_for_post
          iframe; iexists _, _; iframe; ipureintro
          refine ⟨by omega, by omega, ?_⟩
          rw [hj1n, hstep, hbt, hpv1, hpv]; simp
        · have Hlt : ¬ sint.Z a < sint.Z b := Hif
          try wp_auto
          rw [hjz, ite_eq_left_of_eq_true _ _ (eq_true ⟨hj0, by omega⟩)]
          wp_apply wp_load_slice_index _ _ _ _ a hj0 $$ [Hls] as Hls
          · iframe Hls; ipureintro; exact ha
          try wp_auto
          rw [hiz, ite_eq_left_of_eq_true _ _ (eq_true ⟨hi0, by omega⟩)]
          wp_apply wp_load_slice_index _ _ _ _ b hi0 $$ [Hls] as Hls
          · iframe Hls; ipureintro; exact hb
          try wp_auto
          wp_if_destruct
          · -- equal latencies: by index
            subst Hif
            try wp_auto
            wp_if_destruct
            · have hbt : cp.before v (sint.Z jv).toNat (sint.Z iv).toNat = true := by
                simp only [cp.before, hva, hvb, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
                right; exact ⟨trivial, by omega⟩
              try wp_auto
              wp_for_post
              iframe; iexists _, _; iframe; ipureintro
              refine ⟨by omega, by omega, ?_⟩
              rw [hj1n, hstep, hbt, hpv1, hpv]; simp
            · have hbt : cp.before v (sint.Z jv).toNat (sint.Z iv).toNat = false := by
                simp only [cp.before, hva, hvb, Bool.or_eq_false_iff, Bool.and_eq_false_imp,
                  decide_eq_false_iff_not, decide_eq_true_eq]
                exact ⟨Int.lt_irrefl _, fun _ => by omega⟩
              try wp_auto
              wp_for_post
              iframe; iexists _, _; iframe; ipureintro
              refine ⟨by omega, by omega, ?_⟩
              rw [hj1n, hstep, hbt, hpv]; simp
          · have hbt : cp.before v (sint.Z jv).toNat (sint.Z iv).toNat = false := by
              simp only [cp.before, hva, hvb, Bool.or_eq_false_iff, Bool.and_eq_false_imp,
                decide_eq_false_iff_not, decide_eq_true_eq]
              exact ⟨Hlt, fun h => absurd h (hza a b Hif)⟩
            try wp_auto
            wp_for_post
            iframe; iexists _, _; iframe; ipureintro
            refine ⟨by omega, by omega, ?_⟩
            rw [hj1n, hstep, hbt, hpv]; simp
      · -- `quorum[pos] = i`
        cleanup_bool_decide
        rw [cp_N32 N hN7] at Hif
        obtain ⟨hj0, hjN, hpv⟩ := Hj
        have hjN' : (sint.Z jv).toNat = N := by omega
        rw [hjN'] at hpv
        have hin : (sint.Z iv).toNat < N := by omega
        have hrk := cp.rank_lt v N _ hin
        have hpvr : sint.Z pv = cp.rank v N (sint.Z iv).toNat := hpv
        try wp_auto
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩)]
        wp_apply wp_store_slice_index _ _ _ _ $$ [Hqs] as Hqs
        · iframe Hqs; ipureintro; exact ⟨by omega, by omega⟩
        have hi1 : sint.Z (iv + W32 1) = sint.Z iv + 1 := cp_add1_w32 iv hi0 (by omega)
        have hivw : W32 (((sint.Z iv).toNat : Nat) : Int) = iv := by
          apply BitVec.eq_of_toInt_eq
          simp only [W32]; rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le (by omega) (by omega)]
          have : sint.Z iv = iv.toInt := rfl
          omega
        have hpvn : (sint.Z pv).toNat = cp.rank v N (sint.Z iv).toNat := by omega
        try wp_auto
        wp_for_post
        iframe; iexists _, _; iframe; ipureintro
        rw [hpvn]
        refine ⟨by omega, by omega, by simp [hqlen], ?_, ?_⟩
        · intro i' hi'
          rw [List.getElem?_set]
          by_cases he : i' = (sint.Z iv).toNat
          · subst he; rw [if_pos rfl, if_pos (by omega), hivw]
          · rw [ite_eq_right_iff.2 (fun h => absurd h (cp.rank_inj v N _ _ hin (by omega) (Ne.symm he)))]
            exact hqrank i' (by omega)
        · intro x hx
          rcases List.mem_or_eq_of_mem_set hx with hx | rfl
          · exact hqin x hx
          · right; exact ⟨_, hin, hivw.symm⟩
    · cleanup_bool_decide
      rw [cp_N32 N hN7] at Hif
      obtain ⟨hi0, hiN, hqlen, hqrank, hqin⟩ := Hq
      have hiN' : (sint.Z iv).toNat = N := by omega
      rw [hiN'] at hqrank
      have hmemQ : ∀ p : w32, 0 ≤ p.toInt → p.toInt < N → p ∈ qs := by
        intro p h0 h1
        have h := hqrank p.toInt.toNat (by omega)
        have hw : W32 ((p.toInt.toNat : Nat) : Int) = p := by
          apply BitVec.eq_of_toInt_eq
          simp only [W32]; rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le (by omega) (by omega)]
          omega
        rw [hw] at h
        exact List.mem_of_getElem? h
      wp_apply sync.Mutex.wp_Unlock $$ [Hlocked Hal Hlat Hpw Hcw]
      · iframe Hmu Hlocked
        inext; unfold replica.lockInv
        iexists alive, lats
        iframe
        ipureintro; exact Hl
      try wp_auto
      wp_apply wp_Update r γ γc γm γw N me qsl qs ppsl pp $$ [$Hrep $Hqs $HPP $Hpp]
        as ⟨%ppsl', %pp', Hqs, Hpp, HPP, Hpp', %Hpp'⟩
      · ipureintro
        exact ⟨hqlen, hmemQ me hme0 hmeN, fun p hp => hmemQ p (Hpp0 p hp).1 (Hpp0 p hp).2⟩
      have hw32 : ∀ k : Nat, k < N → (W32 (k : Int)).toInt = k := by
        intro k hk
        simp only [W32]; rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le (by omega) (by omega)]
      have hrange : ∀ x ∈ pp', 0 ≤ x.toInt ∧ x.toInt < N := by
        intro x hx
        rcases Hpp'.2 x hx with hx | rfl
        · rcases hqin x hx with rfl | ⟨k, hk, rfl⟩
          · exact ⟨by decide, by rw [show (W32 0).toInt = 0 from rfl]; omega⟩
          · rw [hw32 k hk]; omega
        · exact ⟨by decide, by rw [show (W32 0).toInt = 0 from rfl]; omega⟩
      -- `omega` case-splits on every `Int.toNat`/`sint.nat` fact in scope: drop the stale ones
      clear hqrank hmemQ hw32 Hif hi0 hiN hiN' Hlsl Hqsl hqsn
      wp_apply (wp_slice_make2 (V := w64) (W64 (N : Int) - W64 1)) as %ssl ⟨Hss, -⟩
      · ipureintro; have := cp_sub1 N (by omega) hN7; omega
      rw [cp_N1n N (by omega) hN7]
      ihave %Hssl := ownSlice_len _ _ _ $$ Hss
      have hssn : sint.Z ssl.len = N - 1 := by
        have e1 : sint.nat ssl.len = (sint.Z ssl.len).toNat := rfl; simp at Hssl; omega
      ihave %Hppl' := ownSlice_len _ _ _ $$ Hpp'
      have hppn : sint.Z ppsl'.len = N := by
        have e1 : sint.nat ppsl'.len = (sint.Z ppsl'.len).toNat := rfl; omega
      clear Hssl Hppl'
      try wp_auto
      ihave HL : (∃ (k : w64) (ls : List w64), "i" ∷ i_ptr ↦ k ∗ "Hss" ∷ ssl ↦* ls ∗
          "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ N - 1 ∧ ls.length = N - 1⌝ : IProp netDistGF)
        $$ [i Hss]
      · iexists _, _; iframe; ipureintro
        exact ⟨by decide, by rw [show sint.Z (W64 0) = 0 from rfl]; omega, by simp⟩
      wp_for HL
      wp_if_destruct
      · cleanup_bool_decide
        obtain ⟨hk0, hkN, hls⟩ := Hk
        rw [cp_sub1 N (by omega) hN7] at Hif
        have hkN1 : sint.Z k < N - 1 := Hif
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hk0, by omega⟩)]
        have hpl : pp'.length = N := Hpp'.1
        have hkn' : (sint.Z k).toNat < pp'.length := by rw [hpl]; omega
        obtain ⟨nd, hnd⟩ : ∃ nd, pp'[(sint.Z k).toNat]? = some nd :=
          ⟨_, List.getElem?_eq_getElem hkn'⟩
        clear hkn'
        have hndr := hrange nd (List.mem_of_getElem? hnd)
        have hndr' : 0 ≤ sint.Z nd ∧ sint.Z nd < N := hndr
        wp_apply wp_load_slice_index _ _ _ _ nd hk0 $$ [Hpp'] as Hpp'
        · iframe Hpp'; ipureintro; exact hnd
        have hndz : sint.Z (W64 (sint.Z nd)) = sint.Z nd := by
          simp only [W64, sint.Z]; rw [BitVec.toInt_ofInt]
          have : sint.Z nd = nd.toInt := rfl
          exact Int.bmod_eq_of_le (by omega) (by omega)
        try wp_auto
        rw [hndz, ite_eq_left_of_eq_true _ _ (eq_true ⟨hndr'.1, by omega⟩)]
        clear hndz
        have hndn : (sint.Z nd).toNat < lats.length := by rw [hlatsN]; omega
        obtain ⟨lv, hlv⟩ : ∃ lv, lats[(sint.Z nd).toNat]? = some lv :=
          ⟨_, List.getElem?_eq_getElem hndn⟩
        clear hndn
        wp_apply wp_load_slice_index _ _ _ _ lv hndr'.1 $$ [Hls] as Hls
        · iframe Hls; ipureintro; exact hlv
        try wp_auto
        wp_apply wp_slice_literal (V := GoInterface)
        isplitr
        · ipureintro; rfl
        iintro %s1 ⟨-, -⟩
        try wp_auto
        wp_apply replica.wp_Println wp_Println $$ [$Hlg $Hquiet]
        try wp_auto
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hk0, by omega⟩)]
        wp_apply wp_store_slice_index _ _ _ _ $$ [Hss] as Hss
        · iframe Hss; ipureintro; exact ⟨hk0, by omega⟩
        have hk1 : sint.Z (k + W64 1) = sint.Z k + 1 := cp_add1_w64 k hk0 (by omega)
        try wp_auto
        wp_for_post
        iframe; iexists _, _; iframe; ipureintro
        exact ⟨by omega, by omega, by simp [hls]⟩
      · obtain ⟨hk0, hkN, hls⟩ := Hk
        try wp_auto
        iapply HΦ
        iexists ls, ppsl', pp'
        iframe
        ipureintro; exact ⟨hls, Hpp'.1, hrange⟩

end proof

end Perennial.github_com.imdea_software.swiftpaxos
