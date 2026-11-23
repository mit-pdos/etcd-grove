/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/New.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`replica.New`'s proof (internal spec `Proof/replica/NewSpec.lean`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.NewSpec
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.rpc.Table

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions] [state.Assumptions]

set_option goose.wp.extras true

/-- `(id + 1 + i) % N` (New's `PreferredPeerOrder` entries) is an id. -/
theorem replica.rot_bound (id iv len : w64) (L : Nat) (h0 : 0 ≤ sint.Z id) (h1 : sint.Z id < L) (hL : L ≤ 7)
    (hi0 : 0 ≤ sint.Z iv) (hi : sint.Z iv < L) (hlen : sint.Z len = L) :
    0 ≤ (W32 (sint.Z (BitVec.srem (W64 (sint.Z (W32 (sint.Z id))) + W64 1 + iv) len))).toInt ∧
    (W32 (sint.Z (BitVec.srem (W64 (sint.Z (W32 (sint.Z id))) + W64 1 + iv) len))).toInt < L := by
  have e1 : W64 (sint.Z (W32 (sint.Z id))) = id := by word
  rw [e1]
  have hpos : sint.Z (id + W64 1 + iv) = sint.Z id + 1 + sint.Z iv := by word
  have hs : sint.Z (BitVec.srem (id + W64 1 + iv) len) = (sint.Z id + 1 + sint.Z iv) % L := by
    show BitVec.toInt _ = _
    rw [BitVec.toInt_srem]
    show Int.tmod (sint.Z _) (sint.Z _) = _
    rw [hpos, hlen, Int.tmod_eq_emod_of_nonneg (by omega)]
  have a1 := Int.emod_nonneg (sint.Z id + 1 + sint.Z iv) (b := L) (by omega)
  have a2 := Int.emod_lt_of_pos (sint.Z id + 1 + sint.Z iv) (b := L) (by omega)
  have e2 : (W32 (sint.Z (BitVec.srem (id + W64 1 + iv) len))).toInt =
      sint.Z (BitVec.srem (id + W64 1 + iv) len) := by
    simp only [W32]; rw [BitVec.toInt_ofInt, hs]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  rw [e2, hs]; omega


theorem replica.New.wp_proof
    (wp_InitState : state.InitState.spec (GF := netDistGF) (hG := hG))
    (wp_NewTableId : rpc.NewTableId.spec (hG := hG)) :
    replica.New.spec (hG := hG) := by
  intro als id f addrs l thrifty exec lread cfgp lg γ
  wp_start as ⟨#Hl, %Hid, #HLC⟩
  ihave %Hll := ownSlice_len _ _ _ $$ Hl
  wp_auto
  have hN : sint.Z addrs.len = l.length := by
    have := Hll.1; have := Hll.2
    have e1 : sint.nat addrs.len = (sint.Z addrs.len).toNat := rfl
    omega
  wp_apply (wp_slice_make2 (V := GoInterface) addrs.len) as %peers ⟨Hpeers, -⟩
  · ipureintro; omega
  try wp_auto
  wp_apply (wp_slice_make2 (V := Loc) addrs.len) as %rds ⟨Hrds, -⟩
  · ipureintro; omega
  try wp_auto
  wp_apply (wp_slice_make2 (V := Loc) addrs.len) as %wrs ⟨Hwrs, -⟩
  · ipureintro; omega
  try wp_auto
  wp_apply (wp_map_make1 (K := w32) (V := Loc)) as %cwm Hcwm
  try wp_auto
  wp_apply (wp_slice_make2 (V := Bool) addrs.len) as %als ⟨Hals, -⟩
  · ipureintro; omega
  try wp_auto
  wp_apply (wp_slice_make2 (V := w32) addrs.len) as %ppo ⟨Hppo, -⟩
  · ipureintro; omega
  try wp_auto
  wp_apply wp_InitState as %st Hst
  try wp_auto
  wp_apply wp_NewTableId as %tbl Htbl
  try wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := w64)) as %stm Hstm
  try wp_auto
  wp_apply (chan.wp_make2 (V := Loc) (W64 2000000)) as %pc %γpc ⟨#Hpc, -, Hpco⟩
  · ipureintro; decide
  ihave Hbag := start_bag (V := Loc) (sp.proposeP γ) (ChanState.Buffered []) pc γpc trivial
    $$ Hpc Hpco
  imod Hbag with #Hbag
  try wp_auto
  wp_apply (chan.wp_make2 (V := Loc) (W64 2000000)) as %bc %γbc ⟨#Hbc, -, Hbco⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (wp_slice_make2 (V := w64) addrs.len) as %ews ⟨Hews, -⟩
  · ipureintro; omega
  try wp_auto
  wp_apply (wp_slice_make2 (V := w64) addrs.len) as %lats ⟨Hlats, -⟩
  · ipureintro; omega
  try wp_auto
  have hn : sint.nat addrs.len = l.length := by
    have e1 : sint.nat addrs.len = (sint.Z addrs.len).toNat := rfl
    omega
  rw [hn] at *
  ihave HL : (∃ (iv : w64), "i" ∷ i_ptr ↦ iv ∗
      "Hppo" ∷ (∃ pps : List w32, ppo ↦* pps ∗
        ⌜pps.length = l.length ∧ ∀ p ∈ pps, 0 ≤ p.toInt ∧ p.toInt < l.length⌝) ∗
      "Hews" ∷ ews ↦* List.replicate l.length (W64 0) ∗
      "Hlats" ∷ lats ↦* List.replicate l.length (W64 0) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z iv ∧ sint.Z iv ≤ l.length⌝ : IProp netDistGF) $$ [i Hppo Hews Hlats]
  · iexists W64 0
    iframe
    isplitl [Hppo]
    · iexists _; iframe; ipureintro
      refine ⟨by simp, ?_⟩
      intro p hp
      simp at hp
      obtain ⟨-, rfl⟩ := hp
      have : (zero_val w32).toInt = 0 := rfl
      have : sint.Z id < l.length := Hid.2.1
      have : sint.Z id = id.toInt := rfl
      omega
    ipureintro; simp
  wp_for HL
  wp_if_destruct
  · -- an iteration
    have hN0 : sint.Z addrs.len ≠ 0 := by omega
    rw [if_neg hN0]
    icases Hppo with ⟨%pps, Hppo, %Hpps⟩
    ihave %Hpl := ownSlice_len _ _ _ $$ Hppo
    ihave %Hel := ownSlice_len _ _ _ $$ Hews
    ihave %Hla := ownSlice_len _ _ _ $$ Hlats
    have hi : sint.Z iv < l.length := by
      have := Hif; word
    wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi.1, by
      have e1 : sint.nat ppo.len = (sint.Z ppo.len).toNat := rfl; omega⟩)]
    wp_apply wp_store_slice_index _ _ _ _ $$ [Hppo] as Hppo
    · iframe Hppo; ipureintro; exact ⟨Hi.1, by omega⟩
    have hrot := replica.rot_bound id iv addrs.len l.length Hid.1 Hid.2.1 Hid.2.2 Hi.1 hi hN
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi.1, by
      have e1 : sint.nat ews.len = (sint.Z ews.len).toNat := rfl; simp at Hel; omega⟩)]
    wp_apply wp_store_slice_index _ _ _ _ $$ [Hews] as Hews
    · iframe Hews; ipureintro; simp; omega
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi.1, by
      have e1 : sint.nat lats.len = (sint.Z lats.len).toNat := rfl; simp at Hla; omega⟩)]
    wp_apply wp_store_slice_index _ _ _ _ $$ [Hlats] as Hlats
    · iframe Hlats; ipureintro; simp; omega
    wp_for_post
    iframe
    iexists (iv + W64 1)
    iframe
    isimp only [List.set_replicate_self] at Hews Hlats
    iframe
    isplitl [Hppo]
    · iexists _; iframe; ipureintro
      refine ⟨by simp [Hpps.1], ?_⟩
      intro p hp
      rcases List.mem_or_eq_of_mem_set hp with hp | hp
      · exact Hpps.2 p hp
      · subst hp; exact hrot
    ipureintro; constructor <;> word
  · icases Hppo with ⟨%pps, Hppo, %Hpps⟩
    iapply HΦ
    unfold replica.created
    iexists _, γpc, pps
    iframe
    simp only []
    iframe
    iframe Hbag
    ipureintro
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, Hpps⟩ <;>
      try first | trivial | rfl
    apply BitVec.eq_of_toInt_eq
    have : (W64 (l.length : Int)).toInt = l.length := by
      simp only [W64]; rw [BitVec.toInt_ofInt]; exact Int.bmod_eq_of_le (by omega) (by omega)
    rw [this]; exact hN

end proof

end Perennial.github_com.imdea_software.swiftpaxos
