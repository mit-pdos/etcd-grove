/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/UpdateLogs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`r.updateLogs(cmd, x, s, hs)` (swift.go; `recordLeaderHash`'s callee) against
`swift.Replica.updateLogs.specT` (RecordLeaderHash.lean; round 19, sv-swc): `keysOf` of a put or
a get is its key, `len(keys) == len(hs) == 1` (no `Fatal`), the key's hash log (a fresh one,
`HL.init`, if none: `hlogOwn`'s "no log, no handled command of the key"), `HashLog.Update`
(`leadUpdOk`: its effect keeps `hlogOk`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecordLeaderHashDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DepHashDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [swift.Assumptions]

set_option goose.wp.extras true

theorem swift.Replica.updateLogs.wp_proof [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
    (wp_keysOf : swift.keysOf.specNS)
    (wp_newHL : swift.hlog.NewHashLog.spec)
    (wp_Update : swift.hlog.HashLog.Update.spec) :
    swift.Replica.updateLogs.specT := by
  intro rp hm hM ld hd K Λ c vs dq x sq hs H P
  wp_start as ⟨Hhf, Hhlog, Hvs, #Hhs, #HP, %Hok⟩
  obtain ⟨hpg, hupd⟩ := Hok
  have hop : c.op ≠ W8 3 := by
    rcases hpg with h | h
    · unfold sp.Cmd.isPut sp.opPUT at h; simp at h; rw [h]; decide
    · unfold sp.Cmd.isGet sp.opGET at h; simp at h; rw [h]; decide
  wp_auto
  wp_apply wp_keysOf $$ [] as %ksl Hksl
  · ipureintro; exact hop
  ihave %Hkl := ownSlice_len _ _ _ $$ Hksl
  ihave %Hhl := ownSlice_len _ _ _ $$ Hhs
  ipersist r
  try wp_auto
  have hk1 : sint.Z ksl.len = 1 := by have := Hkl.1; simp at this; word
  have hh1 : sint.Z hs.len = 1 := by have := Hhl.1; simp at this; word
  rw [decide_eq_true (show ksl.len = hs.len by apply BitVec.eq_of_toInt_eq; simp only [sint.Z] at hk1 hh1; omega)]
  wp_auto
  ihave HL : (∃ (i : w64) (kv : w64),
      "i" ∷ i_ptr ↦ i ∗ "key" ∷ key_ptr ↦ kv ∗
      "HL" ∷ ((⌜i = W64 0⌝ ∗ swift.fld rp go!"hlog" ↦ hm ∗ swift.hlogOwn hm hM ld hd K Λ) ∨
        (⌜i = W64 1⌝ ∗ ∃ hM' : GMap w64 Loc, swift.fld rp go!"hlog" ↦ hm ∗
          swift.hlogOwn hm hM' ld hd K Λ)) : IProp netDistGF)
    $$ [i key Hhf Hhlog]
  · iexists (W64 0), _
    iframe i key
    ileft
    iframe Hhf Hhlog
    ipureintro; rfl
  wp_for HL
  icases HL with (⟨%Hi0, Hhf, Hhlog⟩ | ⟨%Hi1, %hM', Hhf, Hhlog⟩)
  rotate_left
  · subst Hi1
    rw [decide_eq_false (by rw [hk1]; decide)]
    simp only [Bool.false_eq_true, ↓reduceIte]
    wp_auto
    iapply HΦ
    iframe
  subst Hi0
  rw [decide_eq_true (by rw [hk1]; decide)]
  simp only [↓reduceIte]
  wp_auto
  rw [if_pos ⟨by decide, by rw [hk1]; decide⟩]
  wp_apply wp_load_slice_index (t := state.Key.ty) ksl (sint.Z (W64 0)) [c.key] _ c.key (by decide)
    $$ [Hksl] as Hksl
  · iframe Hksl; ipureintro; rfl
  try wp_auto
  iunfold swift.hlogOwn at Hhlog
  icases Hhlog with ⟨HhM, HhE, %Hhcov⟩
  wp_apply wp_map_lookup2 $$ [$HhM] as HhM
  wp_join iprop(∃ (hl : Loc) (hMn : GMap w64 Loc) (σ : swift.hlog.HL),
      key_ptr ↦ c.key ∗ swift.fld rp go!"hlog" ↦ hm ∗ l_ptr ↦ hl ∗ hm ↦$ hMn ∗
      swift.hlog.ownHashLog hl σ ∗ ⌜swift.hlogOk ld hd K Λ c.key σ⌝ ∗
      (swift.hlogEnt ld hd K Λ c.key hl -∗ [∗map] k ↦ l' ∈ hMn, swift.hlogEnt ld hd K Λ k l') ∗
      ⌜∀ k, hMn !! k = none → swift.idsOfKey hd k = []⌝)
    with [key Hhf l HhM HhE] as ⟨%hl, %hMn, %σ, key, Hhf, l, HhM, Hσ, %Hσok, Hhback, %Hhcov'⟩
  · obtain ⟨hl, hsome⟩ := Option.isSome_iff_exists.mp (by simpa using Hif)
    rw [hsome]
    simp only [Option.getD_some]
    try wp_auto
    ihave ⟨He, Hback⟩ := swift.bigSepM_change1 hM c.key hl (swift.hlogEnt ld hd K Λ)
        (swift.hlogEnt ld hd K Λ) hsome (fun _ _ _ => .rfl) $$ HhE
    iunfold swift.hlogEnt at He
    icases He with ⟨%σ, Hσ, %Hσok⟩
    iexists hl, hM, σ
    iframe
    ipureintro; exact ⟨Hσok, Hhcov⟩
  · have hnone : hM !! c.key = none := by simpa using Hif
    have h0 := Hhcov c.key hnone
    wp_apply wp_newHL as %hl Hσ
    try wp_auto
    wp_apply wp_mapInsert $$ [$HhM] as HhM
    try wp_auto
    wp_join_done
    iexists hl, _, swift.hlog.HL.init
    iframe
    isplitr
    · ipureintro; exact swift.hlog.hlogOk_init' ld hd K Λ c.key h0
    isplitl
    · iapply (swift.bigSepM_add1 hM c.key hl (swift.hlogEnt ld hd K Λ)
        (swift.hlogEnt ld hd K Λ) hnone (fun _ _ _ => .rfl)) $$ HhE
    · ipureintro
      intro k hk
      by_cases hkc : c.key = k
      · subst hkc; rw [GMap.lookup_insert] at hk; cases hk
      · rw [GMap.lookup_insert_ne _ _ hkc] at hk
        exact Hhcov k hk
  rw [if_pos ⟨by decide, by rw [hh1]; decide⟩]
  wp_apply wp_load_slice_index (t := swift.SHash.ty) hs (sint.Z (W64 0)) [H] _ H (by decide)
    $$ [Hhs] as -
  · iframe Hhs; ipureintro; rfl
  try wp_auto
  wp_apply (wp_Update hl σ x sq H P) $$ [$Hσ $HP] as Hσ
  try wp_auto
  wp_for_post
  iframe
  iexists (W64 0 + W64 1), c.key
  iframe i key
  iright
  isplitr
  · ipureintro; decide
  iexists hMn
  iframe Hhf
  iunfold swift.hlogOwn
  iframe HhM
  isplitl
  · iapply Hhback
    iunfold swift.hlogEnt
    iexists _
    iframe Hσ
    ipureintro; exact hupd σ Hσok
  · ipureintro; exact Hhcov'

end proofs


end Perennial.github_com.imdea_software.swiftpaxos
