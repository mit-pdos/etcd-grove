/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/DepHash.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`r.getDepAndHashes(cmd, x)` (swift.go) against `swift.Replica.getDepAndHashes.specI`
(RunSpecs.lean), and `keysOf` of a put or a get (key.go).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DepHashPure
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HandleSync
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HashLogSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.KeyDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SliceNN
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DepHashDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS]
variable [swift.Assumptions]

end specs

section helpers
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS]

end helpers

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [swift.Assumptions]

set_option goose.wp.extras true

theorem swift.keysOf.wp_proofNS : swift.keysOf.specNS := by
  intro op k vs
  wp_start as %hop
  wp_auto
  rw [decide_eq_false hop]
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral _))) (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w64) [k]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  iapply HΦ $$ Hsl

theorem swift.Replica.getDepAndHashes.wp_proof [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
    (wp_keysOf : swift.keysOf.specNS)
    (wp_newLKI : swift.lki.newLightKeyInfo.spec)
    (wp_add : swift.lki.lightKeyInfo.add.spec)
    (wp_conf : swift.lki.lightKeyInfo.getConflictCmds.spec)
    (wp_newHL : swift.hlog.NewHashLog.spec)
    (wp_append : swift.hlog.HashLog.Append.spec) :
    swift.Replica.getDepAndHashes.specI := by
  intro rp km hm kM hM s hd ld K Λ x c vs
  wp_start as ⟨Hkf, Hkeys, Hhf, Hhlog, %Hpre⟩
  obtain ⟨hxn, hxK, hpg, hlen⟩ := Hpre
  have hop : c.op ≠ W8 3 := by
    rcases hpg with h | h
    · unfold sp.Cmd.isPut sp.opPUT at h; simp at h; rw [h]; decide
    · unfold sp.Cmd.isGet sp.opGET at h; simp at h; rw [h]; decide
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral _))) (Val (LiteralValueV _)))
  iapply wp_slice_literal_nonnull (V := swift.CommandId) []
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %dptr %Hdptr ⟨Hdsl, Hdcap⟩
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral _))) (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := swift.SHash) []
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %hsl ⟨Hhsl, Hhcap⟩
  wp_auto
  wp_apply wp_keysOf $$ [] as %ksl Hksl
  · ipureintro; exact hop
  ihave %Hkl := ownSlice_len _ _ _ $$ Hksl
  ipersist r
  ipersist cmd
  ipersist cmdId
  ihave HL : (∃ (i : w64) (kv : w64),
      "i" ∷ i_ptr ↦ i ∗ "key" ∷ key_ptr ↦ kv ∗
      "HL" ∷ ((⌜i = W64 0⌝ ∗ swift.keysOwn km kM (s ++ hd) ∗ swift.hlogOwn hm hM ld hd K Λ ∗
          (∃ d0 : GoSlice, ⌜d0.ptr ≠ null⌝ ∗ dep_ptr ↦ d0 ∗ d0 ↦* ([] : List swift.CommandId) ∗
            ownSliceCap swift.CommandId d0 (DFrac.own 1)) ∗
          (∃ h0 : GoSlice, hashes_ptr ↦ h0 ∗ h0 ↦* ([] : List swift.SHash) ∗
            ownSliceCap swift.SHash h0 (DFrac.own 1))) ∨
        (⌜i = W64 1⌝ ∗ ∃ (dp hs : GoSlice) (kM' : GMap w64 GoInterface) (hM' : GMap w64 Loc)
            (P : List sp.CmdId) (H : swift.SHash),
          dep_ptr ↦ dp ∗ hashes_ptr ↦ hs ∗
          swift.keysOwn km kM' (s ++ hd ++ [(toCmdId x, c)]) ∗
          swift.hlogOwn hm hM' ld (hd ++ [(toCmdId x, c)]) K Λ ∗
          dp ↦* ((sp.lkDeps (s ++ hd) c).map ofCmdId) ∗ ownSliceCap swift.CommandId dp (DFrac.own 1) ∗
          hs ↦* [H] ∗ ownSliceCap swift.SHash hs (DFrac.own 1) ∗ sp.startHash P H.H'.arr ∗
          ⌜P.getLast? = some (toCmdId x) ∧
            (ld = true → P = swift.idsOfKey hd c.key ++ [toCmdId x]) ∧
            (∀ z ∈ swift.idsOfKey hd c.key, z ∈ P)⌝ ∗ ⌜dp ≠ slice.nil ∧ hs ≠ slice.nil⌝)) :
          IProp netDistGF)
    $$ [i key Hkeys Hhlog dep Hdsl Hdcap hashes Hhsl Hhcap]
  · iexists (W64 0), _
    iframe i key
    ileft
    iframe Hkeys Hhlog
    isplitr
    · ipureintro; rfl
    isplitl [dep Hdsl Hdcap]
    · iexists _; iframe; ipureintro; exact Hdptr
    · iexists _; iframe
  wp_for HL
  have hlen1 : sint.Z ksl.len = 1 := by
    have := Hkl.1; simp at this; word
  icases HL with (⟨%Hi0, Hkeys, Hhlog, ⟨%d0, %Hd0p, dep, Hd0, Hd0c⟩, ⟨%h0, hashes, Hh0, Hh0c⟩⟩ |
    ⟨%Hi1, %dp, %hs, %kM', %hM', %P, %H, dep, hashes, Hkeys, Hhlog, Hdp, Hdpc, Hhs, Hhsc, #HP, %HPok,
      %Hnn⟩)
  rotate_left
  · -- after the key: the loop ends
    subst Hi1
    rw [decide_eq_false (by rw [hlen1]; decide)]
    simp only [Bool.false_eq_true, ↓reduceIte]
    wp_auto
    iapply HΦ
    iframe
    isplitr
    · iexact HP
    isplitr
    · ipureintro; exact HPok
    ipureintro; exact Hnn
  subst Hi0
  rw [decide_eq_true (by rw [hlen1]; decide)]
  simp only [↓reduceIte]
  wp_auto
  rw [if_pos ⟨by decide, by rw [hlen1]; decide⟩]
  wp_apply wp_load_slice_index (t := state.Key.ty) ksl (sint.Z (W64 0)) [c.key] _ c.key (by decide)
    $$ [Hksl] as Hksl
  · iframe Hksl; ipureintro; rfl
  try wp_auto
  iunfold swift.keysOwn at Hkeys
  icases Hkeys with ⟨HkM, HkE, %Hkcov⟩
  wp_apply wp_map_lookup2 $$ [$HkM] as HkM
  ihave HkI : swift.keysIn kM (s ++ hd) $$ [HkE]
  · iunfold swift.keysIn; iframe HkE; ipureintro; exact Hkcov
  wp_join iprop(∃ (kl : Loc) (kMn : GMap w64 GoInterface) (dpn : GoSlice),
      key_ptr ↦ c.key ∗ swift.fld rp go!"keys" ↦ km ∗
      info_ptr ↦ (interface.ok ⟨go.GoType.PointerType swift.lightKeyInfo.ty, #kl⟩ : GoInterface) ∗
      km ↦$ kMn ∗
      swift.lki.lkiOwn kl (swift.lkOf (s ++ hd) c.key).1 (swift.lkOf (s ++ hd) c.key).2 ∗
      (swift.lki.lkiOwn kl
          (swift.lki.addTo c.op (ofCmdId (toCmdId x)) (swift.lkOf (s ++ hd) c.key).1
            (swift.lkOf (s ++ hd) c.key).2).1
          (swift.lki.addTo c.op (ofCmdId (toCmdId x)) (swift.lkOf (s ++ hd) c.key).1
            (swift.lkOf (s ++ hd) c.key).2).2 -∗
        swift.keysIn kMn (s ++ hd ++ [(toCmdId x, c)])) ∗
      dep_ptr ↦ dpn ∗ dpn ↦* ((sp.lkDeps (s ++ hd) c).map ofCmdId) ∗
      ownSliceCap swift.CommandId dpn (DFrac.own 1) ∗ ⌜dpn ≠ slice.nil⌝)
    with [key Hkf info HkM HkI dep Hd0 Hd0c] as ⟨%kl, %kMn, %dpn, key, Hkf, info, HkM, Hlki, Hkback,
      dep, Hdp, Hdpc, %Hdpn⟩
  · -- the key has a `lightKeyInfo`: its conflicts are the dependencies
    obtain ⟨ki, hki⟩ := Option.isSome_iff_exists.mp Hif
    ihave ⟨%kl, %Hkl, Hlki, Hkback⟩ := swift.keysIn_lookup kM (s ++ hd) (toCmdId x) c ki hki $$ HkI
    rw [hki, Hkl]
    simp only [Option.getD_some]
    try wp_auto
    wp_apply wp_conf $$ [$Hlki] as %csl ⟨Hlki, #Hcsl⟩
    try wp_auto
    wp_apply (swift.wp_slice_append_nn (dq := DFrac.discard)) $$ [$Hd0 $Hd0c $Hcsl]
      as %nsl ⟨Hnsl, Hnslc, -, %Hnsl⟩
    · ipureintro; exact DFrac.valid_own_one
    try wp_auto
    wp_join_done
    iexists kl, kM, nsl
    iframe
    isplitl
    · iExactEq Hnsl
      rw [← swift.lkOf_conflict (s ++ hd) c hpg]
      simp
    ipureintro; exact Hnsl Hd0p
  · -- a fresh `lightKeyInfo`
    have hnone : kM !! c.key = none := by simpa using Hif
    have h0 := Hkcov c.key hnone
    have hdeps : (sp.lkDeps (s ++ hd) c).map ofCmdId = [] := by
      rw [← swift.lkOf_conflict (s ++ hd) c hpg, h0]; split <;> rfl
    wp_apply wp_newLKI as %kl Hlki
    try wp_auto
    wp_apply wp_mapInsert $$ [$HkM] as HkM
    try wp_auto
    wp_join_done
    iexists kl, _, d0
    iframe
    isplitl [Hlki]
    · rw [h0]; iexact Hlki
    isplitr [Hd0]
    · iintro Hl
      rw [h0]
      iapply swift.keysIn_new kM (s ++ hd) (toCmdId x) c kl hnone
      iframe
    isplitl
    · rw [hdeps]; iexact Hd0
    ipureintro; intro h; exact Hd0p (by rw [h]; rfl)
  -- `info.add(cmd, cmdId)`: the keys along `x`
  have hClen : (swift.lkOf (s ++ hd) c.key).2.length + 1 < 2 ^ 63 := by
    have := swift.lkOf_len (s ++ hd) c.key; omega
  wp_apply (wp_add kl _ _ (state.Command.mk c.op c.key vs) x) $$ [$Hlki] as Hlki
  · ipureintro; exact hClen
  ihave HkI' := Hkback $$ [Hlki]
  · iExactEq Hlki; rfl
  try wp_auto
  -- the key's hash log
  iunfold swift.hlogOwn at Hhlog
  icases Hhlog with ⟨HhM, HhE, %Hhcov⟩
  wp_apply wp_map_lookup2 $$ [$HhM] as HhM
  wp_join iprop(∃ (hl : Loc) (hMn : GMap w64 Loc) (σ : swift.hlog.HL),
      key_ptr ↦ c.key ∗ swift.fld rp go!"hlog" ↦ hm ∗ l_ptr ↦ hl ∗ hm ↦$ hMn ∗
      swift.hlog.ownHashLog hl σ ∗ ⌜swift.hlogOk ld hd K Λ c.key σ⌝ ∗
      (swift.hlogEnt ld (hd ++ [(toCmdId x, c)]) K Λ c.key hl -∗
        [∗map] k ↦ l' ∈ hMn, swift.hlogEnt ld (hd ++ [(toCmdId x, c)]) K Λ k l') ∗
      ⌜∀ k, hMn !! k = none → swift.idsOfKey (hd ++ [(toCmdId x, c)]) k = []⌝)
    with [key Hhf l HhM HhE] as ⟨%hl, %hMn, %σ, key, Hhf, l, HhM, Hσ, %Hσok, Hhback, %Hhcov'⟩
  · -- the key's log
    obtain ⟨hl, hsome⟩ := Option.isSome_iff_exists.mp (by simpa using Hif)
    rw [hsome]
    simp only [Option.getD_some]
    try wp_auto
    ihave ⟨He, Hback⟩ := swift.bigSepM_change1 hM c.key hl (swift.hlogEnt ld hd K Λ)
        (swift.hlogEnt ld (hd ++ [(toCmdId x, c)]) K Λ) hsome ?_ $$ HhE
    · intro k' l' hk'
      unfold swift.hlogEnt
      iintro ⟨%σ', Ho, %Hok⟩
      iexists σ'; iframe Ho; ipureintro
      exact swift.hlog.hlogOk_other ld hd K Λ k' σ' (toCmdId x) c (fun h => hk' h.symm) Hok
    iunfold swift.hlogEnt at He
    icases He with ⟨%σ, Hσ, %Hσok⟩
    iexists hl, hM, σ
    iframe
    isplitr
    · ipureintro; exact Hσok
    ipureintro
    intro k hk
    have hkc : c.key ≠ k := fun h => by subst h; rw [hsome] at hk; cases hk
    rw [swift.idsOfKey_append1, if_neg hkc]
    exact Hhcov k hk
  · -- no log for the key yet: a fresh one
    have hnone : hM !! c.key = none := by simpa using Hif
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
        (swift.hlogEnt ld (hd ++ [(toCmdId x, c)]) K Λ) hnone ?_) $$ HhE
      intro k' l' hk'
      unfold swift.hlogEnt
      iintro ⟨%σ', Ho, %Hok⟩
      iexists σ'; iframe Ho; ipureintro
      exact swift.hlog.hlogOk_other ld hd K Λ k' σ' (toCmdId x) c (fun h => hk' h.symm) Hok
    · ipureintro
      intro k hk
      by_cases hkc : c.key = k
      · subst hkc; rw [GMap.lookup_insert] at hk; cases hk
      · rw [GMap.lookup_insert_ne _ _ hkc] at hk
        rw [swift.idsOfKey_append1, if_neg hkc]
        exact Hhcov k hk
  have hxhd : toCmdId x ∉ hd.map Prod.fst := fun h => hxn (by rw [List.map_append]; exact List.mem_append_right _ h)
  obtain ⟨hnp, hok', hlast, hld, hall⟩ := swift.hlog.hlogOk_append ld hd K Λ σ (toCmdId x) c Hσok hxhd hxK
  wp_apply (wp_append hl σ (state.Command.mk c.op c.key vs) x) $$ [$Hσ] as %H ⟨Hσ, #HP⟩
  · ipureintro; exact hnp
  wp_bind (App (Val (GoInstruction (CompositeLiteral _))) (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := swift.SHash) [H]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %hsl1 ⟨Hhsl1, -⟩
  try wp_auto
  wp_apply wp_slice_append $$ [$Hh0 $Hh0c $Hhsl1] as %nh ⟨Hnh, Hnhc, -⟩
  try wp_auto
  wp_for_post
  iframe
  iexists (W64 0 + W64 1), c.key
  iframe i key
  iright
  isplitr
  · ipureintro; decide
  iexists dpn, nh, kMn, hMn, _, H
  iframe dep hashes Hdp Hdpc Hnhc
  isplitl [HkI' HkM]
  · iunfold swift.keysIn at HkI'
    icases HkI' with ⟨HkE, %Hkc⟩
    iunfold swift.keysOwn
    iframe
    ipureintro; exact Hkc
  isplitl [Hhback Hσ HhM]
  · iunfold swift.hlogOwn
    iframe HhM
    isplitl
    · iapply Hhback
      iunfold swift.hlogEnt
      iexists _
      iframe Hσ
      ipureintro; exact hok'
    · ipureintro; exact Hhcov'
  ihave %Hnhl := ownSlice_len _ _ _ $$ [Hnh]
  · iExactEq Hnh; rfl
  isplitl [Hnh]
  · iExactEq Hnh; rfl
  iframe HP
  isplitr
  · ipureintro
    exact ⟨hlast, hld, hall⟩
  ipureintro
  refine ⟨Hdpn, fun h => ?_⟩
  rw [h] at Hnhl
  have h1 : sint.nat (slice.nil : GoSlice).len = 0 := by decide
  have h2 := Hnhl.1
  rw [h1] at h2
  simp at h2

end proofs


end Perennial.github_com.imdea_software.swiftpaxos
