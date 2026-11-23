/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/HashLog.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`HashLog`'s proofs (swift/dpath.go): `NewHashLog`, `update`, `Update`, `Append`, over the specs
of `HashLeaf.lean` (`HashLog.chain`, `hash`) as hypotheses.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HashLogSpecs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.hlog

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [swift.Assumptions]

set_option goose.wp.extras true

theorem NewHashLog.wp_proof : NewHashLog.spec := by
  wp_start
  haveI := cmdId_intoValInj (sem := sem)
  wp_auto
  wp_apply (wp_map_make1 (K := swift.CommandId) (V := Loc)) as %nm Hnm
  wp_apply (wp_map_make1 (K := swift.CommandId) (V := Loc)) as %um Hum
  try wp_auto
  iapply HΦ
  unfold ownHashLog
  iexists (zero_val (GoArray w8 32)), (zero_val (GoArray w8 32)), null, null, nm, um, [], ∅, ∅
  iframe Hnm Hum
  isplitl [«$r0»]
  · iExactEq «$r0»; rfl
  have hz : -1 ≤ sint.Z HL.init.synced := by simp [HL.init]
  have hn : ¬ 0 ≤ sint.Z HL.init.synced := by simp [HL.init]
  unfold syncOk hashOk
  rw [ite_eq_right_iff.mpr (fun h => absurd h hn)]
  isplitr
  · unfold dseg; itrivial
  isplitr
  · unfold updsOk; isplitr
    · ipureintro; intro k; simp [HL.init]
    imodintro; iintro %k %u %Hk; simp at Hk
  isplitr
  · ipureintro
    refine ⟨rfl, rfl, hz, rfl, by simp, by simp [HL.init], rfl, ?_, fun k => rfl⟩
    exact ⟨fun _ => rfl, by simp, by simp⟩
  isplitr
  · ipureintro; rfl
  ileft; ipureintro; rfl

theorem HashLog.Append.wp_proof (wp_update : HashLog.update.spec) (wp_hash : hash.spec)
    (wp_chain : HashLog.chain.spec) : HashLog.Append.spec := by
  intro l σ c x
  wp_start as ⟨Hown, %Hx⟩
  haveI := cmdId_intoValInj (sem := sem)
  iunfold ownHashLog at Hown
  icases Hown with ⟨%sh, %h, %head, %tail, %nm, %um, %ns, %nodes, %upds, Hl, Hnm, Hum, Hns,
    #Hupds, %Hp, #Hsync, #Hhash⟩
  wp_auto
  wp_apply (wp_map_lookup2 (K := swift.CommandId) (V := Loc)) $$ [$Hum] as Hum
  try wp_auto
  ihave %Hiff : iprop(⌜∀ k, (upds !! k).isSome = (σ.upd (toCmdId k)).isSome⌝) $$ [Hupds]
  · iunfold updsOk at Hupds; icases Hupds with ⟨%H, -⟩; ipureintro; exact H
  cases hux : upds !! x with
  | some u =>
    iunfold updsOk at Hupds
    icases Hupds with ⟨-, #Hu⟩
    ihave ⟨%e, %sl, %He, #Hue, #Hsl, #HP⟩ := Hu $$ %x %u %hux
    obtain ⟨He, Hel⟩ := He
    ihave Hue2 := Hue
    iStructNamed Hue2
    simp only [Option.isSome_some, decide_true, Option.getD_some]
    try wp_auto
    wp_apply (wp_mapDelete (K := swift.CommandId) (V := Loc)) $$ [$Hum] as Hum
    try wp_auto
    ihave %Hsll := ownSlice_len $$ Hsl
    simp only [List.length_singleton] at Hsll
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by word⟩), show sint.Z (W64 0) = 0 from rfl]
    wp_apply (wp_load_slice_index (V := swift.SHash) sl 0 _ _ (swift.SHash.mk (GoArray.mk e.hash))
      (by decide)) $$ [Hsl] as -
    · iframe Hsl; ipureintro; rfl
    ihave Hown := ownHashLog_intro l (σ.clearUpd (toCmdId x)) sh h head tail nm um ns nodes
      (GMap.delete x upds) (by simpa using Hp) $$ [Hl Hnm Hum Hns]
    · simp only [HL.clearUpd_synced]
      iframe Hl Hnm Hum Hns
      rw [syncOk_clearUpd, hashOk_clearUpd]; iframe Hsync Hhash
      iapply updsOk_delete; iunfold updsOk; iframe Hu; ipureintro; exact Hiff
    wp_apply wp_update l (σ.clearUpd (toCmdId x)) x e.seq (swift.SHash.mk (GoArray.mk e.hash))
      e.path false $$ [$Hpkg $Hown $HP] as Hown
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by word⟩), show sint.Z (W64 0) = 0 from rfl]
    wp_apply (wp_load_slice_index (V := swift.SHash) sl 0 _ _ (swift.SHash.mk (GoArray.mk e.hash))
      (by decide)) $$ [Hsl] as -
    · iframe Hsl; ipureintro; rfl
    try wp_auto
    iapply HΦ
    simp only [HL.append, He]
    iframe Hown HP
  | none =>
    have hnone : σ.upd (toCmdId x) = none := by
      have := Hiff x; rw [hux] at this; simpa using this.symm
    simp only [Option.isSome_none, Bool.false_eq_true, decide_false]
    try wp_auto
    obtain ⟨hshl, hhl, hsy, hpend, hnd, hpnd, hhead, htail, hnodes⟩ := Hp
    have hxn := ids_of_pending ns σ.pending hpend x Hx
    ihave ⟨Hnd, Hns, %Hfresh⟩ := dseg_fresh _ _ ns null null $$ [$«$r0» $Hns]
    ihave ⟨Hns, %Hnn⟩ := dseg_nonnull ns null null $$ Hns
    wp_apply (wp_mapInsert (K := swift.CommandId) (V := Loc)) $$ [$Hnm] as Hnm
    try wp_auto
    have hσ : σ.append (toCmdId x) =
        ({ σ with pending := σ.pending ++ [toCmdId x] }, σ.base ++ σ.pending ++ [toCmdId x]) := by
      simp [HL.append, hnone]
    rw [hσ]
    have hnodes' : ∀ k, (<[x := «$r0_ptr»]> nodes) !! k = lookupN (ns ++ [(«$r0_ptr», x)]) k := by
      intro k; rw [lookupN_snoc _ _ _ hxn]
      by_cases hk : k = x
      · subst hk; simp [GMap.lookup_insert]
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk), if_neg hk]; exact hnodes k
    have hnd' : ((ns ++ [(«$r0_ptr», x)]).map Prod.fst).Nodup := by
      simp only [List.map_append, List.map_cons, List.map_nil]
      refine List.nodup_append.mpr ⟨hnd, by simp, fun a ha b hb => ?_⟩
      simp only [List.mem_singleton] at hb; subst hb; exact fun e => Hfresh (e ▸ ha)
    have hpend' : (ns ++ [(«$r0_ptr», x)]).map (fun p => toCmdId p.2) = σ.pending ++ [toCmdId x] := by
      simp [hpend]
    have hpnd' : (σ.pending ++ [toCmdId x]).Nodup :=
      List.nodup_append.mpr ⟨hpnd, by simp, fun a ha b hb => by
        simp only [List.mem_singleton] at hb; subst hb; exact fun e => Hx (e ▸ ha)⟩
    by_cases hns : ns = []
    · -- the first pending command
      subst hns
      have hh0 : head = null := hhead
      have ht0 : tail = null := htail.1 rfl
      subst hh0 ht0
      try wp_auto
      wp_apply wp_chain l sh (decide (sint.Z (W64 0) ≤ sint.Z σ.synced)) x $$ [$Hpkg] as %h' #Hh'
      · ipureintro; exact hshl
      try wp_auto
      have hpe : σ.pending = [] := by simpa using hpend.symm
      ihave #HP : sp.startHash (σ.base ++ [toCmdId x]) h'.arr $$ [Hsync Hh']
      · by_cases hs : 0 ≤ sint.Z σ.synced
        · simp only [syncOk, if_pos hs, show sint.Z (W64 0) = 0 from rfl, decide_eq_true hs,
            ↓reduceIte]
          iapply sp.startHash_snoc; iframe Hsync Hh'
        · simp only [syncOk, if_neg hs, show sint.Z (W64 0) = 0 from rfl, decide_eq_false hs,
            Bool.false_eq_true, ↓reduceIte, List.nil_append]
          icases Hsync with %Hb
          rw [Hb, List.nil_append]
          iapply sp.startHash_single; iexact Hh'
      ihave %Hl' := sp.hashOf_len $$ Hh'
      ihave %Hnd0 := typedPointsto_not_null $$ Hnd
      iapply HΦ
      simp only [hpe, List.nil_append, List.append_nil]
      isplitl
      · iapply ownHashLog_intro l { σ with pending := [toCmdId x] } sh h' «$r0_ptr» null nm um
          [(«$r0_ptr», x)] (<[x := «$r0_ptr»]> nodes) upds
          ⟨hshl, Hl', hsy, by simp [toCmdId], by simp, by simp, rfl,
            ⟨by simp, fun _ => Or.inl rfl, by simp⟩, by simpa using hnodes'⟩
        iframe Hnm Hum
        isplitl [Hl]
        · iExactEq Hl; rfl
        isplitl [Hnd]
        · iapply (dseg_one _ _ _ _).2; iframe Hnd; ipureintro; exact Hnd0
        isplitr
        · iExactEq Hupds; rfl
        isplitr
        · iExactEq Hsync; rfl
        iunfold hashOk; iright; iexact HP
      · iexact HP
    · have hh0 : head ≠ null := by
        rw [hhead]; obtain ⟨⟨a, y⟩, r, rfl⟩ := List.exists_cons_of_ne_nil hns
        simp only [firstL_cons]; intro h; apply Hnn; simp [h]
      try wp_auto
      rw [decide_eq_false hh0]
      try wp_auto
      ihave %Hnd0 := typedPointsto_not_null $$ Hnd
      have hhead' : head = firstL (ns ++ [(«$r0_ptr», x)]) null := by
        rw [firstL_append]; obtain ⟨q, r, hq⟩ := List.exists_cons_of_ne_nil hns
        rw [hq] at hhead ⊢; exact hhead
      have htail' : tailOk (ns ++ [(«$r0_ptr», x)]) «$r0_ptr» := by
        refine ⟨by simp, fun h1 => ?_, fun _ => by simp⟩
        exfalso; have : ns.length ≠ 0 := fun h0 => hns (List.eq_nil_of_length_eq_zero h0)
        simp only [List.length_append, List.length_singleton] at h1; omega
      wp_if_destruct
      · -- one pending node, no tail pointer yet
        have hlen1 : ns.length = 1 := by
          rcases Nat.lt_or_ge ns.length 2 with h2 | h2
          · have : ns.length ≠ 0 := fun h0 => hns (List.eq_nil_of_length_eq_zero h0)
            omega
          · exfalso; have := htail.2.2 h2
            obtain ⟨A, p, hA⟩ := (sp.eq_nil_or_snoc ns).resolve_left hns
            subst hA; simp at this; apply Hnn; simp [← this]
        obtain ⟨⟨a, y⟩, hns1⟩ : ∃ p, ns = [p] := by
          match ns, hlen1 with
          | [p], _ => exact ⟨p, rfl⟩
        have ha : head = a := by rw [hhead, hns1]; rfl
        subst ha
        rw [hns1]
        ihave ⟨-, Ha⟩ := (dseg_one _ _ _ _).1 $$ Hns
        try wp_auto
        ihave Hns : dseg (ns ++ [(«$r0_ptr», x)]) null null $$ [Ha Hnd]
        · rw [hns1]
          simp only [List.cons_append, List.nil_append, dseg_cons, firstL_cons, firstL_nil,
            dseg_nil]
          iframe; ipureintro; exact ⟨hh0, Hnd0⟩
        try wp_auto
        wp_apply wp_hash h x $$ [$Hpkg] as %h' #Hh'
        · ipureintro; exact hhl
        try wp_auto
        ihave %Hl' := sp.hashOf_len $$ Hh'
        have hpne : σ.pending ≠ [] := by
          rw [← hpend]; intro h0; exact hns (List.map_eq_nil_iff.mp h0)
        ihave #HP : sp.startHash (σ.base ++ σ.pending ++ [toCmdId x]) h'.arr $$ [Hhash Hh']
        · iunfold hashOk at Hhash
          icases Hhash with (%He | #Hb)
          · exact absurd He hpne
          · iapply sp.startHash_snoc; iframe Hb Hh'
        iapply HΦ
        isplitl
        · iapply ownHashLog_intro l { σ with pending := σ.pending ++ [toCmdId x] } sh h' head
            «$r0_ptr» nm um (ns ++ [(«$r0_ptr», x)]) (<[x := «$r0_ptr»]> nodes) upds
            ⟨hshl, Hl', hsy, hpend', hnd', hpnd', hhead', htail', hnodes'⟩
          iframe Hnm Hum Hns
          isplitl [Hl]
          · iExactEq Hl; rfl
          isplitr
          · iExactEq Hupds; rfl
          isplitr
          · iExactEq Hsync; rfl
          iunfold hashOk; iright; iExactEq HP; simp
        · iexact HP
      · -- a tail pointer: the last node
        have htl : tail = lastL ns null := by
          rcases Nat.lt_or_ge ns.length 2 with h2 | h2
          · have : ns.length ≠ 0 := fun h0 => hns (List.eq_nil_of_length_eq_zero h0)
            have h1 : ns.length = 1 := by omega
            rcases htail.2.1 h1 with h | h
            · exact absurd h (by simpa using Hif)
            · exact h
          · exact htail.2.2 h2
        obtain ⟨A, ⟨t, y⟩, hA⟩ := (sp.eq_nil_or_snoc ns).resolve_left hns
        have ht : tail = t := by rw [htl, hA]; simp
        subst ht
        rw [hA]
        ihave ⟨HA, Ht⟩ := (dseg_app A [(tail, y)] null null).1 $$ Hns
        ihave ⟨-, Ht⟩ := (dseg_one _ _ _ _).1 $$ Ht
        try wp_auto
        ihave Hns : dseg (ns ++ [(«$r0_ptr», x)]) null null $$ [HA Ht Hnd]
        · rw [hA]
          iapply (dseg_app (A ++ [(tail, y)]) [(«$r0_ptr», x)] null null).2
          simp only [firstL_cons, lastL_snoc]
          isplitl [HA Ht]
          · iapply (dseg_app A [(tail, y)] null «$r0_ptr»).2
            simp only [firstL_cons]
            iframe HA
            iapply (dseg_one _ _ _ _).2; iframe Ht; ipureintro
            intro h; apply Hnn; rw [hA]; simp [h]
          iapply (dseg_one _ _ _ _).2; iframe Hnd; ipureintro; exact Hnd0
        try wp_auto
        wp_apply wp_hash h x $$ [$Hpkg] as %h' #Hh'
        · ipureintro; exact hhl
        try wp_auto
        ihave %Hl' := sp.hashOf_len $$ Hh'
        have hpne : σ.pending ≠ [] := by
          rw [← hpend]; intro h0; exact hns (List.map_eq_nil_iff.mp h0)
        ihave #HP : sp.startHash (σ.base ++ σ.pending ++ [toCmdId x]) h'.arr $$ [Hhash Hh']
        · iunfold hashOk at Hhash
          icases Hhash with (%He | #Hb)
          · exact absurd He hpne
          · iapply sp.startHash_snoc; iframe Hb Hh'
        iapply HΦ
        isplitl
        · iapply ownHashLog_intro l { σ with pending := σ.pending ++ [toCmdId x] } sh h' head
            «$r0_ptr» nm um (ns ++ [(«$r0_ptr», x)]) (<[x := «$r0_ptr»]> nodes) upds
            ⟨hshl, Hl', hsy, hpend', hnd', hpnd', hhead', htail', hnodes'⟩
          iframe Hnm Hum Hns
          isplitl [Hl]
          · iExactEq Hl; rfl
          isplitr
          · iExactEq Hupds; rfl
          isplitr
          · iExactEq Hsync; rfl
          iunfold hashOk; iright; iExactEq HP; simp
        · iexact HP

end proofs

end swift.hlog

end Perennial.github_com.imdea_software.swiftpaxos
