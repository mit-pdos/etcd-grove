/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/HashLogUpdate.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`HashLog.update` and `HashLog.Update` (swift/dpath.go): the node's unlinking (by the four shapes
of its neighbours), the saved update, the re-basing, and the hash's recomputation over the pending
list (`chain` from `syncedHash`).
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

set_option hygiene false in
/-- The recomputation of `hash` (the loop over the pending list, then the store), from the
loop's entry state (see its first use). -/
local macro "recompute" shx:ident ns:ident nodes:ident head:ident tail:ident : tactic =>
  `(tactic| (
  obtain ⟨hsy', hpend', hnd', hpnd', hhead', htail', hnodes'⟩ := hfacts
  ihave HL : (∃ (D R : List (Loc × swift.CommandId)) (ini : GoArray w8 32) (st : Bool),
      "n" ∷ n_ptr ↦ firstL R null ∗ "initial" ∷ initial_ptr ↦ ini ∗
      "started" ∷ started_ptr ↦ st ∗ "Hns" ∷ dseg $ns null null ∗
      "%HDR" ∷ ⌜$ns = D ++ R ∧ ini.arr.length = 32⌝ ∗
      "#Hacc" ∷ accOk τ ($shx).arr (D.map (fun p => toCmdId p.2)) ini.arr st : IProp netDistGF)
    $$ [n initial started Hns]
  · iexists [], $ns, $shx, _
    rw [← hhead']
    iframe n initial started Hns
    isplitr
    · ipureintro; exact ⟨rfl, hshl'⟩
    unfold accOk; rw [if_pos (by simp)]; ipureintro; exact ⟨rfl, by rw [hτs]; rfl⟩
  wp_for HL
  obtain ⟨hDR, hinil⟩ := HDR
  ihave ⟨Hns, %Hnn⟩ := dseg_nonnull $ns null null $$ Hns
  wp_if_destruct
  · rcases R with _ | ⟨⟨a, y⟩, R'⟩
    · exfalso; simp only [firstL_nil, _root_.decide_true, Bool.not_true] at Hif
      exact absurd (go.intoVal_inj Hif) (by decide)
    have ha0 : a ≠ null := by
      intro h0; apply Hnn; rw [hDR]; simp [h0]
    rw [hDR]
    ihave ⟨HA, %-, Ha, HR⟩ := (dseg_mid D R' a y null null).1 $$ Hns
    simp only [firstL_cons]
    try wp_auto
    wp_apply wp_chain l ini st y $$ [Hpkg] as %h' #Hh'
    · ipureintro; exact hinil
    try wp_auto
    ihave %Hl' := sp.hashOf_len $$ Hh'
    ihave #Hacc' : accOk τ ($shx).arr ((D.map (fun p => toCmdId p.2)) ++ [toCmdId y]) h'.arr true
      $$ [Hsyncτ Hacc Hh']
    · iapply accOk_step; iframe Hsyncτ Hacc Hh'
    wp_for_post
    iframe
    iexists D ++ [(a, y)], R', h', true
    iframe
    isplitl [HA Ha HR]
    · iapply (dseg_mid D R' a y null null).2; iframe; ipureintro; exact ha0
    isplitr
    · ipureintro; exact ⟨by simp, Hl'⟩
    simp only [List.map_append, List.map_cons, List.map_nil]
    iexact Hacc'
  · rcases R with _ | ⟨⟨a, y⟩, R'⟩
    · simp only [firstL_nil, _root_.decide_true, Bool.not_true, ↓reduceIte]
      try wp_auto
      obtain rfl : D = $ns := by simpa using hDR.symm
      iapply HΦ
      iapply ownHashLog_intro l τ $shx ini $head $tail nm um D $nodes upds
        ⟨hshl', hinil, hsy', hpend', hnd', hpnd', hhead', htail', hnodes'⟩
      iframe Hnm Hum Hns Hupdsτ Hsyncτ
      isplitl [Hl]
      · iExactEq Hl; rfl
      iapply accOk_done (st := st); rw [← hpend']; iexact Hacc
    · exfalso
      have ha : a = null := by
        by_cases h0 : a = null
        · exact h0
        · simp [h0] at Hif
      apply Hnn; rw [hDR]; simp [ha]))

set_option hygiene false in
/-- After the node's unlinking (`HlN`, `HnsN`, `Hnm` over `nsN`, `nodesN`, `hd`, `tl`): the
re-basing if `s` is above `synced`, then the recomputation. -/
local macro "afterUnlink" hd:ident tl:ident : tactic => `(tactic| (
  try wp_auto
  by_cases hsle : sint.Z s ≤ sint.Z σ.synced
  rotate_left
  · -- re-based on `h`
    have hlt : sint.Z σ.synced < sint.Z s := by omega
    simp only [decide_eq_false hsle]
    try wp_auto
    rw [decide_eq_true hlt]
    obtain ⟨τ, hτdef⟩ : ∃ τ : HL, τ = HL.mk s P (σ.pending.erase (toCmdId x)) σ.upd :=
      ⟨_, rfl⟩
    have hτ : σ.updateTo (toCmdId x) s hha.arr P save = τ := by
      rw [hτdef]; simp [HL.updateTo, hxp, hlt]
    rw [hτ]
    have hτs : τ.synced = s := by rw [hτdef]
    have hτb : τ.base = P := by rw [hτdef]
    have hτp : τ.pending = σ.pending.erase (toCmdId x) := by rw [hτdef]
    have hτu : τ.upd = σ.upd := by rw [hτdef]
    try wp_auto
    ihave Hl : l ↦ swift.HashLog.mk τ.synced (swift.SHash.mk hha) $hd $tl (swift.SHash.mk h) nm um
      $$ [HlN]
    · rw [hτs]; iExactEq HlN; rfl
    have hsyτ : 0 ≤ sint.Z τ.synced := by rw [hτs]; omega
    ihave #Hsyncτ : syncOk τ hha.arr $$ [HP]
    · unfold syncOk; rw [if_pos hsyτ, hτb]; iexact HP
    ihave #Hupdsτ : updsOk τ upds $$ [Hupds]
    · unfold updsOk; rw [hτu]; iexact Hupds
    have hfacts : -1 ≤ sint.Z τ.synced ∧ nsN.map (fun p => toCmdId p.2) = τ.pending ∧
        (nsN.map Prod.fst).Nodup ∧ τ.pending.Nodup ∧ $hd = firstL nsN null ∧ tailOk nsN $tl ∧
        ∀ k, nodesN !! k = lookupN nsN k :=
      ⟨by omega, hτp ▸ hpendN, hndN, hτp ▸ List.Nodup.erase _ hpnd, hhdN, htlN, hnodesN⟩
    ihave %hshl' := sp.startHash_len $$ HP
    rename_i Hns_old
    iclear Hsync Hhash Hupds HP
    ihave Hns : dseg nsN null null $$ [HnsN]
    · iexact HnsN
    try wp_auto
    recompute hha nsN nodesN $hd $tl
  · -- the same base
    have hle : ¬ sint.Z σ.synced < sint.Z s := by omega
    simp only [decide_eq_true hsle]
    try wp_auto
    rw [decide_eq_false hle]
    obtain ⟨τ, hτdef⟩ : ∃ τ : HL, τ = HL.mk σ.synced σ.base (σ.pending.erase (toCmdId x)) σ.upd :=
      ⟨_, rfl⟩
    have hτ : σ.updateTo (toCmdId x) s hha.arr P save = τ := by
      rw [hτdef]; simp [HL.updateTo, hxp, hle]
    rw [hτ]
    have hτs : τ.synced = σ.synced := by rw [hτdef]
    have hτp : τ.pending = σ.pending.erase (toCmdId x) := by rw [hτdef]
    try wp_auto
    ihave Hl : l ↦ swift.HashLog.mk τ.synced (swift.SHash.mk sh) $hd $tl (swift.SHash.mk h) nm um
      $$ [HlN]
    · rw [hτs]; iExactEq HlN; rfl
    ihave #Hsyncτ : syncOk τ sh.arr $$ [Hsync]
    · rw [hτdef]; unfold syncOk; simp only; iexact Hsync
    ihave #Hupdsτ : updsOk τ upds $$ [Hupds]
    · rw [hτdef]; unfold updsOk; simp only; iexact Hupds
    have hfacts : -1 ≤ sint.Z τ.synced ∧ nsN.map (fun p => toCmdId p.2) = τ.pending ∧
        (nsN.map Prod.fst).Nodup ∧ τ.pending.Nodup ∧ $hd = firstL nsN null ∧ tailOk nsN $tl ∧
        ∀ k, nodesN !! k = lookupN nsN k :=
      ⟨hτs ▸ hsy, hτp ▸ hpendN, hndN, hτp ▸ List.Nodup.erase _ hpnd, hhdN, htlN, hnodesN⟩
    have hshl' : sh.arr.length = 32 := hshl
    iclear Hsync Hhash Hupds HP
    ihave Hns : dseg nsN null null $$ [HnsN]
    · iexact HnsN
    try wp_auto
    recompute sh nsN nodesN $hd $tl))

theorem HashLog.update.wp_proof (wp_chain : HashLog.chain.spec) : HashLog.update.spec := by
  intro l σ x s hh P save
  obtain ⟨hha⟩ := hh
  wp_start as ⟨Hown, #HP⟩
  haveI := cmdId_intoValInj (sem := sem)
  iunfold ownHashLog at Hown
  icases Hown with ⟨%sh, %h, %head, %tail, %nm, %um, %ns, %nodes, %upds, Hl, Hnm, Hum, Hns,
    #Hupds, %Hp, #Hsync, #Hhash⟩
  obtain ⟨hshl, hhl, hsy, hpend, hnd, hpnd, hhead, htail, hnodes⟩ := Hp
  try wp_auto
  wp_apply (wp_map_lookup2 (K := swift.CommandId) (V := Loc)) $$ [$Hnm] as Hnm
  try wp_auto
  have hidnd : (ns.map Prod.snd).Nodup := by
    rw [← hpend] at hpnd
    exact nodup_of_map toCmdId _ (by simpa [List.map_map, Function.comp_def] using hpnd)
  cases hnx : nodes !! x with
  | none =>
    have hxp : toCmdId x ∉ σ.pending := by
      rw [← hpend]; intro hm
      obtain ⟨p, hp, hpx⟩ := List.mem_map.mp hm
      apply lookupN_none ns x (by rw [← hnodes]; exact hnx)
      have : p.2 = x := by have := congrArg ofCmdId hpx; simpa using this
      exact List.mem_map.mpr ⟨p, hp, this⟩
    simp only [Option.isSome_none, Bool.false_eq_true, decide_false, Bool.not_false]
    cases save
    · try wp_auto
      wp_if_destruct
      · -- `s ≤ synced`, nothing to do
        try wp_auto
        iapply HΦ
        have : σ.updateTo (toCmdId x) s hha.arr P false = σ := by
          simp [HL.updateTo, hxp, Hif]
        rw [this]
        iapply ownHashLog_intro l σ sh h head tail nm um ns nodes upds
          ⟨hshl, hhl, hsy, hpend, hnd, hpnd, hhead, htail, hnodes⟩
        iframe; iframe #
      · -- re-based on `h`
        have hlt : sint.Z σ.synced < sint.Z s := by omega
        have hτ : σ.updateTo (toCmdId x) s hha.arr P false = { σ with synced := s, base := P } := by
          simp [HL.updateTo, hxp, show ¬ sint.Z s ≤ sint.Z σ.synced by omega]
        rw [hτ]
        try wp_auto
        rw [decide_eq_true hlt]
        try wp_auto
        ihave Hl : l ↦ swift.HashLog.mk s (swift.SHash.mk hha) head tail (swift.SHash.mk h) nm um $$ [Hl]
        · iExactEq Hl; rfl
        obtain ⟨τ, hτdef⟩ : ∃ τ : HL, τ = { σ with synced := s, base := P } := ⟨_, rfl⟩
        rw [← hτdef]
        have hτs : τ.synced = s := by rw [hτdef]
        have hτb : τ.base = P := by rw [hτdef]
        have hτp : τ.pending = σ.pending := by rw [hτdef]
        have hτu : τ.upd = σ.upd := by rw [hτdef]
        rw [← hτs]
        have hsyτ : 0 ≤ sint.Z τ.synced := by rw [hτs]; omega
        ihave #Hsyncτ : syncOk τ hha.arr $$ [HP]
        · unfold syncOk; rw [if_pos hsyτ, hτb]; iexact HP
        ihave #Hupdsτ : updsOk τ upds $$ [Hupds]
        · unfold updsOk; rw [hτu]; iexact Hupds
        have hfacts : -1 ≤ sint.Z τ.synced ∧ ns.map (fun p => toCmdId p.2) = τ.pending ∧
            (ns.map Prod.fst).Nodup ∧ τ.pending.Nodup ∧ head = firstL ns null ∧ tailOk ns tail ∧
            ∀ k, nodes !! k = lookupN ns k :=
          ⟨by omega, hτp ▸ hpend, hnd, hτp ▸ hpnd, hhead, htail, hnodes⟩
        ihave %hshl' := sp.startHash_len $$ HP
        iclear Hsync Hhash Hupds HP
        try wp_auto
        recompute hha ns nodes head tail
    · try wp_auto
      wp_apply (wp_slice_literal (V := swift.SHash)) [swift.SHash.mk hha]
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      try wp_auto
      ipersist «$r0»
      ipersist Hsl
      wp_apply (wp_mapInsert (K := swift.CommandId) (V := Loc)) $$ [$Hum] as Hum
      try wp_auto
      iapply HΦ
      ihave %Hhl := sp.startHash_len $$ HP
      have hτ : σ.updateTo (toCmdId x) s hha.arr P true =
          { σ with upd := fun y => if y = toCmdId x then some ⟨s, hha.arr, P⟩ else σ.upd y } := by
        simp [HL.updateTo, hxp]
      rw [hτ]
      iapply ownHashLog_intro l
        { σ with upd := fun y => if y = toCmdId x then some ⟨s, hha.arr, P⟩ else σ.upd y }
        sh h head tail nm um ns nodes _ ⟨hshl, hhl, hsy, hpend, hnd, hpnd, hhead, htail, hnodes⟩
      iframe Hnm Hum Hns
      isplitl [Hl]
      · iExactEq Hl; rfl
      isplitr
      · iunfold updsOk at Hupds
        icases Hupds with ⟨%Hiff, #Hu⟩
        unfold updsOk
        isplitr
        · ipureintro; intro k
          by_cases hk : k = x
          · subst hk; simp [GMap.lookup_insert]
          · have : toCmdId k ≠ toCmdId x := fun e => hk (by
              have := congrArg ofCmdId e; simpa using this)
            rw [GMap.lookup_insert_ne _ _ (Ne.symm hk)]; simp only [if_neg this]; exact Hiff k
        imodintro
        iintro %k %u %Hk
        by_cases hk : k = x
        · subst hk
          rw [GMap.lookup_insert] at Hk; cases Hk
          iexists ⟨s, hha.arr, P⟩, _
          iframe HP
          isplitr
          · ipureintro; simp [Hhl]
          iframe «$r0» Hsl
        · have : toCmdId k ≠ toCmdId x := fun e => hk (by
            have := congrArg ofCmdId e; simpa using this)
          rw [GMap.lookup_insert_ne _ _ (Ne.symm hk)] at Hk
          ihave ⟨%e, %sl', %He, H1, H2, H3⟩ := Hu $$ %k %u %Hk
          iexists e, sl'; iframe H1 H2 H3; ipureintro
          simp only [if_neg this]; exact He
      isplitr
      · iExactEq Hsync; rfl
      iExactEq Hhash; rfl
  | some a =>
    obtain ⟨A, B, hAB⟩ := lookupN_some ns x a (by rw [← hnodes]; exact hnx)
    have hxp : toCmdId x ∈ σ.pending := by rw [← hpend, hAB]; simp
    simp only [Option.isSome_some, _root_.decide_true, Bool.not_true, Bool.false_and,
      Option.getD_some]
    try wp_auto
    rw [hAB]
    ihave ⟨HA, %Ha0, Ha, HB⟩ := (dseg_mid A B a x null null).1 $$ Hns
    try wp_auto
    ihave ⟨HA, %HnA⟩ := dseg_nonnull A null a $$ HA
    ihave ⟨HB, %HnB⟩ := dseg_nonnull B a null $$ HB
    have hndl : ((A ++ (a, x) :: B).map Prod.fst).Nodup := hAB ▸ hnd
    have haA : a ∉ A.map Prod.fst := by
      intro h0; simp only [List.map_append, List.map_cons] at hndl
      exact (List.nodup_append.mp hndl).2.2 a h0 a (by simp) rfl
    have haB : a ∉ B.map Prod.fst := by
      intro h0; simp only [List.map_append, List.map_cons] at hndl
      exact (List.nodup_cons.mp (List.nodup_append.mp hndl).2.1).1 h0
    have hidAB : ((A ++ (a, x) :: B).map Prod.snd).Nodup := hAB ▸ hidnd
    have hhd : head = firstL (A ++ (a, x) :: B) null := hAB ▸ hhead
    have htl : tailOk (A ++ (a, x) :: B) tail := hAB ▸ htail
    have hnodesN : ∀ k, (GMap.delete x nodes) !! k = lookupN (A ++ B) k := by
      intro k; rw [lookupN_remove A B a x hidAB]
      by_cases hk : k = x
      · subst hk; simp [GMap.lookup_delete]
      · rw [GMap.lookup_delete_ne _ (Ne.symm hk), if_neg hk, hnodes, hAB]
    have hpendN : (A ++ B).map (fun p => toCmdId p.2) = σ.pending.erase (toCmdId x) := by
      rw [← hpend, hAB]
      exact (erase_mid (fun p : Loc × swift.CommandId => toCmdId p.2) A B (a, x) (by
        intro h0; obtain ⟨q, hq, hqx⟩ := List.mem_map.mp h0
        have : q.2 = x := by have := congrArg ofCmdId hqx; simpa using this
        simp only [List.map_append, List.map_cons] at hidAB
        exact (List.nodup_append.mp hidAB).2.2 q.2 (List.mem_map_of_mem hq) x (by simp) this)).symm
    have hndN : ((A ++ B).map Prod.fst).Nodup := by
      simp only [List.map_append, List.map_cons] at hndl ⊢
      exact List.nodup_append.mpr ⟨(List.nodup_append.mp hndl).1,
        (List.nodup_cons.mp (List.nodup_append.mp hndl).2.1).2,
        fun u hu v hv => (List.nodup_append.mp hndl).2.2 u hu v (List.mem_cons_of_mem _ hv)⟩
    generalize hNs : A ++ B = nsN at hnodesN hpendN hndN
    rcases sp.eq_nil_or_snoc A with rfl | ⟨A', ⟨p, z⟩, rfl⟩ <;>
      rcases B with _ | ⟨⟨q, w⟩, B'⟩
    · -- the only node
      simp only [List.nil_append, firstL_cons] at hhd
      subst hhd
      simp only [lastL_nil, firstL_nil, _root_.decide_true, Bool.not_true]
      try wp_auto
      have htl0 : tail = null ∨ tail = head := by
        rcases htl.2.1 (by simp) with h0 | h0
        · exact Or.inl h0
        · right; rw [h0]; rfl
      have hhdN : null = firstL nsN null := by rw [← hNs]; rfl
      have htlN : tailOk nsN null := by rw [← hNs]; exact ⟨fun _ => rfl, by simp, by simp⟩
      wp_if_destruct
      all_goals
        try wp_auto
        wp_apply (wp_mapDelete (K := swift.CommandId) (V := Loc)) $$ [$Hnm] as Hnm
        generalize hdn : GMap.delete x nodes = nodesN at hnodesN
        ihave HnsN : dseg nsN null null $$ []
        · rw [← hNs, List.nil_append, dseg_nil]; itrivial
      · ihave HlN : l ↦ swift.HashLog.mk σ.synced (swift.SHash.mk sh) null null
            (swift.SHash.mk h) nm um $$ [Hl]
        · iExactEq Hl; rfl
        afterUnlink null null
      · have : tail = null := htl0.resolve_right (by simpa using Hif)
        subst this
        ihave HlN : l ↦ swift.HashLog.mk σ.synced (swift.SHash.mk sh) null null
            (swift.SHash.mk h) nm um $$ [Hl]
        · iExactEq Hl; rfl
        afterUnlink null null
    · -- the first node, others after it
      simp only [List.nil_append, firstL_cons] at hhd
      subst hhd
      have hq0 : q ≠ null := fun h0 => HnB (by simp [h0])
      have htlv : tail = lastL ((q, w) :: B') null := by
        have := htl.2.2 (by simp); rw [this]; simp [lastL_cons]
      have htna : tail ≠ head := by
        rw [htlv]; intro h0; apply haB; rw [← h0]; exact lastL_mem _ _ (by simp)
      rw [dseg_cons]
      ihave ⟨-, Hq, HB'⟩ := HB
      simp only [lastL_nil, firstL_cons, _root_.decide_true, Bool.not_true]
      try wp_auto
      simp only [decide_eq_false hq0, Bool.not_false]
      try wp_auto
      simp only [decide_eq_false htna]
      try wp_auto
      wp_apply (wp_mapDelete (K := swift.CommandId) (V := Loc)) $$ [$Hnm] as Hnm
      generalize hdn : GMap.delete x nodes = nodesN at hnodesN
      have hhdN : q = firstL nsN null := by rw [← hNs]; rfl
      have htlN : tailOk nsN tail := by
        rw [← hNs, htlv]; simp only [List.nil_append]; exact tailOk_last _ (by simp)
      ihave HnsN : dseg nsN null null $$ [Hq HB']
      · rw [← hNs, List.nil_append, dseg_cons]; iframe; ipureintro; exact hq0
      ihave HlN : l ↦ swift.HashLog.mk σ.synced (swift.SHash.mk sh) q tail
          (swift.SHash.mk h) nm um $$ [Hl]
      · iExactEq Hl; rfl
      afterUnlink q tail
    · -- the last node, others before it
      have hp0 : p ≠ null := fun h0 => HnA (by simp [h0])
      have hhne : head ≠ a := by
        rw [hhd, firstL_append]; intro h0; apply haA; rw [← h0]
        exact firstL_mem _ _ (by simp)
      have hhdA : head = firstL (A' ++ [(p, z)]) null := by
        rw [hhd, firstL_append]; obtain ⟨u, r, hu⟩ := List.exists_cons_of_ne_nil
          (show A' ++ [(p, z)] ≠ [] by simp)
        rw [hu]; rfl
      have htla : tail = a := by
        have := htl.2.2 (by simp); rw [this, lastL_snoc]
      subst htla
      ihave ⟨HA', HP'⟩ := (dseg_app A' [(p, z)] null tail).1 $$ HA
      simp only [firstL_cons] at *
      ihave ⟨-, Hp⟩ := (dseg_one _ _ _ _).1 $$ HP'
      simp only [lastL_snoc, firstL_nil]
      try wp_auto
      simp only [decide_eq_false hp0, Bool.not_false, _root_.decide_true, Bool.not_true]
      try wp_auto
      simp only [decide_eq_false hhne]
      try wp_auto
      wp_apply (wp_mapDelete (K := swift.CommandId) (V := Loc)) $$ [$Hnm] as Hnm
      generalize hdn : GMap.delete x nodes = nodesN at hnodesN
      have hhdN : head = firstL nsN null := by rw [← hNs, List.append_nil]; exact hhdA
      have htlN : tailOk nsN p := by
        rw [← hNs, List.append_nil]
        have := tailOk_last (A' ++ [(p, z)]) (by simp); simpa using this
      ihave HnsN : dseg nsN null null $$ [HA' Hp]
      · rw [← hNs, List.append_nil]
        iapply (dseg_app A' [(p, z)] null null).2
        simp only [firstL_cons]
        iframe HA'; iapply (dseg_one _ _ _ _).2; iframe Hp; ipureintro; exact hp0
      ihave HlN : l ↦ swift.HashLog.mk σ.synced (swift.SHash.mk sh) head p
          (swift.SHash.mk h) nm um $$ [Hl]
      · iExactEq Hl; rfl
      afterUnlink head p
    · -- a node in the middle
      have hp0 : p ≠ null := fun h0 => HnA (by simp [h0])
      have hq0 : q ≠ null := fun h0 => HnB (by simp [h0])
      have hhne : head ≠ a := by
        rw [hhd, firstL_append]; intro h0; apply haA; rw [← h0]
        exact firstL_mem _ _ (by simp)
      have hhdA : head = firstL (A' ++ [(p, z)] ++ (q, w) :: B') null := by
        rw [hhd]; cases A' <;> rfl
      have htlB : tail = lastL ((q, w) :: B') null := by
        have := htl.2.2 (by simp; omega); rw [this]; simp only [lastL_append, lastL_cons]
      have htne : tail ≠ a := by
        rw [htlB]; intro h0; apply haB; rw [← h0]; exact lastL_mem _ _ (by simp)
      ihave ⟨HA', HP'⟩ := (dseg_app A' [(p, z)] null a).1 $$ HA
      simp only [firstL_cons] at *
      ihave ⟨-, Hp⟩ := (dseg_one _ _ _ _).1 $$ HP'
      rw [dseg_cons]
      ihave ⟨-, Hq, HB'⟩ := HB
      simp only [lastL_snoc, firstL_cons]
      try wp_auto
      simp only [decide_eq_false hp0, Bool.not_false]
      try wp_auto
      simp only [decide_eq_false hq0, Bool.not_false]
      try wp_auto
      simp only [decide_eq_false hhne]
      try wp_auto
      simp only [decide_eq_false htne]
      try wp_auto
      wp_apply (wp_mapDelete (K := swift.CommandId) (V := Loc)) $$ [$Hnm] as Hnm
      generalize hdn : GMap.delete x nodes = nodesN at hnodesN
      have hhdN : head = firstL nsN null := by rw [← hNs]; exact hhdA
      have htlN : tailOk nsN tail := by
        rw [← hNs, htlB]
        have h2 : 2 ≤ (A' ++ [(p, z)] ++ (q, w) :: B').length := by simp; omega
        refine ⟨fun h0 => by simp at h0, fun h1 => by omega, fun _ => ?_⟩
        simp only [lastL_append, lastL_cons]
      ihave HnsN : dseg nsN null null $$ [HA' Hp Hq HB']
      · rw [← hNs]
        iapply (dseg_app (A' ++ [(p, z)]) ((q, w) :: B') null null).2
        simp only [firstL_cons, lastL_snoc]
        isplitl [HA' Hp]
        · iapply (dseg_app A' [(p, z)] null q).2
          simp only [firstL_cons]
          iframe HA'; iapply (dseg_one _ _ _ _).2; iframe Hp; ipureintro; exact hp0
        rw [dseg_cons]; iframe; ipureintro; exact hq0
      ihave HlN : l ↦ swift.HashLog.mk σ.synced (swift.SHash.mk sh) head tail
          (swift.SHash.mk h) nm um $$ [Hl]
      · iExactEq Hl; rfl
      afterUnlink head tail

theorem HashLog.Update.wp_proof (wp_update : HashLog.update.spec) : HashLog.Update.spec := by
  intro l σ x s hh P
  wp_start as ⟨Hown, #HP⟩
  try wp_auto
  wp_apply wp_update l σ x s hh P true $$ [$Hpkg $Hown $HP] as Hown
  try wp_auto
  iapply HΦ; iexact Hown

end proofs

end swift.hlog

end Perennial.github_com.imdea_software.swiftpaxos
