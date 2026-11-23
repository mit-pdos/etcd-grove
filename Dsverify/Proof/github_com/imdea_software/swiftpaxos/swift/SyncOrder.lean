/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/SyncOrder.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`syncOrder(msg)` (recovery.go) against the model's `sp.syncOrder`: the Go map `kept` built from
the `MSync`'s maps (phase and class 0, the model's `syncKept` has phase 3: `recOrder` reads only
the dependencies, `sp.recOrder_congr`), then `recOrder` over `sortedIds`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecOrderDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

set_option linter.unusedSimpArgs false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace sp

/-- `recOrder` reads only the kept dependencies. -/
theorem recOrder_congr (k k' : Kept) (ids : List CmdId)
    (h : ∀ x, (k.get x).map RecEntry.dep = (k'.get x).map RecEntry.dep) :
    recOrder k ids = recOrder k' ids := by
  have hn : ∀ d, (k.get d).isNone = (k'.get d).isNone := by
    intro d
    rw [← Option.isNone_map (f := RecEntry.dep), h, Option.isNone_map]
  unfold recOrder
  simp only [h, hn]

theorem Kept.get_map_of (l : List CmdId) (f : CmdId → RecEntry) (x : CmdId) :
    Kept.get (l.map (fun y => (y, f y))) x = if x ∈ l then some (f x) else none := by
  induction l with
  | nil => simp [Kept.get]
  | cons a l ih =>
    unfold Kept.get at ih ⊢
    rw [List.map_cons, List.find?_cons]
    by_cases hax : a = x
    · subst hax; simp
    · have hb : (a == x) = false := by simp [hax]
      simp only [hb]
      rw [ih]
      by_cases hx : x ∈ l
      · simp [hx]
      · simp [hx, Ne.symm hax]

/-- The model's entry of `x` in the Go `kept` of `syncOrder` (phase and class 0). -/
def syncEntryOf (M : SyncMsg) (x : CmdId) : RecEntry :=
  ((M.find? (·.1 == x)).map (fun p => (⟨0, p.2.1, p.2.2, 0⟩ : RecEntry))).getD ⟨0, default, [], 0⟩

theorem Kept.get_map_pairs (M : SyncMsg) (g : CmdId × Cmd × List CmdId → RecEntry) (x : CmdId) :
    Kept.get (M.map (fun p => (p.1, g p))) x = (M.find? (·.1 == x)).map g := by
  induction M with
  | nil => simp [Kept.get]
  | cons a l ih =>
    unfold Kept.get at ih ⊢
    rw [List.map_cons, List.find?_cons, List.find?_cons]
    cases h : a.1 == x <;> simp_all

/-- The Go `kept` of `syncOrder` against `syncKept`: the same dependencies, given its keys are
the `MSync`'s. -/
theorem syncOrder_go (M : SyncMsg) (l ids : List CmdId)
    (hl : ∀ x, x ∈ l ↔ x ∈ M.map Prod.fst)
    (hids : sortIds (M.map Prod.fst) = ids) :
    recOrder (l.map (fun y => (y, syncEntryOf M y))) ids = syncOrder M := by
  rw [syncOrder_eq, hids]
  apply recOrder_congr
  intro x
  rw [Kept.get_map_of, syncKept, Kept.get_map_pairs]
  by_cases hx : x ∈ l
  · rw [if_pos hx]
    have hm := (hl x).1 hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
    cases hf : M.find? (·.1 == p.1) with
    | none => rw [List.find?_eq_none] at hf; exact absurd (by simp) (hf p hp)
    | some q => simp [syncEntryOf, hf]
  · rw [if_neg hx]
    have : M.find? (·.1 == x) = none := by
      rw [List.find?_eq_none]; intro p hp hpx
      simp at hpx; subst hpx
      exact hx ((hl _).2 (List.mem_map.mpr ⟨p, hp, rfl⟩))
    rw [this]; rfl

end sp

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [swift.Assumptions]

theorem swift.syncOrder.wp_proof (wp_sortedIds : swift.sortedIds.specI (hG := hG))
    (wp_recOrder : swift.recOrder.specI (hG := hG)) : swift.syncOrder.specI (hG := hG) := by
  intro ls b M
  haveI := swift.hlog.cmdId_intoValInj (sem := sem)
  wp_start as ⟨HM, %HMl⟩
  iunfold swift.syncMaps at HM
  icases HM with ⟨%rep, %bl, %ph, %cm, %dp, %phM, %cmM, %dpM, #Hls, #Hph, #Hcm, #Hdp, %HMk, #HMl⟩
  wp_auto
  wp_apply (wp_map_make1 (K := swift.CommandId) (V := Loc)) as %km Hkm
  iStructNamed Hls
  wp_auto
  ipersist msg
  ipersist kept
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (wp_map_for_range (fun keys i => iprop(
      (∃ x : swift.CommandId, cmdId_ptr ↦ x) ∗ ⌜0 ≤ i⌝ ∗
      swift.keptOwn km (((keys.take i.toNat).map toCmdId).map (fun y => (y, sp.syncEntryOf M y)))
        (fun _ => false)))) $$ Hph
  iintro %keys %Hkeys
  isplitl [cmdId Hkm]
  · isplitl [cmdId]
    · iexists _; iexact cmdId
    isplitr
    · ipureintro; omega
    iunfold swift.keptOwn
    iexists ∅
    iframe
    isplitr
    · ipureintro; simp [sp.Kept.get]
    · iapply BigSepM.bigSepM_empty.2; iempintro
  isplitl []
  · imodintro
    iintro %i %key %v %Hiv ⟨⟨%x, cmdId⟩, %Hi0, Hk⟩
    wp_auto
    have hkM : toCmdId key ∈ M.map Prod.fst := (HMk.2.2 key).1 (by rw [Hiv.2]; rfl)
    obtain ⟨p, hpf⟩ : ∃ p, M.find? (·.1 == toCmdId key) = some p := by
      apply Option.isSome_iff_exists.mp
      rw [List.find?_isSome]
      obtain ⟨p, hp, hp1⟩ := List.mem_map.mp hkM
      exact ⟨p, hp, by simp [hp1]⟩
    have hpM := List.mem_of_find?_eq_some hpf
    have hp1 : p.1 = toCmdId key := by have := List.find?_some hpf; simpa using this
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hpM
    ihave Hpj := BigSepL.bigSepL_lookup hj $$ HMl
    icases Hpj with ⟨%vs, %dsl, %Hvd, #Hvs, #Hdsl⟩
    rw [hp1, ofCmdId_toCmdId] at Hvd
    wp_apply (wp_map_lookup1 _ _ cm cmM key) $$ Hcm as -
    wp_apply (wp_map_lookup1 _ _ dp dpM key) $$ Hdp as -
    rw [Hvd.1, Hvd.2]
    simp only [Option.getD_some]
    iunfold swift.keptOwn at Hk
    icases Hk with ⟨%mk, Hm, %Hmk, Hents⟩
    wp_apply (wp_mapInsert _ km mk key «$r0_ptr») $$ Hm as Hm
    unfold forMapPostcondition
    iright; ileft
    isplitr; · ipureintro; rfl
    have htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_succ, Hiv.1]; rfl
    have hkey_nin : key ∉ keys.take i.toNat := by
      intro hin
      have hnd := List.take_append_drop (i.toNat + 1) keys ▸ Hkeys.2.2
      rw [show i.toNat + 1 = (i + 1).toNat by omega, htake, List.append_assoc,
        List.nodup_append] at hnd
      exact hnd.2.2 key hin key (by simp) rfl
    have hinj : ∀ a b : swift.CommandId, toCmdId a = toCmdId b → a = b :=
      fun a b h => by simpa using congrArg ofCmdId h
    have hget : ∀ (l : List swift.CommandId) (c : swift.CommandId),
        sp.Kept.get ((l.map toCmdId).map (fun y => (y, sp.syncEntryOf M y))) (toCmdId c) =
          if c ∈ l then some (sp.syncEntryOf M (toCmdId c)) else none := by
      intro l c
      rw [sp.Kept.get_map_of]
      by_cases hc : c ∈ l
      · rw [if_pos (List.mem_map_of_mem hc), if_pos hc]
      · rw [if_neg, if_neg hc]
        intro h; obtain ⟨a, ha, hac⟩ := List.mem_map.mp h; rw [hinj a c hac] at ha; exact hc ha
    have hold : ∀ c, (mk !! c).isSome = decide (c ∈ keys.take i.toNat) := by
      intro c; rw [Hmk.2, hget]; by_cases hc : c ∈ keys.take i.toNat <;> simp [hc]
    have hmkey : mk !! key = none := by
      have := hold key; rw [decide_eq_false hkey_nin] at this
      cases h : mk !! key with
      | none => rfl
      | some _ => rw [h] at this; cases this
    isplitl [cmdId]
    · iexists _; iexact cmdId
    isplitr
    · ipureintro; omega
    iunfold swift.keptOwn
    iexists _
    iframe Hm
    isplitr
    · ipureintro
      constructor
      · rw [htake, List.map_map, List.map_map]
        rw [List.map_map] at Hmk
        have hnd : (keys.take i.toNat ++ [key]).Nodup := by
          rw [← htake]; exact (List.take_sublist _ _).nodup Hkeys.2.2
        exact List.Pairwise.map _ (fun a b hab h => hab (hinj a b (by simpa using h))) hnd
      · intro c
        rw [hget]
        by_cases hc : c = key
        · subst hc; rw [GMap.lookup_insert_eq, htake]; simp
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm hc), hold, htake]
          by_cases hc' : c ∈ keys.take i.toNat <;> simp [hc', hc]
    iapply (BigSepM.bigSepM_insert_elim (PROP := IProp netDistGF)) $$ [«$r0»] [Hents]
    · iexists sp.syncEntryOf M (toCmdId key)
      isplitr
      · ipureintro; rw [hget, htake]; simp
      iunfold swift.recOwn
      iexists W64 0, W64 0, vs, dsl
      have he : sp.syncEntryOf M (toCmdId key) = ⟨0, p.2.1, p.2.2, 0⟩ := by
        simp [sp.syncEntryOf, hpf]
      rw [he]
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe
      isplitr; · iexact Hvs
      isplitr; · iexact Hdsl
      ipureintro; simp
    · iapply (BigSepM.bigSepM_mono (Φ := fun c p' => iprop(∃ e,
          ⌜sp.Kept.get (((keys.take i.toNat).map toCmdId).map (fun y => (y, sp.syncEntryOf M y)))
            (toCmdId c) = some e⌝ ∗ swift.recOwn p' e false))) $$ Hents
      intro c v _
      iintro ⟨%e, %he, Hr⟩
      iexists e
      iframe Hr
      ipureintro
      rw [hget] at he ⊢
      by_cases hc : c ∈ keys.take i.toNat
      · rw [if_pos hc] at he; rw [htake, if_pos (List.mem_append_left _ hc)]; exact he
      · rw [if_neg hc] at he; cases he
  iintro ⟨-, %_, Hk⟩ -
  have hinj : ∀ a b : swift.CommandId, toCmdId a = toCmdId b → a = b :=
    fun a b h => by simpa using congrArg ofCmdId h
  rw [show (↑phM.size : Int).toNat = keys.length by rw [Hkeys.2.1]; omega, List.take_length]
  iunfold swift.keptOwn at Hk
  icases Hk with ⟨%mk, Hm, %Hmk, Hents⟩
  have hkeysM : ∀ c, c ∈ keys ↔ toCmdId c ∈ M.map Prod.fst := fun c => by
    rw [Hkeys.1, HMk.2.2]
  have hmk : ∀ c, (mk !! c).isSome = true ↔ c ∈ keys := by
    intro c
    rw [Hmk.2, sp.Kept.get_map_of]
    constructor
    · intro h
      by_cases hc : toCmdId c ∈ keys.map toCmdId
      · obtain ⟨a, ha, hac⟩ := List.mem_map.mp hc; rw [hinj a c hac] at ha; exact ha
      · rw [if_neg hc] at h; cases h
    · intro h; rw [if_pos (List.mem_map_of_mem h)]; rfl
  have hsz : GMap.size mk ≤ 2 ^ 62 := by
    rw [GMap.size_eq_length mk keys Hkeys.2.2 (fun c => (hmk c).symm), Hkeys.2.1,
      GMap.size_eq_length phM (M.map (fun p => ofCmdId p.1))
        (List.Pairwise.map _ (fun a b hab h => hab (by simpa using congrArg toCmdId h))
          (List.pairwise_map.mp HMk.2.1))
        (fun c => by
          rw [HMk.2.2, List.mem_map, List.mem_map]
          constructor
          · rintro ⟨p, hp, hpc⟩; exact ⟨p, hp, by rw [← hpc]; simp⟩
          · rintro ⟨p, hp, hpc⟩; exact ⟨p, hp, by rw [hpc]; simp⟩)]
    simpa using HMl
  wp_auto
  wp_apply (wp_sortedIds km mk (DFrac.own 1)) $$ [Hm] as %isl %ids ⟨Hm, Hids, %Hids⟩
  · iframe; ipureintro; exact hsz
  wp_apply (wp_recOrder km _ (fun _ => false) isl ids (DFrac.own 1)) $$ [Hm Hents Hids]
    as %osl ⟨-, -, Ho, Hocap⟩
  · iframe
    isplitl [Hm Hents]
    · iunfold swift.keptOwn
      iexists mk
      iframe
      ipureintro; exact Hmk
    ipureintro
    refine ⟨Hids.1, fun c hc => ?_⟩
    rw [← Hmk.2]; exact (Hids.2.1 c).1 hc
  have hperm : List.Perm (M.map Prod.fst) (ids.map toCmdId) := by
    rw [List.perm_ext_iff_of_nodup HMk.2.1
      (List.Pairwise.map _ (fun a b hab h => hab (hinj a b h)) Hids.1)]
    intro x
    constructor
    · intro hx
      have : ofCmdId x ∈ keys := (hkeysM _).2 (by simpa using hx)
      have := (Hids.2.1 _).2 ((hmk _).2 this)
      exact List.mem_map.mpr ⟨_, this, by simp⟩
    · intro hx
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
      exact (hkeysM a).1 ((hmk a).1 ((Hids.2.1 a).1 ha))
  rw [sp.syncOrder_go M (keys.map toCmdId) (ids.map toCmdId)
    (fun x => by
      constructor
      · intro hx; obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx; exact (hkeysM a).1 ha
      · intro hx; exact List.mem_map.mpr ⟨ofCmdId x, (hkeysM _).2 (by simpa using hx), by simp⟩)
    (Hids.2.2 _ hperm)]
  iapply HΦ
  iframe

end proof

end Perennial.github_com.imdea_software.swiftpaxos
