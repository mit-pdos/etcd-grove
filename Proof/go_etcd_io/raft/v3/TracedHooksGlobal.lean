/-
Lean-first (no Rocq counterpart). Trace-check's S5 (2026-11-09): the proof of the global step's law
(`trCap_fire.statement`, `TracedHooksDraft.lean`): inside the logger's update, the simulation's
invariant steps by the line's effect (`simRun_lineEffect`), the node's share moves to the next phase,
the state's facts are kept (the caller's `FxPres`) and give the invariants (`simFx_violated`, with
raft's vote table from its commit invariant).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedHooksDraft
public import Proof.go_etcd_io.raft.v3.TraceSimMatch
public import Proof.go_etcd_io.raft.v3.TraceSimRun

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section pure
variable [GooseExts]

/-- A line not named `BecomeFollower` is never skipped as one. -/
theorem isBF_false (t : Etcdraft.Trace) (ts : Etcdraft.TState) (h : (t.line ts.l).ev.name ≠ "BecomeFollower") :
    t.isBecomeFollowerInUpdateTermOrReturnToFollower ts = false := by
  unfold Etcdraft.Trace.isBecomeFollowerInUpdateTermOrReturnToFollower Etcdraft.Trace.isEvent
  simp [h]

theorem isBootstrapName_bf (n : String) (h : Etcdraft.isBootstrapName n = false) : n ≠ "BecomeFollower" := by
  intro e; subst e; simp [Etcdraft.isBootstrapName] at h

/-- **The simulation invariant's pure clauses after a phase step's line** (node `id`'s share
`(cs, P)` becoming `(toC a', P ++ P')`, the state `σ` stepping to `withNode σ (idAbs id) a'`). -/
theorem simStep_pure (C : List w64) (L : List TraceEv) (σ : Etcdraft.State)
    (A : GMap w64 (ServerC × List Etcdraft.Msg)) (phP : List Etcdraft.Msg) (id : w64) (hC : id ∈ C)
    (hnd : C.Nodup) (P : List Etcdraft.Msg) (e : TraceEv) (a' : Etcdraft.Server) (P' : List Etcdraft.Msg)
    (hrun : SimRun C L σ) (hsrv : σ.server = confAbs C)
    (hA : ∀ i ∈ C, ∃ Q, A !! i = some (toC σ.server (σ.s (idAbs i)), Q)) (hAid : A !! id = some (toC σ.server (σ.s (idAbs id)), P))
    (hAn : ∀ i, i ∉ C → A !! i = none)
    (hsrcA : ∀ i ∈ C, ∀ x ∈ ((A !! i).map Prod.snd).getD [], x.source = idAbs i)
    (hsrcP : ∀ x ∈ P', x.source = idAbs id)
    (hP : BagRep σ.pendingMessages ((C.flatMap (fun i => ((A !! i).map Prod.snd).getD [])) ++ phP))
    (hpv : σ.preVote = false) (hcq : σ.checkQuorum = false)
    (hname : Etcdraft.isBootstrapName (gsStr e.name) = false)
    (hle : LineEffect C false e (idAbs id) (σ.s (idAbs id)) a' none _root_.id
      (fun b => P'.foldl Etcdraft.Bag.with b) (fun _ => False))
    (hσinv : σ.violated = .ok none)
    (hinv : (withNode σ (idAbs id) a' _root_.id (fun b => P'.foldl Etcdraft.Bag.with b)).violated = .ok none) :
    let σ' := withNode σ (idAbs id) a' _root_.id (fun b => P'.foldl Etcdraft.Bag.with b)
    let A' := A.insert id (toC σ.server a', P ++ P')
    SimRun C (L ++ [e]) σ' ∧ σ'.server = confAbs C ∧
      (∀ i ∈ C, ∃ Q, A' !! i = some (toC σ'.server (σ'.s (idAbs i)), Q)) ∧ (∀ i, i ∉ C → A' !! i = none) ∧
      (∀ i ∈ C, ∀ x ∈ ((A' !! i).map Prod.snd).getD [], x.source = idAbs i) ∧
      BagRep σ'.pendingMessages ((C.flatMap (fun i => ((A' !! i).map Prod.snd).getD [])) ++ phP) ∧
      σ'.messages = σ.messages := by
  intro σ' A'
  have hsrv' : σ'.server = σ.server := rfl
  have hs_id : σ'.s (idAbs id) = a' := by simp [σ', withNode]
  have hs_ne : ∀ j, j ≠ idAbs id → σ'.s j = σ.s j := by intro j hj; simp [σ', withNode, hj]
  refine ⟨?_, by rw [hsrv', hsrv], ?_, ?_, ?_, ?_, rfl⟩
  · apply simRun_lineEffect C L σ hrun hσinv e false (idAbs id) _ a' none _ _ _ hle hsrv rfl hpv hcq
    · intro lines ln _ hp
      have := parseLine_ev _ _ _ hp
      have hb : Etcdraft.isBootstrapName ln.ev.name = false := by rw [this]; exact hname
      have hlen := parseLines_length _ _ (by assumption)
      simp only [List.length_map] at hlen
      rw [← hlen]; exact bootFlags_nonBoot _ _ _ hb
    · intro lines ln pl hl hp
      have hlen := parseLines_length _ _ hl
      simp only [List.length_map] at hlen
      apply isBF_false
      rw [linesTrace_line_last C lines ln _ (by simp; omega), parseLine_ev _ _ _ hp]
      exact isBootstrapName_bf _ hname
    · intro _ _; trivial
    · intro v hv; exact False.elim hv
    · exact hinv
  · intro i hi
    by_cases h : i = id
    · subst h; exact ⟨P ++ P', by simp [A', hs_id, hsrv']⟩
    · obtain ⟨Q, hQ⟩ := hA i hi
      refine ⟨Q, ?_⟩
      rw [show A' !! i = A !! i from GMap.lookup_insert_ne _ _ (Ne.symm h), hQ, hsrv',
        hs_ne _ (fun e => h (idAbs_inj.1 e))]
  · intro i hi
    have : id ≠ i := fun e => hi (e ▸ hC)
    rw [show A' !! i = A !! i from GMap.lookup_insert_ne _ _ this]; exact hAn i hi
  · intro i hi x hx
    by_cases h : i = id
    · subst h
      have hl : A' !! i = some (toC σ.server a', P ++ P') := GMap.lookup_insert _ _ _
      rw [hl] at hx
      simp only [Option.map_some, Option.getD_some, List.mem_append] at hx
      rcases hx with hx | hx
      · exact hsrcA _ hi x (by rw [hAid]; simpa using hx)
      · exact hsrcP x hx
    · rw [show A' !! i = A !! i from GMap.lookup_insert_ne _ _ (Ne.symm h)] at hx; exact hsrcA i hi x hx
  · have hfold := bagRep_foldl_with P' _ _ hP
    apply bagRep_perm _ _ _ hfold
    have := flatMap_update_perm C (fun i => ((A !! i).map Prod.snd).getD []) (fun i => ((A' !! i).map Prod.snd).getD [])
      id hnd hC P' (by simp [A', hAid]) (fun j hj => by
        rw [show A' !! j = A !! j from GMap.lookup_insert_ne _ _ (Ne.symm hj)])
    simp only [List.append_assoc]
    refine (List.Perm.append_left _ List.perm_append_comm).trans ?_
    rw [← List.append_assoc]
    exact List.Perm.append_right phP this.symm

theorem bag_mem_domain_of_count (b : Etcdraft.Bag) (m : Etcdraft.Msg) (h : 0 < Etcdraft.Bag.count b m) :
    m ∈ b.domain := by
  unfold Etcdraft.Bag.count at h
  cases hf : b.find? (fun it => it.1 == m) with
  | none => rw [hf] at h; simp at h
  | some it =>
    have hm := List.mem_of_find?_eq_some hf
    have he : it.1 = m := by simpa using List.find?_some hf
    exact List.mem_map.2 ⟨it, hm, he⟩

/-- **The receive line's pure core** (`simStep_pure`'s counterpart, the token `k`'s message `m`
consumed). -/
theorem simStepR_pure (C : List w64) (L : List TraceEv) (σ : Etcdraft.State)
    (A : GMap w64 (ServerC × List Etcdraft.Msg)) (B : GMap Nat Etcdraft.Msg) (phP phM : List Etcdraft.Msg)
    (id : w64) (hC : id ∈ C)
    (hnd : C.Nodup) (P : List Etcdraft.Msg) (e : TraceEv) (a' : Etcdraft.Server) (P' Pph : List Etcdraft.Msg)
    (k : Nat) (m : Etcdraft.Msg) (Mid : Etcdraft.Server → Prop)
    (hrun : SimRun C L σ) (hsrv : σ.server = confAbs C)
    (hA : ∀ i ∈ C, ∃ Q, A !! i = some (toC σ.server (σ.s (idAbs i)), Q)) (hAid : A !! id = some (toC σ.server (σ.s (idAbs id)), P))
    (hAn : ∀ i, i ∉ C → A !! i = none)
    (hsrcA : ∀ i ∈ C, ∀ x ∈ ((A !! i).map Prod.snd).getD [], x.source = idAbs i)
    (hsrcP : ∀ x ∈ P', x.source = idAbs id)
    (hP : BagRep σ.pendingMessages ((C.flatMap (fun i => ((A !! i).map Prod.snd).getD [])) ++ phP))
    (hM : BagRep σ.messages ((GMap.toList B).map Prod.snd ++ phM)) (hBk : B !! k = some m)
    (huniq : MsgsUniq σ)
    (hpv : σ.preVote = false) (hcq : σ.checkQuorum = false)
    (hname : Etcdraft.isBootstrapName (gsStr e.name) = false)
    (hmatch : ∀ ln, Etcdraft.parseLine 0 (evConv e) = .ok ln → recvPred ln m = true)
    (hle : LineEffect C false e (idAbs id) (σ.s (idAbs id)) a' (some m) (fun b => b.without m)
      (fun b => (P' ++ Pph).foldl Etcdraft.Bag.with b) Mid)
    (hσinv : σ.violated = .ok none)
    (hmids : ∀ v, Mid v → (withNode σ (idAbs id) v _root_.id _root_.id).violated = .ok none)
    (hinv : (withNode σ (idAbs id) a' (fun b => b.without m) (fun b => (P' ++ Pph).foldl Etcdraft.Bag.with b)).violated = .ok none) :
    let σ' := withNode σ (idAbs id) a' (fun b => b.without m) (fun b => (P' ++ Pph).foldl Etcdraft.Bag.with b)
    let A' := A.insert id (toC σ.server a', P ++ P')
    SimRun C (L ++ [e]) σ' ∧ σ'.server = confAbs C ∧
      (∀ i ∈ C, ∃ Q, A' !! i = some (toC σ'.server (σ'.s (idAbs i)), Q)) ∧ (∀ i, i ∉ C → A' !! i = none) ∧
      (∀ i ∈ C, ∀ x ∈ ((A' !! i).map Prod.snd).getD [], x.source = idAbs i) ∧
      BagRep σ'.pendingMessages ((C.flatMap (fun i => ((A' !! i).map Prod.snd).getD [])) ++ (phP ++ Pph)) ∧
      BagRep σ'.messages ((GMap.toList (B.delete k)).map Prod.snd ++ phM) := by
  intro σ' A'
  have hsrv' : σ'.server = σ.server := rfl
  have hs_id : σ'.s (idAbs id) = a' := by simp [σ', withNode]
  have hs_ne : ∀ j, j ≠ idAbs id → σ'.s j = σ.s j := by intro j hj; simp [σ', withNode, hj]
  -- the token's message is in flight
  have hml : m ∈ (GMap.toList B).map Prod.snd ++ phM :=
    List.mem_append_left _ (List.mem_map.2 ⟨(k, m), (GMap.mem_toList B k m).2 hBk, rfl⟩)
  have hcnt : 0 < Etcdraft.Bag.count σ.messages m := by rw [hM.2.2 m]; exact List.count_pos_iff.2 hml
  have hmd := bag_mem_domain_of_count _ _ hcnt
  refine ⟨?_, by rw [hsrv', hsrv], ?_, ?_, ?_, ?_, ?_⟩
  · apply simRun_lineEffect C L σ hrun hσinv e false (idAbs id) _ a' (some m) _ _ _ hle hsrv rfl hpv hcq
    · intro lines ln _ hp
      have := parseLine_ev _ _ _ hp
      have hb : Etcdraft.isBootstrapName ln.ev.name = false := by rw [this]; exact hname
      have hlen := parseLines_length _ _ (by assumption)
      simp only [List.length_map] at hlen
      rw [← hlen]; exact bootFlags_nonBoot _ _ _ hb
    · intro lines ln pl hl hp
      have hlen := parseLines_length _ _ hl
      simp only [List.length_map] at hlen
      apply isBF_false
      rw [linesTrace_line_last C lines ln _ (by simp; omega), parseLine_ev _ _ _ hp]
      exact isBootstrapName_bf _ hname
    · intro ln hp
      refine ⟨hM.1, hmd, hcnt, fun m' hm' hne => ?_⟩
      cases h : recvPred ln m'
      · rfl
      · exact absurd (huniq ln m' m (List.mem_append_left _ hm') (List.mem_append_left _ hmd) h (hmatch ln hp)) hne
    · exact hmids
    · exact hinv
  · intro i hi
    by_cases h : i = id
    · subst h; exact ⟨P ++ P', by simp [A', hs_id, hsrv']⟩
    · obtain ⟨Q, hQ⟩ := hA i hi
      refine ⟨Q, ?_⟩
      rw [show A' !! i = A !! i from GMap.lookup_insert_ne _ _ (Ne.symm h), hQ, hsrv',
        hs_ne _ (fun e => h (idAbs_inj.1 e))]
  · intro i hi
    have : id ≠ i := fun e => hi (e ▸ hC)
    rw [show A' !! i = A !! i from GMap.lookup_insert_ne _ _ this]; exact hAn i hi
  · intro i hi x hx
    by_cases h : i = id
    · subst h
      have hl : A' !! i = some (toC σ.server a', P ++ P') := GMap.lookup_insert _ _ _
      rw [hl] at hx
      simp only [Option.map_some, Option.getD_some, List.mem_append] at hx
      rcases hx with hx | hx
      · exact hsrcA _ hi x (by rw [hAid]; simpa using hx)
      · exact hsrcP x hx
    · rw [show A' !! i = A !! i from GMap.lookup_insert_ne _ _ (Ne.symm h)] at hx; exact hsrcA i hi x hx
  · have hfold := bagRep_foldl_with (P' ++ Pph) _ _ hP
    apply bagRep_perm _ _ _ hfold
    have := flatMap_update_perm C (fun i => ((A !! i).map Prod.snd).getD []) (fun i => ((A' !! i).map Prod.snd).getD [])
      id hnd hC P' (by simp [A', hAid]) (fun j hj => by
        rw [show A' !! j = A !! j from GMap.lookup_insert_ne _ _ (Ne.symm hj)])
    -- F ++ phP ++ (P' ++ Pph) ~ (F ++ P') ++ (phP ++ Pph) ~ F' ++ (phP ++ Pph)
    refine List.Perm.trans ?_ (List.Perm.append_right (phP ++ Pph) this.symm)
    simp only [List.append_assoc]
    apply List.Perm.append_left
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.Perm.append_right Pph List.perm_append_comm
  · have hw := bagRep_without _ _ m hM hml
    apply bagRep_perm _ _ _ hw
    have hp : ((GMap.toList B).map Prod.snd ++ phM).Perm (m :: ((GMap.toList (B.delete k)).map Prod.snd ++ phM)) := by
      have := (GMap.mapToList_delete B k m hBk).map Prod.snd
      simpa using this.append_right phM
    have := hp.erase m
    simpa using this

theorem toList_union_perm {V : Type} (m1 m2 : GMap Nat V) (hd : GMap.Disjoint m1 m2) :
    (GMap.toList (m1 ∪ m2)).Perm (GMap.toList m1 ++ GMap.toList m2) := by
  rw [List.perm_ext_iff_of_nodup (GMap.NoDup_map_to_list _)]
  · rintro ⟨k, v⟩
    rw [List.mem_append, GMap.mem_toList, GMap.mem_toList, GMap.mem_toList, GMap.lookup_union_Some_raw]
    constructor
    · rintro (h | ⟨-, h⟩)
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h
      · right; refine ⟨?_, h⟩
        cases h1 : m1 !! k with
        | none => rfl
        | some _ =>
          exfalso
          have e1 : (m1 !! k).isSome = true := by rw [h1]; rfl
          have e2 : (m2 !! k).isSome = true := by rw [h]; rfl
          exact hd k e1 e2
  · rw [List.nodup_append]
    refine ⟨GMap.NoDup_map_to_list _, GMap.NoDup_map_to_list _, ?_⟩
    rintro ⟨k, v⟩ h1 ⟨k', v'⟩ h2 e
    simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
    rw [GMap.mem_toList] at h1 h2
    exact hd k (by simp [h1]) (by simp [h2])

/-- **The `Ready` line's pure core**: node `id`'s pending messages (its share `P` and its phantoms)
move to the network (the share's under the new tokens `Bn`, the phantoms among the network's
phantoms), its share empties, its server persisted. -/
theorem simStepReady_pure (C : List w64) (L : List TraceEv) (σ : Etcdraft.State)
    (A : GMap w64 (ServerC × List Etcdraft.Msg)) (B Bn : GMap Nat Etcdraft.Msg) (phP phM : List Etcdraft.Msg)
    (id : w64) (hC : id ∈ C) (hnd : C.Nodup) (P : List Etcdraft.Msg)
    (e : TraceEv) (s : NState) (cfg : CfgM) (hev : NodeEvOf (W64 8) id s cfg e) (hout : cfg.outgoing = ∅)
    (hrun : SimRun C L σ) (hsrv : σ.server = confAbs C)
    (hA : ∀ i ∈ C, ∃ Q, A !! i = some (toC σ.server (σ.s (idAbs i)), Q))
    (hAid : A !! id = some (toC σ.server (σ.s (idAbs id)), P))
    (hAn : ∀ i, i ∉ C → A !! i = none)
    (hsrcA : ∀ i ∈ C, ∀ x ∈ ((A !! i).map Prod.snd).getD [], x.source = idAbs i)
    (hP : BagRep σ.pendingMessages ((C.flatMap (fun i => ((A !! i).map Prod.snd).getD [])) ++ phP))
    (hM : BagRep σ.messages ((GMap.toList B).map Prod.snd ++ phM))
    (hBn : ((GMap.toList Bn).map Prod.snd).Perm P) (hdisj : GMap.Disjoint Bn B)
    (hσinv : σ.violated = .ok none) (hinv : (σ.ready (idAbs id)).violated = .ok none) :
    let σ' := σ.ready (idAbs id)
    let A' := A.insert id (toC σ.server (σ'.s (idAbs id)), [])
    let src := fun x : Etcdraft.Msg => x.source == idAbs id
    SimRun C (L ++ [e]) σ' ∧ σ'.server = confAbs C ∧
      (∀ i ∈ C, ∃ Q, A' !! i = some (toC σ'.server (σ'.s (idAbs i)), Q)) ∧ (∀ i, i ∉ C → A' !! i = none) ∧
      (∀ i ∈ C, ∀ x ∈ ((A' !! i).map Prod.snd).getD [], x.source = idAbs i) ∧
      BagRep σ'.pendingMessages ((C.flatMap (fun i => ((A' !! i).map Prod.snd).getD [])) ++ phP.filter (fun x => !src x)) ∧
      BagRep σ'.messages ((GMap.toList (Bn ∪ B)).map Prod.snd ++ (phM ++ phP.filter src)) := by
  intro σ' A' src
  have hsrv' : σ'.server = σ.server := rfl
  have hs_ne : ∀ j, j ≠ idAbs id → σ'.s j = σ.s j := by
    intro j hj; simp [σ', Etcdraft.State.ready, Etcdraft.State.persistState, Etcdraft.State.upd, hj]
  -- the shares' lists: the old is the new with `P`
  have hperm := flatMap_update_perm C (fun i => ((A' !! i).map Prod.snd).getD []) (fun i => ((A !! i).map Prod.snd).getD [])
    id hnd hC P (by simp [A', hAid]) (fun j hj => by
      rw [show A' !! j = A !! j from GMap.lookup_insert_ne _ _ (Ne.symm hj)])
  -- every message of a share is its node's
  have hsrcF : ∀ x ∈ C.flatMap (fun i => ((A' !! i).map Prod.snd).getD []), src x = false := by
    intro x hx
    obtain ⟨i, hi, hx⟩ := List.mem_flatMap.1 hx
    by_cases h : i = id
    · subst h; simp [A'] at hx
    · rw [show A' !! i = A !! i from GMap.lookup_insert_ne _ _ (Ne.symm h)] at hx
      have := hsrcA i hi x hx
      simp only [src, this, beq_eq_false_iff_ne]
      exact fun e => h (idAbs_inj.1 e)
  have hsrcPv : ∀ x ∈ P, src x = true := by
    intro x hx; simp only [src, beq_iff_eq]; exact hsrcA id hC x (by rw [hAid]; simpa using hx)
  refine ⟨simRun_ready_any C L σ hrun hσinv e id s cfg hev hout hC hinv, by rw [hsrv', hsrv], ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    by_cases h : i = id
    · rw [h]; exact ⟨[], by simp only [A', hsrv']; rw [GMap.lookup_insert]⟩
    · obtain ⟨Q, hQ⟩ := hA i hi
      refine ⟨Q, ?_⟩
      rw [show A' !! i = A !! i from GMap.lookup_insert_ne _ _ (Ne.symm h), hQ, hsrv',
        hs_ne _ (fun e => h (idAbs_inj.1 e))]
  · intro i hi
    have : id ≠ i := fun e => hi (e ▸ hC)
    rw [show A' !! i = A !! i from GMap.lookup_insert_ne _ _ this]; exact hAn i hi
  · intro i hi x hx
    by_cases h : i = id
    · subst h; simp [A'] at hx
    · rw [show A' !! i = A !! i from GMap.lookup_insert_ne _ _ (Ne.symm h)] at hx; exact hsrcA i hi x hx
  · -- the pending bag: the old minus the node's messages
    have hf := bagCnt_filter _ _ (fun x => src x) hP
    have hm := bagCnt_minus _ _ hf _ _ hP
    show BagRep (σ.pendingMessages.minus (σ.pendingMessages.filterMsgs src)) _
    refine ⟨hm.1, hm.2.1, fun x => ?_⟩
    rw [hm.2.2 x]
    simp only []
    have e1 : List.count x (C.flatMap (fun i => ((A !! i).map Prod.snd).getD []) ++ phP) =
        List.count x (C.flatMap (fun i => ((A' !! i).map Prod.snd).getD [])) + List.count x P + List.count x phP := by
      rw [List.count_append, hperm.count_eq, List.count_append]
    rw [e1, List.count_append]
    by_cases hx : src x = true
    · have h0 : List.count x (C.flatMap (fun i => ((A' !! i).map Prod.snd).getD [])) = 0 :=
        List.count_eq_zero.2 (fun hm' => by rw [hsrcF x hm'] at hx; cases hx)
      have h1 : List.count x (phP.filter (fun x => !src x)) = 0 :=
        List.count_eq_zero.2 (fun hm' => by have := (List.mem_filter.1 hm').2; simp [hx] at this)
      simp only [hx, ↓reduceIte, h0, h1]; omega
    · have h0 : List.count x P = 0 := List.count_eq_zero.2 (fun hm' => hx (hsrcPv x hm'))
      have h1 : List.count x (phP.filter (fun x => !src x)) = List.count x phP :=
        List.count_filter (by simp [hx])
      simp only [hx, Bool.false_eq_true, ↓reduceIte, h0, h1]; omega
  · -- the network's bag: the node's messages added
    have hf := bagCnt_filter _ _ (fun x => src x) hP
    have hp := bagCnt_plus σ.messages _ hM _ _ hf
    show BagRep ((σ.pendingMessages.filterMsgs src).plus σ.messages) _
    refine ⟨hp.1, hp.2.1, fun x => ?_⟩
    rw [hp.2.2 x]
    simp only []
    have hU := (toList_union_perm Bn B hdisj).map Prod.snd
    have e2 : List.count x ((GMap.toList (Bn ∪ B)).map Prod.snd ++ (phM ++ phP.filter src)) =
        List.count x P + List.count x ((GMap.toList B).map Prod.snd) + List.count x phM +
          List.count x (phP.filter src) := by
      rw [List.count_append, hU.count_eq, List.map_append, List.count_append, hBn.count_eq, List.count_append]
      omega
    have e1 : List.count x (C.flatMap (fun i => ((A !! i).map Prod.snd).getD []) ++ phP) =
        List.count x (C.flatMap (fun i => ((A' !! i).map Prod.snd).getD [])) + List.count x P + List.count x phP := by
      rw [List.count_append, hperm.count_eq, List.count_append]
    rw [e2, e1, List.count_append]
    by_cases hx : src x = true
    · have h0 : List.count x (C.flatMap (fun i => ((A' !! i).map Prod.snd).getD [])) = 0 :=
        List.count_eq_zero.2 (fun hm' => by rw [hsrcF x hm'] at hx; cases hx)
      have h1 : List.count x (phP.filter src) = List.count x phP := List.count_filter hx
      simp only [hx, ↓reduceIte, h0, h1]; omega
    · have h0 : List.count x P = 0 := List.count_eq_zero.2 (fun hm' => hx (hsrcPv x hm'))
      have h1 : List.count x (phP.filter src) = 0 :=
        List.count_eq_zero.2 (fun hm' => hx (List.mem_filter.1 hm').2)
      simp only [hx, Bool.false_eq_true, ↓reduceIte, h0, h1]; omega

end pure

end EtcdGrove
end Perennial

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A pure consequence, the resource kept. -/
theorem keep_pure {P : IProp GF} {φ : Prop} (h : P ⊢ ⌜φ⌝) : P ⊢ P ∗ ⌜φ⌝ :=
  (and_intro .rfl h).trans persistent_and_sep.1

/-- **The global step's law** (`trCap_fire.statement`). -/
theorem trCap_fire : trCap_fire.statement (GF := GF) := by
  intro γd γ r id c tl E Φ Φ' hps
  iintro ⟨Hcap, #Htl, Hfx⟩
  iunfold FxPres at Hfx
  icases Hfx with #Hfx
  iunfold trCap at Hcap
  icases Hcap with ⟨%tn, %C, %tl', %cs, %P, #Hdir, %Hpf, #Htl', #Hlg, %Hnn, #Hinv, #Hrinv, Hnode, %HΦ⟩
  icombine Htl Htl' gives %Htleq
  subst Htleq
  obtain ⟨hvC, hperm, hout, hC⟩ := Hpf
  have hnd : C.Nodup := hperm.nodup_iff.1 (NoDup_elements _)
  iunfold TraceFire
  iexists tn
  iframe Hdir Hlg
  isplitr; · ipureintro; exact Hnn
  iintro %e %HE
  iauintro
  unfold atomic_acc
  iinv Hinv with >Hi Hclose
  iunfold simInv at Hi
  icases Hi with ⟨%L, %σ, %A, %B, %phP, %phM, HL, HA, HB, #Hfσ, %Hp⟩
  iunfold raftLogInv at Hrinv
  have Hsub : (↑(raftLogN γ) : CoPset) ⊆ ⊤ \ ↑(simNS γ) :=
    mask_ndot_ne' (raftN γ) "log" "tracesim" (by decide)
  iinv Hrinv with Hr Hrclose
  iunfold raftLogInvBody at Hr
  icases Hr with ⟨%lc, Hc, Hj, >Htbl, Hw, Hrest⟩
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists L
  iunfold traceFrag at HL
  iunfold traceAuth
  iframe HL
  isplit
  · iintro HL
    imod Hmask with -
    imod Hrclose $$ [Hc Hj Htbl Hw Hrest] with -
    · inext; iunfold raftLogInvBody; iexists lc; iframe
    imod Hclose $$ [HL HA HB] with -
    · inext; iunfold simInv; iexists L, σ, A, B, phP, phM; iunfold traceFrag; iframe HL HA HB Hfσ; ipureintro; exact Hp
    imodintro
    iframe Hnode
  · iintro HL
    imod Hmask with -
    iunfold simNode at Hnode
    icases ghost_map_lookup $$ HA Hnode with %HAid
    obtain ⟨hrun, hsrv, hA, hAn, hPb, hMb, hpv, hcq, hsrcA⟩ := Hp
    obtain ⟨Q, hQ⟩ := hA id hC
    rw [HAid] at hQ
    simp only [Option.some.injEq, Prod.mk.injEq] at hQ
    obtain ⟨hcs, hQP⟩ := hQ
    obtain ⟨hname, hall⟩ := hps C cs P HΦ ⟨hperm, hout, hC⟩ e HE
    obtain ⟨a', P', hΦ', hsrcP, hle⟩ := hall (σ.s (idAbs id)) (by rw [hcs, hsrv])
    icases keep_pure (simFx_violated γ C σ hsrv) $$ [$Htbl $Hfσ] with ⟨⟨Htbl, -⟩, %hv⟩
    have hpre : Φ C cs P ∧ E e ∧ toC (confAbs C) (σ.s (idAbs id)) = cs ∧ Φ' C (toC (confAbs C) a') (P ++ P') ∧
        LineEffect C false e (idAbs id) (σ.s (idAbs id)) a' none _root_.id
          (fun b => List.foldl Etcdraft.Bag.with b P') (fun _ => False) ∧
        σ.server = confAbs C ∧ σ.s (idAbs id) = σ.s (idAbs id) ∧ σ.preVote = false ∧ σ.checkQuorum = false ∧
        σ.violated = .ok none :=
      ⟨HΦ, HE, by rw [hcs, hsrv], hΦ', hle, hsrv, rfl, hpv, hcq, hv⟩
    icases Hfx $$ %C %cs %P %e %(σ.s (idAbs id)) %a' %P' %σ %hpre Htbl Hfσ with ⟨Htbl, #Hfσ'⟩
    have hsrv' : (withNode σ (idAbs id) a' _root_.id (fun b => List.foldl Etcdraft.Bag.with b P')).server =
        confAbs C := hsrv
    icases keep_pure (simFx_violated γ C _ hsrv') $$ [$Htbl $Hfσ'] with ⟨⟨Htbl, -⟩, %hv'⟩
    have hAid : A !! id = some (toC σ.server (σ.s (idAbs id)), P) := by rw [HAid, hcs]
    obtain ⟨hrun', hsrvN, hA', hAn', hsrc', hPb', hM'⟩ :=
      simStep_pure C L σ A phP id hC hnd P e a' P' hrun hsrv hA hAid hAn hsrcA hsrcP hPb hpv hcq hname
        hle hv hv'
    imod ghost_map_update (toC σ.server a', P ++ P') $$ HA Hnode with ⟨HA, Hnode⟩
    imod Hrclose $$ [Hc Hj Htbl Hw Hrest] with -
    · inext; iunfold raftLogInvBody; iexists lc; iframe
    imod Hclose $$ [HL HA HB] with -
    · inext; iunfold simInv
      iexists L ++ [e], withNode σ (idAbs id) a' _root_.id (fun b => List.foldl Etcdraft.Bag.with b P'),
        A.insert id (toC σ.server a', P ++ P'), B, phP, phM
      iunfold traceFrag; iframe HL HA HB Hfσ'
      ipureintro
      exact ⟨hrun', hsrvN, hA', hAn', hPb', by rw [hM']; exact hMb, hpv, hcq, hsrc'⟩
    imodintro
    iunfold trCap
    iexists tn, C, tl, toC σ.server a', P ++ P'
    iunfold simNode
    iframe Hdir Htl Hlg Hinv Hnode
    isplitr; · ipureintro; exact ⟨hvC, hperm, hout, hC⟩
    isplitr; · ipureintro; exact Hnn
    isplitr; · iunfold raftLogInv; iexact Hrinv
    ipureintro; rw [hsrv]; exact hΦ'

/-- **The global step's law for a receive line** (`trCap_fire_recv.statement`). -/
theorem trCap_fire_recv : trCap_fire_recv.statement (GF := GF) := by
  intro γd γ r id c tl E k m Mid Φ Φ' hps
  iintro ⟨Hcap, #Htl, Hfx, ⟨%tn0, #Hdir0, Htok⟩⟩
  iunfold FxPresR at Hfx
  icases Hfx with #Hfx
  iunfold trCap at Hcap
  icases Hcap with ⟨%tn, %C, %tl', %cs, %P, #Hdir, %Hpf, #Htl', #Hlg, %Hnn, #Hinv, #Hrinv, Hnode, %HΦ⟩
  icombine Htl Htl' gives %Htleq
  subst Htleq
  iunfold traceDir at Hdir Hdir0
  icases dghostVar_agree γd tn _ tn0 _ $$ Hdir Hdir0 with %Htn
  subst Htn
  ihave #Hdir : traceDir γd tn $$ [Hdir]
  · iunfold traceDir; iexact Hdir
  obtain ⟨hvC, hperm, hout, hC⟩ := Hpf
  have hnd : C.Nodup := hperm.nodup_iff.1 (NoDup_elements _)
  iunfold TraceFire
  iexists tn
  iframe Hdir Hlg
  isplitr; · ipureintro; exact Hnn
  iintro %e %HE
  iauintro
  unfold atomic_acc
  iinv Hinv with >Hi Hclose
  iunfold simInv at Hi
  icases Hi with ⟨%L, %σ, %A, %B, %phP, %phM, HL, HA, HB, #Hfσ, %Hp⟩
  iunfold raftLogInv at Hrinv
  have Hsub : (↑(raftLogN γ) : CoPset) ⊆ ⊤ \ ↑(simNS γ) :=
    mask_ndot_ne' (raftN γ) "log" "tracesim" (by decide)
  iinv Hrinv with Hr Hrclose
  iunfold raftLogInvBody at Hr
  icases Hr with ⟨%lc, Hc, Hj, >Htbl, Hw, Hrest⟩
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists L
  iunfold traceFrag at HL
  iunfold traceAuth
  iframe HL
  isplit
  · iintro HL
    imod Hmask with -
    imod Hrclose $$ [Hc Hj Htbl Hw Hrest] with -
    · inext; iunfold raftLogInvBody; iexists lc; iframe
    imod Hclose $$ [HL HA HB] with -
    · inext; iunfold simInv; iexists L, σ, A, B, phP, phM; iunfold traceFrag; iframe HL HA HB Hfσ; ipureintro; exact Hp
    imodintro
    iframe Hnode Htok
  · iintro HL
    imod Hmask with -
    iunfold simNode at Hnode
    icases ghost_map_lookup $$ HA Hnode with %HAid
    obtain ⟨hrun, hsrv, hA, hAn, hPb, hMb, hpv, hcq, hsrcA⟩ := Hp
    obtain ⟨Q, hQ⟩ := hA id hC
    rw [HAid] at hQ
    simp only [Option.some.injEq, Prod.mk.injEq] at hQ
    obtain ⟨hcs, hQP⟩ := hQ
    obtain ⟨hname, hmatch, hall⟩ := hps C cs P HΦ ⟨hperm, hout, hC⟩ e HE
    obtain ⟨a', P', Pph, hΦ', hsrcP, hle⟩ := hall (σ.s (idAbs id)) (by rw [hcs, hsrv])
    iunfold inFlight at Htok
    icases ghost_map_lookup $$ HB Htok with %HBk
    icases keep_pure (simFx_violated γ C σ hsrv) $$ [$Htbl $Hfσ] with ⟨⟨Htbl, -⟩, %hv0⟩
    have hmd : m ∈ σ.messages.domain := by
      have hml : m ∈ (GMap.toList B).map Prod.snd ++ phM :=
        List.mem_append_left _ (List.mem_map.2 ⟨(k, m), (GMap.mem_toList B k m).2 HBk, rfl⟩)
      exact bag_mem_domain_of_count _ _ (by rw [hMb.2.2 m]; exact List.count_pos_iff.2 hml)
    have hpre : Φ C cs P ∧ E e ∧ toC (confAbs C) (σ.s (idAbs id)) = cs ∧ Φ' C (toC (confAbs C) a') (P ++ P') ∧
        LineEffect C false e (idAbs id) (σ.s (idAbs id)) a' (some m) (fun b => b.without m)
          (fun b => List.foldl Etcdraft.Bag.with b (P' ++ Pph)) Mid ∧
        σ.server = confAbs C ∧ σ.s (idAbs id) = σ.s (idAbs id) ∧ σ.preVote = false ∧ σ.checkQuorum = false ∧
        σ.violated = .ok none ∧ m ∈ σ.messages.domain :=
      ⟨HΦ, HE, by rw [hcs, hsrv], hΦ', hle, hsrv, rfl, hpv, hcq, hv0, hmd⟩
    icases Hfx $$ %C %cs %P %e %(σ.s (idAbs id)) %a' %P' %Pph %σ %hpre Htbl Hfσ with ⟨Htbl, #Hfσ', #Hmid⟩
    ihave #Hfσc := Hfσ
    iunfold simFx at Hfσc
    icases Hfσc with ⟨-, -, %hfx⟩
    have huq : MsgsUniq σ := hfx.2.2
    icases keep_pure (simFx_violated γ C σ hsrv) $$ [$Htbl $Hfσ] with ⟨⟨Htbl, -⟩, %hv⟩
    have hsrv' : (withNode σ (idAbs id) a' (fun b => b.without m) (fun b => List.foldl Etcdraft.Bag.with b (P' ++ Pph))).server =
        confAbs C := hsrv
    -- the intermediate states' invariants, by contradiction on one
    by_cases hmids : ∀ v, Mid v → (withNode σ (idAbs id) v _root_.id _root_.id).violated = .ok none
    rotate_left
    · simp only [Classical.not_forall] at hmids
      obtain ⟨v, hv, hbad⟩ := hmids
      ihave #Hfv := Hmid $$ %v %hv
      have hsv : (withNode σ (idAbs id) v _root_.id _root_.id).server = confAbs C := hsrv
      icases keep_pure (simFx_violated γ C _ hsv) $$ [$Htbl $Hfv] with ⟨-, %hv'⟩
      exact absurd hv' hbad
    icases keep_pure (simFx_violated γ C _ hsrv') $$ [$Htbl $Hfσ'] with ⟨⟨Htbl, -⟩, %hv'⟩
    have hAid : A !! id = some (toC σ.server (σ.s (idAbs id)), P) := by rw [HAid, hcs]
    obtain ⟨hrun', hsrvN, hA', hAn', hsrc', hPb', hM'⟩ :=
      simStepR_pure C L σ A B phP phM id hC hnd P e a' P' Pph k m Mid hrun hsrv hA hAid hAn hsrcA hsrcP hPb hMb HBk huq hpv hcq
        hname hmatch hle hv hmids hv'
    imod ghost_map_update (toC σ.server a', P ++ P') $$ HA Hnode with ⟨HA, Hnode⟩
    imod ghost_map_delete $$ HB Htok with HB
    imod Hrclose $$ [Hc Hj Htbl Hw Hrest] with -
    · inext; iunfold raftLogInvBody; iexists lc; iframe
    imod Hclose $$ [HL HA HB] with -
    · inext; iunfold simInv
      iexists L ++ [e], withNode σ (idAbs id) a' (fun b => b.without m) (fun b => List.foldl Etcdraft.Bag.with b (P' ++ Pph)),
        A.insert id (toC σ.server a', P ++ P'), B.delete k, phP ++ Pph, phM
      iunfold traceFrag; iframe HL HA HB Hfσ'
      ipureintro
      exact ⟨hrun', hsrvN, hA', hAn', hPb', hM', hpv, hcq, hsrc'⟩
    imodintro
    iunfold trCap
    iexists tn, C, tl, toC σ.server a', P ++ P'
    iunfold simNode
    iframe Hdir Htl Hlg Hinv Hnode
    isplitr; · ipureintro; exact ⟨hvC, hperm, hout, hC⟩
    isplitr; · ipureintro; exact Hnn
    isplitr; · iunfold raftLogInv; iexact Hrinv
    ipureintro; rw [hsrv]; exact hΦ'

end ghost

end EtcdGrove
end Perennial
