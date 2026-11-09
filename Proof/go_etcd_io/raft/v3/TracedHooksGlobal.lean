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
theorem shareStep_pure (C : List w64) (σ : Etcdraft.State)
    (A : GMap w64 (ServerC × List Etcdraft.Msg)) (phP : List Etcdraft.Msg) (id : w64) (hC : id ∈ C)
    (hnd : C.Nodup) (P : List Etcdraft.Msg) (a' : Etcdraft.Server) (P' : List Etcdraft.Msg)
    (hsrv : σ.server = confAbs C)
    (hA : ∀ i ∈ C, ∃ Q, A !! i = some (toC σ.server (σ.s (idAbs i)), Q)) (hAid : A !! id = some (toC σ.server (σ.s (idAbs id)), P))
    (hAn : ∀ i, i ∉ C → A !! i = none)
    (hsrcA : ∀ i ∈ C, ∀ x ∈ ((A !! i).map Prod.snd).getD [], x.source = idAbs i)
    (hsrcP : ∀ x ∈ P', x.source = idAbs id)
    (hP : BagRep σ.pendingMessages ((C.flatMap (fun i => ((A !! i).map Prod.snd).getD [])) ++ phP))
 :
    let σ' := withNode σ (idAbs id) a' _root_.id (fun b => P'.foldl Etcdraft.Bag.with b)
    let A' := A.insert id (toC σ.server a', P ++ P')
    σ'.server = confAbs C ∧
      (∀ i ∈ C, ∃ Q, A' !! i = some (toC σ'.server (σ'.s (idAbs i)), Q)) ∧ (∀ i, i ∉ C → A' !! i = none) ∧
      (∀ i ∈ C, ∀ x ∈ ((A' !! i).map Prod.snd).getD [], x.source = idAbs i) ∧
      BagRep σ'.pendingMessages ((C.flatMap (fun i => ((A' !! i).map Prod.snd).getD [])) ++ phP) ∧
      σ'.messages = σ.messages := by
  intro σ' A'
  have hsrv' : σ'.server = σ.server := rfl
  have hs_id : σ'.s (idAbs id) = a' := by simp [σ', withNode]
  have hs_ne : ∀ j, j ≠ idAbs id → σ'.s j = σ.s j := by intro j hj; simp [σ', withNode, hj]
  refine ⟨by rw [hsrv', hsrv], ?_, ?_, ?_, ?_, rfl⟩
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
  refine ⟨?_, shareStep_pure C σ A phP id hC hnd P a' P' hsrv hA hAid hAn hsrcA hsrcP hP⟩
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

/-- A bound on a map's keys. -/
noncomputable def keyBound {V : Type} (B : GMap Nat V) : Nat :=
  (GMap.toList B).foldl (fun a p => max a (p.1 + 1)) 0

theorem keyBound_gt {V : Type} (B : GMap Nat V) (k : Nat) (v : V) (h : B !! k = some v) : k < keyBound B := by
  unfold keyBound
  have hm : (k, v) ∈ GMap.toList B := (GMap.mem_toList B k v).2 h
  suffices ∀ (l : List (Nat × V)) (a : Nat), (k, v) ∈ l ∨ k < a →
      k < l.foldl (fun a p => max a (p.1 + 1)) a by exact this _ 0 (Or.inl hm)
  intro l
  induction l with
  | nil => intro a h; simp at h; exact h
  | cons p l ih =>
    intro a h
    simp only [List.foldl_cons]
    apply ih
    rcases h with h | h
    · rw [List.mem_cons] at h
      rcases h with h | h
      · right; subst h; omega
      · left; exact h
    · right; omega

theorem mapSeq_values_perm {V : Type} : ∀ (start : Nat) (l : List V),
    ((GMap.toList (GMap.mapSeq start l)).map Prod.snd).Perm l := by
  intro start l
  induction l generalizing start with
  | nil => show (((∅ : GMap Nat V).toList).map Prod.snd).Perm []; rw [GMap.toList_empty]; rfl
  | cons v l ih =>
    rw [GMap.mapSeq_cons]
    have hfresh : GMap.mapSeq (start + 1) l !! start = none := by
      rw [GMap.lookup_map_seq]; simp
      intro h; omega
    have := (GMap.mapToList_insert (GMap.mapSeq (start + 1) l) start v hfresh).map Prod.snd
    simp only [List.map_cons] at this
    exact this.trans ((ih (start + 1)).cons v)

theorem mapSeq_disjoint {V : Type} (B : GMap Nat V) (l : List V) :
    GMap.Disjoint (GMap.mapSeq (keyBound B) l) B := by
  intro k h1 h2
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h2
  have hk := keyBound_gt B k v hv
  have : GMap.mapSeq (keyBound B) l !! k = none := by rw [GMap.lookup_map_seq]; simp; omega
  rw [this] at h1; cases h1

/-- `gsStr` is injective (a byte is a valid character). -/
theorem gsStr_inj {a b : GoString} (h : gsStr a = gsStr b) : a = b := by
  have ht : ∀ l : GoString, (gsStr l).toList = l.map (fun c => Char.ofNat c.toNat) :=
    fun _ => String.toList_ofList
  have h1 : (gsStr a).toList = (gsStr b).toList := congrArg _ h
  rw [ht, ht] at h1
  have hinj : ∀ x y : w8, Char.ofNat x.toNat = Char.ofNat y.toNat → x = y := by
    intro x y hxy
    have k : ∀ n, n < 256 → (Char.ofNat n).toNat = n := by
      intro n hn; unfold Char.ofNat; rw [dite_eq_left (by unfold Nat.isValidChar; omega)]; rfl
    have := congrArg Char.toNat hxy
    rw [k _ x.isLt, k _ y.isLt] at this
    exact BitVec.eq_of_toNat_eq this
  clear h ht
  induction a generalizing b with
  | nil => cases b with
    | nil => rfl
    | cons _ _ => simp at h1
  | cons x a ih => cases b with
    | nil => simp at h1
    | cons y b =>
      simp only [List.map_cons, List.cons.injEq] at h1
      rw [hinj x y h1.1, ih h1.2]

theorem lastOf_snoc_self (L : List TraceEv) (e : TraceEv) (n : GoString) (h : e.nid = n) :
    LastOf (L ++ [e]) n (some e) :=
  ⟨L, [], rfl, h, by simp⟩

theorem lastOf_snoc_other (L : List TraceEv) (e : TraceEv) (n : GoString) (o : Option TraceEv)
    (h : e.nid ≠ n) (hl : LastOf L n o) : LastOf (L ++ [e]) n o := by
  cases o with
  | none =>
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hl x hx
    · simp at hx; subst hx; exact h
  | some e0 =>
    obtain ⟨L1, L2, hL, hn, hL2⟩ := hl
    refine ⟨L1, L2 ++ [e], by rw [hL]; simp, hn, ?_⟩
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hL2 x hx
    · simp at hx; subst hx; exact h

/-- **The flags after a node's non-bootstrap line.** -/
theorem bootClause_step (C : List w64) (L : List TraceEv) (e : TraceEv) (ln : Etcdraft.Line) (id : w64)
    (Bt : GMap w64 (Bool × Option TraceEv)) (hp : Etcdraft.parseLine 0 (evConv e) = .ok ln) (hn : ln.nid = idAbs id)
    (hnid : e.nid = decStr id) (hself : booted (L ++ [e]) (idAbs id))
    (h : ∀ i ∈ C, ∃ b o, Bt !! i = some (b, o) ∧ (b = true ↔ booted L (idAbs i)) ∧ LastOf L (decStr i) o ∧
      (b = true → o.isSome)) :
    ∀ i ∈ C, ∃ b o, (Bt.insert id (true, some e)) !! i = some (b, o) ∧ (b = true ↔ booted (L ++ [e]) (idAbs i)) ∧
      LastOf (L ++ [e]) (decStr i) o ∧ (b = true → o.isSome) := by
  intro i hi
  by_cases hii : i = id
  · subst hii
    exact ⟨true, some e, GMap.lookup_insert _ _ _, by simp; exact hself,
      lastOf_snoc_self L e _ hnid, fun _ => rfl⟩
  · obtain ⟨b, o, hb', hiff, hlo, hso⟩ := h i hi
    refine ⟨b, o, by rw [GMap.lookup_insert_ne _ _ (Ne.symm hii)]; exact hb', ?_, ?_, hso⟩
    · rw [booted_snoc_other L e ln _ hp (by rw [hn]; exact fun e => hii (idAbs_inj.1 e).symm)]
      exact hiff
    · exact lastOf_snoc_other L e _ o (by rw [hnid]; exact fun h => hii (decStr_inj h).symm) hlo

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
  intro γd γ r id c tl E Φ Φ' Λ Λ' hps hΛ
  iintro ⟨Hcap, #Htl, Hfx⟩
  iunfold FxPres at Hfx
  icases Hfx with #Hfx
  iunfold trCap at Hcap
  icases Hcap with ⟨%bt0, Hcap⟩
  iunfold trCapB at Hcap
  icases Hcap with ⟨%tn, %C, %tl', %cs, %P, #Hdir, %Hpf, #Htl', #Hlg, %Hnn, #Hinv, #Hrinv, Hnode, Hbt, %HΦ⟩
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
  icases Hi with ⟨%L, %σ, %A, %B, %phP, %phM, %Bt, HL, HA, HB, HBt, #Hfσ, %Hp⟩
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
    imod Hclose $$ [HL HA HB HBt] with -
    · inext; iunfold simInv; iexists L, σ, A, B, phP, phM, Bt; iunfold traceFrag; iframe HL HA HB HBt Hfσ; ipureintro; exact Hp
    imodintro
    iframe Hnode Hbt
  · iintro HL
    imod Hmask with -
    iunfold simNode at Hnode
    icases ghost_map_lookup $$ HA Hnode with %HAid
    obtain ⟨hrun, hsrv, hA, hAn, hPb, hMb, hpv, hcq, hsrcA, hbtC⟩ := Hp
    obtain ⟨Q, hQ⟩ := hA id hC
    rw [HAid] at hQ
    simp only [Option.some.injEq, Prod.mk.injEq] at hQ
    obtain ⟨hcs, hQP⟩ := hQ
    obtain ⟨hnid, hname, hall⟩ := hps C cs P HΦ ⟨hperm, hout, hC⟩ e HE
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
    icases Hbt with ⟨%o0, Hbt, -⟩
    iunfold simBoot at Hbt
    imod ghost_map_update (true, some e) $$ HBt Hbt with ⟨HBt, Hbt⟩
    have hle0 := hle
    obtain ⟨ln, hpl, hnl, -⟩ := hle0
    have hbl : Etcdraft.isBootstrapName ln.ev.name = false := by rw [parseLine_ev _ _ _ hpl]; exact hname
    imod Hrclose $$ [Hc Hj Htbl Hw Hrest] with -
    · inext; iunfold raftLogInvBody; iexists lc; iframe
    imod Hclose $$ [HL HA HB HBt] with -
    · inext; iunfold simInv
      iexists L ++ [e], withNode σ (idAbs id) a' _root_.id (fun b => List.foldl Etcdraft.Bag.with b P'),
        A.insert id (toC σ.server a', P ++ P'), B, phP, phM, Bt.insert id (true, some e)
      iunfold traceFrag; iframe HL HA HB HBt Hfσ'
      ipureintro
      exact ⟨hrun', hsrvN, hA', hAn', hPb', by rw [hM']; exact hMb, hpv, hcq, hsrc',
        bootClause_step C L e ln id Bt hpl hnl hnid (booted_snoc_self L e ln _ hpl hnl hbl) hbtC⟩
    imodintro
    iunfold trCapB
    iexists tn, C, tl, toC σ.server a', P ++ P'
    iunfold simNode
    iframe Hdir Htl Hlg Hinv Hnode
    isplitr; · ipureintro; exact ⟨hvC, hperm, hout, hC⟩
    isplitr; · ipureintro; exact Hnn
    isplitr; · iunfold raftLogInv; iexact Hrinv
    isplitl [Hbt]; · iexists some e; iunfold simBoot; iframe Hbt; ipureintro; exact hΛ e HE
    ipureintro; rw [hsrv]; exact hΦ'

/-- **The global step's law for a `Ready` line** (`trCap_fire_ready.statement`). -/
theorem trCap_fire_ready : trCap_fire_ready.statement (GF := GF) := by
  intro γd γ r id c tl E Φ Φ' Λ Λ' hps hΛ
  iintro ⟨Hcap, #Htl, Hfx⟩
  iunfold FxPresReady at Hfx
  icases Hfx with #Hfx
  iunfold trCap at Hcap
  icases Hcap with ⟨%bt0, Hcap⟩
  iunfold trCapB at Hcap
  icases Hcap with ⟨%tn, %C, %tl', %cs, %P, #Hdir, %Hpf, #Htl', #Hlg, %Hnn, #Hinv, #Hrinv, Hnode, Hbt, %HΦ⟩
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
  icases Hi with ⟨%L, %σ, %A, %B, %phP, %phM, %Bt, HL, HA, HB, HBt, #Hfσ, %Hp⟩
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
    imod Hclose $$ [HL HA HB HBt] with -
    · inext; iunfold simInv; iexists L, σ, A, B, phP, phM, Bt; iunfold traceFrag; iframe HL HA HB HBt Hfσ; ipureintro; exact Hp
    imodintro
    iframe Hnode Hbt
  · iintro HL
    imod Hmask with -
    iunfold simNode at Hnode
    icases ghost_map_lookup $$ HA Hnode with %HAid
    obtain ⟨hrun, hsrv, hA, hAn, hPb, hMb, hpv, hcq, hsrcA, hbtC⟩ := Hp
    obtain ⟨Q, hQ⟩ := hA id hC
    rw [HAid] at hQ
    simp only [Option.some.injEq, Prod.mk.injEq] at hQ
    obtain ⟨hcs, hQP⟩ := hQ
    obtain ⟨⟨s0, cfg0, hev0, hout0⟩, hall⟩ := hps C cs P HΦ ⟨hperm, hout, hC⟩ e HE
    have hΦ' := hall (σ.s (idAbs id)) (by rw [hcs, hsrv])
    icases keep_pure (simFx_violated γ C σ hsrv) $$ [$Htbl $Hfσ] with ⟨⟨Htbl, -⟩, %hv⟩
    have hpre : Φ C cs P ∧ E e ∧ σ.server = confAbs C ∧ toC (confAbs C) (σ.s (idAbs id)) = cs ∧
        σ.preVote = false ∧ σ.checkQuorum = false ∧ σ.violated = .ok none :=
      ⟨HΦ, HE, hsrv, by rw [hcs, hsrv], hpv, hcq, hv⟩
    icases Hfx $$ %C %cs %P %e %σ %hpre Htbl Hfσ with ⟨Htbl, #Hfσ'⟩
    have hsrv' : (σ.ready (idAbs id)).server = confAbs C := hsrv
    icases keep_pure (simFx_violated γ C _ hsrv') $$ [$Htbl $Hfσ'] with ⟨⟨Htbl, -⟩, %hv'⟩
    have hAid : A !! id = some (toC σ.server (σ.s (idAbs id)), P) := by rw [HAid, hcs]
    obtain ⟨hrun', hsrvN, hA', hAn', hsrc', hPb', hM'⟩ :=
      simStepReady_pure C L σ A B (GMap.mapSeq (keyBound B) P) phP phM id hC hnd P e s0 cfg0 hev0 hout0
        hrun hsrv hA hAid hAn hsrcA hPb hMb (mapSeq_values_perm _ P) (mapSeq_disjoint B P) hv hv'
    imod ghost_map_update (toC σ.server ((σ.ready (idAbs id)).s (idAbs id)), ([] : List Etcdraft.Msg)) $$ HA Hnode
      with ⟨HA, Hnode⟩
    imod ghost_map_insert_big (GMap.mapSeq (keyBound B) P) (mapSeq_disjoint B P) $$ HB with ⟨HB, Htoks⟩
    icases Hbt with ⟨%o0, Hbt, -⟩
    iunfold simBoot at Hbt
    imod ghost_map_update (true, some e) $$ HBt Hbt with ⟨HBt, Hbt⟩
    have hev1 := hev0
    obtain ⟨hname1, hnid1, -, hvote1, -, -, -, ⟨xs1, ys1, -, hys1, hconf1⟩, hmsg1, -, -, -, -⟩ := hev1
    rw [hout0, elements_empty_nil] at hys1
    have hys10 := List.Perm.eq_nil hys1
    subst hys10
    have hname1' : gsStr e.name = "Ready" := by
      simp only [evtNames] at hname1
      have : e.name = go!"Ready" := by have := hname1; simp at this; exact this.symm
      rw [this]; rfl
    have hpl := parseLine_node 0 e id s0.vote xs1 [] hnid1 hvote1 hconf1 hmsg1 (by rw [hname1']; rfl)
      (by rw [hname1']; decide)
    imod Hrclose $$ [Hc Hj Htbl Hw Hrest] with -
    · inext; iunfold raftLogInvBody; iexists lc; iframe
    imod Hclose $$ [HL HA HB HBt] with -
    · inext; iunfold simInv
      iexists L ++ [e], σ.ready (idAbs id),
        A.insert id (toC σ.server ((σ.ready (idAbs id)).s (idAbs id)), ([] : List Etcdraft.Msg)),
        GMap.mapSeq (keyBound B) P ∪ B, phP.filter (fun x => !(x.source == idAbs id)),
        phM ++ phP.filter (fun x => x.source == idAbs id), Bt.insert id (true, some e)
      iunfold traceFrag; iframe HL HA HB HBt Hfσ'
      ipureintro
      exact ⟨hrun', hsrvN, hA', hAn', hPb', hM', hpv, hcq, hsrc',
        bootClause_step C L e _ id Bt hpl rfl hnid1 (booted_snoc_self L e _ _ hpl rfl (by simp [evConv, hname1']; rfl)) hbtC⟩
    imodintro
    isplitl [Hnode Hbt]
    · iunfold trCapB
      iexists tn, C, tl, toC σ.server ((σ.ready (idAbs id)).s (idAbs id)), []
      iunfold simNode
      iframe Hdir Htl Hlg Hinv Hnode
      isplitr; · ipureintro; exact ⟨hvC, hperm, hout, hC⟩
      isplitr; · ipureintro; exact Hnn
      isplitr; · iunfold raftLogInv; iexact Hrinv
      isplitl [Hbt]; · iexists some e; iunfold simBoot; iframe Hbt; ipureintro; exact hΛ e HE
      ipureintro
      have : (σ.ready (idAbs id)).s (idAbs id) = { σ.s (idAbs id) with durable := Etcdraft.durableOf (σ.s (idAbs id)) } := by
        simp [Etcdraft.State.ready, Etcdraft.State.persistState, Etcdraft.State.upd]
      rw [this, hsrv]; exact hΦ'
    · iexists tn, P, GMap.mapSeq (keyBound B) P
      iframe Hdir
      isplitr; · ipureintro; exact mapSeq_values_perm _ P
      iunfold inFlight
      iexact Htoks

/-- **The global step's law for a receive line** (`trCap_fire_recv.statement`). -/
theorem trCap_fire_recv : trCap_fire_recv.statement (GF := GF) := by
  intro γd γ r id c tl E k m Mid Φ Φ' Λ Λ' hps hΛ
  iintro ⟨Hcap, #Htl, Hfx, ⟨%tn0, #Hdir0, Htok⟩⟩
  iunfold FxPresR at Hfx
  icases Hfx with #Hfx
  iunfold trCap at Hcap
  icases Hcap with ⟨%bt0, Hcap⟩
  iunfold trCapB at Hcap
  icases Hcap with ⟨%tn, %C, %tl', %cs, %P, #Hdir, %Hpf, #Htl', #Hlg, %Hnn, #Hinv, #Hrinv, Hnode, Hbt, %HΦ⟩
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
  icases Hi with ⟨%L, %σ, %A, %B, %phP, %phM, %Bt, HL, HA, HB, HBt, #Hfσ, %Hp⟩
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
    imod Hclose $$ [HL HA HB HBt] with -
    · inext; iunfold simInv; iexists L, σ, A, B, phP, phM, Bt; iunfold traceFrag; iframe HL HA HB HBt Hfσ; ipureintro; exact Hp
    imodintro
    iframe Hnode Hbt Htok
  · iintro HL
    imod Hmask with -
    iunfold simNode at Hnode
    icases ghost_map_lookup $$ HA Hnode with %HAid
    obtain ⟨hrun, hsrv, hA, hAn, hPb, hMb, hpv, hcq, hsrcA, hbtC⟩ := Hp
    obtain ⟨Q, hQ⟩ := hA id hC
    rw [HAid] at hQ
    simp only [Option.some.injEq, Prod.mk.injEq] at hQ
    obtain ⟨hcs, hQP⟩ := hQ
    obtain ⟨hnid, hname, hmatch, hall⟩ := hps C cs P HΦ ⟨hperm, hout, hC⟩ e HE
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
    icases Hbt with ⟨%o0, Hbt, -⟩
    iunfold simBoot at Hbt
    imod ghost_map_update (true, some e) $$ HBt Hbt with ⟨HBt, Hbt⟩
    have hle0 := hle
    obtain ⟨ln, hpl, hnl, -⟩ := hle0
    have hbl : Etcdraft.isBootstrapName ln.ev.name = false := by rw [parseLine_ev _ _ _ hpl]; exact hname
    imod Hrclose $$ [Hc Hj Htbl Hw Hrest] with -
    · inext; iunfold raftLogInvBody; iexists lc; iframe
    imod Hclose $$ [HL HA HB HBt] with -
    · inext; iunfold simInv
      iexists L ++ [e], withNode σ (idAbs id) a' (fun b => b.without m) (fun b => List.foldl Etcdraft.Bag.with b (P' ++ Pph)),
        A.insert id (toC σ.server a', P ++ P'), B.delete k, phP ++ Pph, phM, Bt.insert id (true, some e)
      iunfold traceFrag; iframe HL HA HB HBt Hfσ'
      ipureintro
      exact ⟨hrun', hsrvN, hA', hAn', hPb', hM', hpv, hcq, hsrc', bootClause_step C L e ln id Bt hpl hnl hnid (booted_snoc_self L e ln _ hpl hnl hbl) hbtC⟩
    imodintro
    iunfold trCapB
    iexists tn, C, tl, toC σ.server a', P ++ P'
    iunfold simNode
    iframe Hdir Htl Hlg Hinv Hnode
    isplitr; · ipureintro; exact ⟨hvC, hperm, hout, hC⟩
    isplitr; · ipureintro; exact Hnn
    isplitr; · iunfold raftLogInv; iexact Hrinv
    isplitl [Hbt]; · iexists some e; iunfold simBoot; iframe Hbt; ipureintro; exact hΛ e HE
    ipureintro; rw [hsrv]; exact hΦ'

/-- **The global step's law for a bootstrap line** (`trCap_fire_boot.statement`). -/
theorem trCap_fire_boot : trCap_fire_boot.statement (GF := GF) := by
  intro γd γ r id c tl E Φ Λ Λ' hE hΛ
  iintro ⟨Hcap, #Htl⟩
  iunfold trCapB at Hcap
  icases Hcap with ⟨%tn, %C, %tl', %cs, %P, #Hdir, %Hpf, #Htl', #Hlg, %Hnn, #Hinv, #Hrinv, Hnode, Hbt, %HΦ⟩
  icombine Htl Htl' gives %Htleq
  subst Htleq
  obtain ⟨hvC, hperm, hout, hC⟩ := Hpf
  iunfold TraceFire
  iexists tn
  iframe Hdir Hlg
  isplitr; · ipureintro; exact Hnn
  iintro %e %HE
  iauintro
  unfold atomic_acc
  iinv Hinv with >Hi Hclose
  iunfold simInv at Hi
  icases Hi with ⟨%L, %σ, %A, %B, %phP, %phM, %Bt, HL, HA, HB, HBt, #Hfσ, %Hp⟩
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
    imod Hclose $$ [HL HA HB HBt] with -
    · inext; iunfold simInv; iexists L, σ, A, B, phP, phM, Bt; iunfold traceFrag; iframe HL HA HB HBt Hfσ; ipureintro; exact Hp
    imodintro
    iframe Hnode Hbt
  · iintro HL
    imod Hmask with -
    obtain ⟨hrun, hsrv, hA, hAn, hPb, hMb, hpv, hcq, hsrcA, hbtC⟩ := Hp
    icases Hbt with ⟨%o0, Hbt, -⟩
    iunfold simBoot at Hbt
    icases ghost_map_lookup $$ HBt Hbt with %HBtid
    obtain ⟨b0, o1, hb0, hiff, -, -⟩ := hbtC id hC
    rw [HBtid] at hb0; cases hb0
    have hnb : ¬ booted L (idAbs id) := fun h => by have := hiff.2 h; cases this
    obtain ⟨hnid, ln, hpl, hnl, hbl⟩ := hE e HE
    imod ghost_map_update (false, some e) $$ HBt Hbt with ⟨HBt, Hbt⟩
    icases keep_pure (simFx_violated γ C σ hsrv) $$ [$Htbl $Hfσ] with ⟨⟨Htbl, -⟩, %hv⟩
    have hrun' := simRun_boot C L σ hrun hv e ln hpl (fun lines hl =>
      bootFlags_unbooted C L lines ln (idAbs id) (by rw [mem_confAbs]; exact hC) hl hnb hnl hbl)
    have hbt' : ∀ i ∈ C, ∃ b o, (Bt.insert id (false, some e)) !! i = some (b, o) ∧
        (b = true ↔ booted (L ++ [e]) (idAbs i)) ∧ LastOf (L ++ [e]) (decStr i) o ∧ (b = true → o.isSome) := by
      intro i hi
      by_cases hii : i = id
      · subst hii
        exact ⟨false, some e, GMap.lookup_insert _ _ _,
          by rw [booted_snoc_boot L e ln _ hpl hbl]; simp; exact hnb,
          lastOf_snoc_self L e _ hnid, fun h => by cases h⟩
      · obtain ⟨b, o, hb, hiff', hlo, hso⟩ := hbtC i hi
        exact ⟨b, o, by rw [GMap.lookup_insert_ne _ _ (Ne.symm hii)]; exact hb,
          by rw [booted_snoc_boot L e ln _ hpl hbl]; exact hiff',
          lastOf_snoc_other L e _ o (by rw [hnid]; exact fun h => hii (decStr_inj h).symm) hlo, hso⟩
    imod Hrclose $$ [Hc Hj Htbl Hw Hrest] with -
    · inext; iunfold raftLogInvBody; iexists lc; iframe
    imod Hclose $$ [HL HA HB HBt] with -
    · inext; iunfold simInv
      iexists L ++ [e], σ, A, B, phP, phM, Bt.insert id (false, some e)
      iunfold traceFrag; iframe HL HA HB HBt Hfσ
      ipureintro
      exact ⟨hrun', hsrv, hA, hAn, hPb, hMb, hpv, hcq, hsrcA, hbt'⟩
    imodintro
    iunfold trCapB
    iexists tn, C, tl, cs, P
    iframe Hdir Htl Hlg Hinv Hnode
    isplitr; · ipureintro; exact ⟨hvC, hperm, hout, hC⟩
    isplitr; · ipureintro; exact Hnn
    isplitr; · iunfold raftLogInv; iexact Hrinv
    isplitl [Hbt]; · iexists some e; iunfold simBoot; iframe Hbt; ipureintro; exact hΛ e HE
    ipureintro; exact HΦ


/-- A booted node stays booted. -/
theorem booted_snoc_mono (L : List TraceEv) (e : TraceEv) (j : Etcdraft.ID) (h : booted L j) :
    booted (L ++ [e]) j := by
  obtain ⟨x, hx, rest⟩ := h
  exact ⟨x, List.mem_append_left _ hx, rest⟩

/-- **The law of a `BecomeFollower` line after the node's segment** (`trCap_fire_bf.statement`). -/
theorem trCap_fire_bf : trCap_fire_bf.statement (GF := GF) := by
  intro γd γ r id c tl s Φ Φ' Λ Λ' hps hΛ
  iintro ⟨Hcap, #Htl, Hfx⟩
  iunfold FxPresBF at Hfx
  icases Hfx with #Hfx
  iunfold trCapB at Hcap
  icases Hcap with ⟨%tn, %C, %tl', %cs, %P, #Hdir, %Hpf, #Htl', #Hlg, %Hnn, #Hinv, #Hrinv, Hnode, Hbt, %HΦ⟩
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
  icases Hi with ⟨%L, %σ, %A, %B, %phP, %phM, %Bt, HL, HA, HB, HBt, #Hfσ, %Hp⟩
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
    imod Hclose $$ [HL HA HB HBt] with -
    · inext; iunfold simInv; iexists L, σ, A, B, phP, phM, Bt; iunfold traceFrag; iframe HL HA HB HBt Hfσ; ipureintro; exact Hp
    imodintro
    iframe Hnode Hbt
  · iintro HL
    imod Hmask with -
    iunfold simNode at Hnode
    icases ghost_map_lookup $$ HA Hnode with %HAid
    obtain ⟨hrun, hsrv, hA, hAn, hPb, hMb, hpv, hcq, hsrcA, hbtC⟩ := Hp
    obtain ⟨Q, hQ⟩ := hA id hC
    rw [HAid] at hQ
    simp only [Option.some.injEq, Prod.mk.injEq] at hQ
    obtain ⟨hcs, hQP⟩ := hQ
    icases Hbt with ⟨%o0, Hbt, %HΛo⟩
    iunfold simBoot at Hbt
    icases ghost_map_lookup $$ HBt Hbt with %HBtid
    obtain ⟨b0, o1, hb0, hiff, hlast, hsome⟩ := hbtC id hC
    rw [HBtid] at hb0
    simp only [Option.some.injEq, Prod.mk.injEq] at hb0
    obtain ⟨hb0, ho1⟩ := hb0
    subst hb0; subst ho1
    have hbooted : booted L (idAbs id) := hiff.1 rfl
    obtain ⟨e0, he0⟩ := Option.isSome_iff_exists.1 (hsome rfl)
    subst he0
    obtain ⟨L1, L2, hsplit, hn0, hL2⟩ := hlast
    have hev := HE
    obtain ⟨hname1, hnid1, -, hvote1, -, -, -, ⟨xs1, ys1, -, hys1, hconf1⟩, hmsg1, -, -, -, -⟩ := hev
    rw [hout, elements_empty_nil] at hys1
    have hys10 := List.Perm.eq_nil hys1
    subst hys10
    have hname1' : gsStr e.name = "BecomeFollower" := by
      simp only [evtNames] at hname1
      have : e.name = go!"BecomeFollower" := by have := hname1; simp at this; exact this.symm
      rw [this]; rfl
    have hpl := parseLine_node 0 e id s.vote xs1 [] hnid1 hvote1 hconf1 hmsg1 (by rw [hname1']; rfl)
      (by rw [hname1']; decide)
    obtain ⟨hskipC, hdownC⟩ := hps C cs P (some e0) HΦ HΛo ⟨hperm, hout, hC⟩ e e0 HE rfl
    have hnid0' : (evConv e0).nid = (evConv e).nid := by simp only [evConv, hn0, hnid1]
    have hnid2' : ∀ x ∈ L2, (evConv x).nid ≠ (evConv e).nid := by
      intro x hx h; simp only [evConv] at h; exact hL2 x hx (by rw [gsStr_inj h, hnid1])
    have hL : L ≠ [] := by rw [hsplit]; simp
    have hboot : ∀ lines (ln : Etcdraft.Line), parseLines (L.map evConv) = .ok lines → ln.nid = idAbs id →
        (bootFlags (confAbs C) (lines ++ [ln])).getD L.length false = false :=
      fun lines ln hl hn => bootFlags_booted C L lines ln (idAbs id) hl hbooted hn
    have hBt' := bootClause_step C L e _ id Bt hpl rfl hnid1 (booted_snoc_mono L e _ hbooted) hbtC
    icases keep_pure (simFx_violated γ C σ hsrv) $$ [$Htbl $Hfσ] with ⟨⟨Htbl, -⟩, %hv⟩
    imod ghost_map_update (true, some e) $$ HBt Hbt with ⟨HBt, Hbt⟩
    by_cases hcond : bfCond (evConv e0) (evConv e) = true
    · have hrun' := simRun_bfSkip C L σ hrun hL e id s c HE hout L1 L2 e0 hsplit hnid0' hnid2' hcond hboot hv
      imod Hrclose $$ [Hc Hj Htbl Hw Hrest] with -
      · inext; iunfold raftLogInvBody; iexists lc; iframe
      imod Hclose $$ [HL HA HB HBt] with -
      · inext; iunfold simInv
        iexists L ++ [e], σ, A, B, phP, phM, Bt.insert id (true, some e)
        iunfold traceFrag; iframe HL HA HB HBt Hfσ
        ipureintro
        exact ⟨hrun', hsrv, hA, hAn, hPb, hMb, hpv, hcq, hsrcA, hBt'⟩
      imodintro
      iunfold trCapB
      iexists tn, C, tl, cs, P
      iunfold simNode
      iframe Hdir Htl Hlg Hinv Hnode
      isplitr; · ipureintro; exact ⟨hvC, hperm, hout, hC⟩
      isplitr; · ipureintro; exact Hnn
      isplitr; · iunfold raftLogInv; iexact Hrinv
      isplitl [Hbt]; · iexists some e; iunfold simBoot; iframe Hbt; ipureintro; exact hΛ e HE
      ipureintro; exact hskipC hcond
    · have hcond' : bfCond (evConv e0) (evConv e) = false := by simpa using hcond
      obtain ⟨hst, hR, hs, hpre, bt, bc, bl, hΦ'⟩ := hdownC hcond' (σ.s (idAbs id)) (by rw [← hsrv]; exact hcs.symm)
      have heq : σ.becomeFollowerOfTerm (idAbs id) (σ.s (idAbs id)).currentTerm =
          withNode σ (idAbs id) (bfSrv (σ.s (idAbs id))) _root_.id _root_.id := rfl
      have hΦσ : Φ C (toC (confAbs C) (σ.s (idAbs id))) P := by rw [← hsrv, ← hcs]; exact HΦ
      have hpreF := And.intro hΦσ (And.intro hsrv (And.intro hpv (And.intro hcq (And.intro hv hst))))
      icases Hfx $$ %C %P %σ %hpreF Htbl Hfσ with ⟨Htbl, #Hfσ'⟩
      have hsrv' : (withNode σ (idAbs id) (bfSrv (σ.s (idAbs id))) _root_.id _root_.id).server = confAbs C := hsrv
      icases keep_pure (simFx_violated γ C _ hsrv') $$ [$Htbl $Hfσ'] with ⟨⟨Htbl, -⟩, %hv'⟩
      have hrun' := simRun_bfStepDown C L σ hrun hL e id s c HE hperm hout hC hsrv L1 L2 e0 hsplit hnid0' hnid2'
        hcond' hst (by rw [heq]; simpa [withNode] using hR) hs hpre bt bc bl hboot (by rw [heq]; exact hv')
      rw [heq] at hrun'
      have hAid : A !! id = some (toC σ.server (σ.s (idAbs id)), P) := by rw [HAid, hcs]
      obtain ⟨hsrvN, hA', hAn', hsrc', hPb', hM'⟩ :=
        shareStep_pure C σ A phP id hC hnd P (bfSrv (σ.s (idAbs id))) [] hsrv hA hAid hAn hsrcA (by simp) hPb
      imod ghost_map_update (toC σ.server (bfSrv (σ.s (idAbs id))), P ++ []) $$ HA Hnode with ⟨HA, Hnode⟩
      imod Hrclose $$ [Hc Hj Htbl Hw Hrest] with -
      · inext; iunfold raftLogInvBody; iexists lc; iframe
      imod Hclose $$ [HL HA HB HBt] with -
      · inext; iunfold simInv
        iexists L ++ [e], withNode σ (idAbs id) (bfSrv (σ.s (idAbs id))) _root_.id _root_.id,
          A.insert id (toC σ.server (bfSrv (σ.s (idAbs id))), P ++ []), B, phP, phM, Bt.insert id (true, some e)
        iunfold traceFrag; iframe HL HA HB HBt Hfσ'
        ipureintro
        exact ⟨hrun', hsrvN, hA', hAn', hPb', hMb, hpv, hcq, hsrc', hBt'⟩
      imodintro
      iunfold trCapB
      iexists tn, C, tl, toC σ.server (bfSrv (σ.s (idAbs id))), P ++ []
      iunfold simNode
      iframe Hdir Htl Hlg Hinv Hnode
      isplitr; · ipureintro; exact ⟨hvC, hperm, hout, hC⟩
      isplitr; · ipureintro; exact Hnn
      isplitr; · iunfold raftLogInv; iexact Hrinv
      isplitl [Hbt]; · iexists some e; iunfold simBoot; iframe Hbt; ipureintro; exact hΛ e HE
      ipureintro; rw [hsrv, List.append_nil]; exact hΦ'

end ghost

end EtcdGrove
end Perennial
