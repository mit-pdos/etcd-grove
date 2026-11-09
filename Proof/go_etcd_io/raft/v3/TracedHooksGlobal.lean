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
      BagRep σ'.pendingMessages ((C.flatMap (fun i => ((A' !! i).map Prod.snd).getD [])) ++ phP) ∧
      σ'.messages = σ.messages := by
  intro σ' A'
  have hsrv' : σ'.server = σ.server := rfl
  have hs_id : σ'.s (idAbs id) = a' := by simp [σ', withNode]
  have hs_ne : ∀ j, j ≠ idAbs id → σ'.s j = σ.s j := by intro j hj; simp [σ', withNode, hj]
  refine ⟨?_, by rw [hsrv', hsrv], ?_, ?_, ?_, rfl⟩
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
    (hnd : C.Nodup) (P : List Etcdraft.Msg) (e : TraceEv) (a' : Etcdraft.Server) (P' : List Etcdraft.Msg)
    (k : Nat) (m : Etcdraft.Msg) (Mid : Etcdraft.Server → Prop)
    (hrun : SimRun C L σ) (hsrv : σ.server = confAbs C)
    (hA : ∀ i ∈ C, ∃ Q, A !! i = some (toC σ.server (σ.s (idAbs i)), Q)) (hAid : A !! id = some (toC σ.server (σ.s (idAbs id)), P))
    (hAn : ∀ i, i ∉ C → A !! i = none)
    (hP : BagRep σ.pendingMessages ((C.flatMap (fun i => ((A !! i).map Prod.snd).getD [])) ++ phP))
    (hM : BagRep σ.messages ((GMap.toList B).map Prod.snd ++ phM)) (hBk : B !! k = some m)
    (huniq : MsgsUniq σ)
    (hpv : σ.preVote = false) (hcq : σ.checkQuorum = false)
    (hname : Etcdraft.isBootstrapName (gsStr e.name) = false)
    (hmatch : ∀ ln, Etcdraft.parseLine 0 (evConv e) = .ok ln → recvPred ln m = true)
    (hle : LineEffect C false e (idAbs id) (σ.s (idAbs id)) a' (some m) (fun b => b.without m)
      (fun b => P'.foldl Etcdraft.Bag.with b) Mid)
    (hσinv : σ.violated = .ok none)
    (hmids : ∀ v, Mid v → (withNode σ (idAbs id) v _root_.id _root_.id).violated = .ok none)
    (hinv : (withNode σ (idAbs id) a' (fun b => b.without m) (fun b => P'.foldl Etcdraft.Bag.with b)).violated = .ok none) :
    let σ' := withNode σ (idAbs id) a' (fun b => b.without m) (fun b => P'.foldl Etcdraft.Bag.with b)
    let A' := A.insert id (toC σ.server a', P ++ P')
    SimRun C (L ++ [e]) σ' ∧ σ'.server = confAbs C ∧
      (∀ i ∈ C, ∃ Q, A' !! i = some (toC σ'.server (σ'.s (idAbs i)), Q)) ∧ (∀ i, i ∉ C → A' !! i = none) ∧
      BagRep σ'.pendingMessages ((C.flatMap (fun i => ((A' !! i).map Prod.snd).getD [])) ++ phP) ∧
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
  refine ⟨?_, by rw [hsrv', hsrv], ?_, ?_, ?_, ?_⟩
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
      · exact absurd (huniq ln m' m hm' hmd h (hmatch ln hp)) hne
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
  · have hfold := bagRep_foldl_with P' _ _ hP
    apply bagRep_perm _ _ _ hfold
    have := flatMap_update_perm C (fun i => ((A !! i).map Prod.snd).getD []) (fun i => ((A' !! i).map Prod.snd).getD [])
      id hnd hC P' (by simp [A', hAid]) (fun j hj => by
        rw [show A' !! j = A !! j from GMap.lookup_insert_ne _ _ (Ne.symm hj)])
    simp only [List.append_assoc]
    refine (List.Perm.append_left _ List.perm_append_comm).trans ?_
    rw [← List.append_assoc]
    exact List.Perm.append_right phP this.symm
  · have hw := bagRep_without _ _ m hM hml
    apply bagRep_perm _ _ _ hw
    have hp : ((GMap.toList B).map Prod.snd ++ phM).Perm (m :: ((GMap.toList (B.delete k)).map Prod.snd ++ phM)) := by
      have := (GMap.mapToList_delete B k m hBk).map Prod.snd
      simpa using this.append_right phM
    have := hp.erase m
    simpa using this

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
    obtain ⟨hrun, hsrv, hA, hAn, hPb, hMb, hpv, hcq⟩ := Hp
    obtain ⟨Q, hQ⟩ := hA id hC
    rw [HAid] at hQ
    simp only [Option.some.injEq, Prod.mk.injEq] at hQ
    obtain ⟨hcs, hQP⟩ := hQ
    obtain ⟨hname, hall⟩ := hps C cs P HΦ e HE
    obtain ⟨a', P', hΦ', hle⟩ := hall (σ.s (idAbs id)) (by rw [hcs, hsrv])
    have hpre : Φ C cs P ∧ E e ∧ toC (confAbs C) (σ.s (idAbs id)) = cs ∧ Φ' C (toC (confAbs C) a') (P ++ P') ∧
        LineEffect C false e (idAbs id) (σ.s (idAbs id)) a' none _root_.id
          (fun b => List.foldl Etcdraft.Bag.with b P') (fun _ => False) ∧
        σ.server = confAbs C ∧ σ.s (idAbs id) = σ.s (idAbs id) :=
      ⟨HΦ, HE, by rw [hcs, hsrv], hΦ', hle, hsrv, rfl⟩
    ihave #Hfσ' := Hfx $$ %C %cs %P %e %(σ.s (idAbs id)) %a' %P' %σ %hpre Hfσ
    icases keep_pure (simFx_violated γ C σ hsrv) $$ [$Htbl $Hfσ] with ⟨⟨Htbl, -⟩, %hv⟩
    have hsrv' : (withNode σ (idAbs id) a' _root_.id (fun b => List.foldl Etcdraft.Bag.with b P')).server =
        confAbs C := hsrv
    icases keep_pure (simFx_violated γ C _ hsrv') $$ [$Htbl $Hfσ'] with ⟨⟨Htbl, -⟩, %hv'⟩
    have hAid : A !! id = some (toC σ.server (σ.s (idAbs id)), P) := by rw [HAid, hcs]
    obtain ⟨hrun', hsrvN, hA', hAn', hPb', hM'⟩ :=
      simStep_pure C L σ A phP id hC hnd P e a' P' hrun hsrv hA hAid hAn hPb hpv hcq hname
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
      exact ⟨hrun', hsrvN, hA', hAn', hPb', by rw [hM']; exact hMb, hpv, hcq⟩
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
    obtain ⟨hrun, hsrv, hA, hAn, hPb, hMb, hpv, hcq⟩ := Hp
    obtain ⟨Q, hQ⟩ := hA id hC
    rw [HAid] at hQ
    simp only [Option.some.injEq, Prod.mk.injEq] at hQ
    obtain ⟨hcs, hQP⟩ := hQ
    obtain ⟨hname, hmatch, hall⟩ := hps C cs P HΦ e HE
    obtain ⟨a', P', hΦ', hle⟩ := hall (σ.s (idAbs id)) (by rw [hcs, hsrv])
    have hpre : Φ C cs P ∧ E e ∧ toC (confAbs C) (σ.s (idAbs id)) = cs ∧ Φ' C (toC (confAbs C) a') (P ++ P') ∧
        LineEffect C false e (idAbs id) (σ.s (idAbs id)) a' (some m) (fun b => b.without m)
          (fun b => List.foldl Etcdraft.Bag.with b P') Mid ∧
        σ.server = confAbs C ∧ σ.s (idAbs id) = σ.s (idAbs id) :=
      ⟨HΦ, HE, by rw [hcs, hsrv], hΦ', hle, hsrv, rfl⟩
    ihave ⟨#Hfσ', #Hmid⟩ := Hfx $$ %C %cs %P %e %(σ.s (idAbs id)) %a' %P' %σ %hpre Hfσ
    iunfold inFlight at Htok
    icases ghost_map_lookup $$ HB Htok with %HBk
    ihave #Hfσc := Hfσ
    iunfold simFx at Hfσc
    icases Hfσc with ⟨-, %hfx⟩
    have huq : MsgsUniq σ := hfx.2.2.2.2
    icases keep_pure (simFx_violated γ C σ hsrv) $$ [$Htbl $Hfσ] with ⟨⟨Htbl, -⟩, %hv⟩
    have hsrv' : (withNode σ (idAbs id) a' (fun b => b.without m) (fun b => List.foldl Etcdraft.Bag.with b P')).server =
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
    obtain ⟨hrun', hsrvN, hA', hAn', hPb', hM'⟩ :=
      simStepR_pure C L σ A B phP phM id hC hnd P e a' P' k m Mid hrun hsrv hA hAid hAn hPb hMb HBk huq hpv hcq
        hname hmatch hle hv hmids hv'
    imod ghost_map_update (toC σ.server a', P ++ P') $$ HA Hnode with ⟨HA, Hnode⟩
    imod ghost_map_delete $$ HB Htok with HB
    imod Hrclose $$ [Hc Hj Htbl Hw Hrest] with -
    · inext; iunfold raftLogInvBody; iexists lc; iframe
    imod Hclose $$ [HL HA HB] with -
    · inext; iunfold simInv
      iexists L ++ [e], withNode σ (idAbs id) a' (fun b => b.without m) (fun b => List.foldl Etcdraft.Bag.with b P'),
        A.insert id (toC σ.server a', P ++ P'), B.delete k, phP, phM
      iunfold traceFrag; iframe HL HA HB Hfσ'
      ipureintro
      exact ⟨hrun', hsrvN, hA', hAn', hPb', hM', hpv, hcq⟩
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
