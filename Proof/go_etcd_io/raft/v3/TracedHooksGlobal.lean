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
  sorry

end ghost

end EtcdGrove
end Perennial
