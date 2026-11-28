/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__startStopReplication.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).startStopReplication`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__startStopReplication
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getLastIndex
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getCurrentTerm
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__goFunc
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__replicate
public import Dsverify.Spec.github_com.hashicorp.raft.asyncNotifyCh
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__observe
public import Dsverify.Proof.github_com.hashicorp.raft.core.ObsHelpers
public import Dsverify.Proof.github_com.hashicorp.raft.main.MainCLemmas
public import Dsverify.Proof.github_com.hashicorp.raft.Threads.QPool
public import Dsverify.Proof.github_com.hashicorp.raft.leader.Futures
public import Perennial.Spec.time.Now

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft
open proto gprot

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

theorem ml_fractional_exists_agree {PROP : Type _} [BI PROP] {X : Type _} (Φ : X → Qp → PROP)
    (hfrac : ∀ x, Fractional (Φ x)) (hagree : ∀ x y q1 q2, Φ x q1 ∗ Φ y q2 ⊢ ⌜x = y⌝) :
    Fractional (fun q => iprop(∃ x, Φ x q)) where
  fractional p q := by
    constructor
    · iintro ⟨%x, H⟩
      icases ((hfrac x).fractional p q).1 $$ H with ⟨H1, H2⟩
      isplitl [H1]
      · iexists x; iexact H1
      · iexists x; iexact H2
    · refine (sep_exists_right.1).trans (exists_elim fun x => ?_)
      refine (sep_exists_left.1).trans (exists_elim fun y => ?_)
      refine (and_intro (hagree x y p q) .rfl).trans (pure_elim_left fun h => ?_)
      subst h
      exact ((hfrac x).fractional p q).2.trans (exists_intro (Ψ := fun x => Φ x (p + q)) x)

instance ml_true_fractional : Fractional (fun _ : Qp => (iprop(True) : IProp GF)) where
  fractional p q := by
    constructor
    · iintro -; isplit <;> itrivial
    · iintro -; itrivial

instance ml_lastContact_fractional (s : Loc) :
    Fractional (fun q : Qp => iprop(∃ t : time.Time,
      s.[followerReplication, go!"lastContact"] ↦{DFrac.own q} t) : Qp → IProp GF) := by
  apply ml_fractional_exists_agree (Φ := fun t q =>
    iprop(s.[followerReplication, go!"lastContact"] ↦{DFrac.own q} t))
  · intro t; exact ⟨fun q1 q2 => typedPointsto_frac_add _ t q1 q2⟩
  · intro x y q1 q2
    iintro ⟨H1, H2⟩
    icombine H1 H2 gives %h
    ipureintro; exact h

theorem take_succ_mem {α} (l : List α) (k : Nat) (x j : α) (h : l[k]? = some x) :
    j ∈ l.take (k + 1) ↔ j ∈ l.take k ∨ j = x := by
  rw [List.take_add_one, h]; simp

theorem nodup_not_mem_take {α} (l : List α) (k : Nat) (x : α) (hnd : l.Nodup) (h : l[k]? = some x) :
    x ∉ l.take k := by
  intro hm
  obtain ⟨t, hx⟩ := List.mem_iff_getElem?.mp hm
  have htk : t < k := by
    have := (List.getElem?_eq_some_iff.mp hx).1; simp at this; omega
  rw [List.getElem?_take, if_pos htk] at hx
  have htl : t < l.length := (List.getElem?_eq_some_iff.mp hx).1
  have := (hnd.getElem?_inj (j := k) htl).mp (by rw [hx, h])
  omega

theorem peerObs_ty_ne : PeerObservation.ty ≠ RaftState.ty := by
  unfold PeerObservation.ty RaftState.ty; simp

/-- The latest configuration's servers: their IDs are `cfgIdsOf`, each one of the protocol's
servers and its own address (unfolds `cfgAtIs`/`cfgVal`). -/
theorem ssr_cfg_servers (γ : GNames) (L : RLog) (p : Nat) (c : Configuration)
    (hp : p = lastCfgIdx L) :
    cfgAtIs (GF := GF) γ L p c ⊢
      ∃ ss : List Server, c.Servers' ↦*□ ss ∗ ⌜srvIds ss = cfgIdsOf γ.srvs L ∧
        ∀ sv ∈ ss, sv.Address' = sv.ID' ∧ sv.ID' ∈ γ.srvs⌝ := by
  subst hp
  iintro #H
  ihave ⟨%ss, #Hs, %hids⟩ := cfgAtIs_ids γ L c $$ H
  unfold cfgAtIs cfgVal
  icases H with (⟨%hp, #Hs0⟩ | ⟨%ss', %e, ⟨#Hs', %hok⟩, %h⟩)
  · ihave %heq := ownSlice_agree _ _ _ _ _ $$ Hs Hs0
    subst heq
    iexists []; iframe #; ipureintro
    exact ⟨hids, fun sv hsv => by simp at hsv⟩
  · ihave %heq := ownSlice_agree _ _ _ _ _ $$ Hs Hs'
    subst heq
    iexists ss; iframe #; ipureintro
    obtain ⟨-, hin, hsv, -⟩ := hok
    refine ⟨hids, fun sv hm => ⟨(hsv sv hm).2.1, hin _ ?_⟩⟩
    exact List.mem_map.mpr ⟨sv, hm, rfl⟩

end defs
end github_com.hashicorp.raft

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]
variable [htb : ThreadBoundLe GF (2 ^ 28)]

open github_com.hashicorp.raft proto gprot

set_option maxHeartbeats 4000000 in
theorem github_com.hashicorp.raft.Raft.startStopReplication.wp_proof
    (wp_getLastIndex : github_com.hashicorp.raft.raftState.getLastIndex.spec (GF := GF) (hG := hG))
    (wp_getCurrentTerm : github_com.hashicorp.raft.raftState.getCurrentTerm.spec (GF := GF) (hG := hG))
    (wp_goFunc : github_com.hashicorp.raft.raftState.goFunc.spec (GF := GF) (hG := hG))
    (wp_replicate : github_com.hashicorp.raft.Raft.replicate.spec (GF := GF) (hG := hG))
    (wp_asyncNotifyCh : github_com.hashicorp.raft.asyncNotifyCh.spec (GF := GF) (hG := hG))
    (wp_observe : github_com.hashicorp.raft.Raft.observe.spec (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.startStopReplication.spec (GF := GF) (hG := hG) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

end proof

end Perennial
