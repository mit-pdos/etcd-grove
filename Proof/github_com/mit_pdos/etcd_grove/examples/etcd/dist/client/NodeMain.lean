/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/client/NodeMain.lean`. Lean-first.
- `NodeMain.wp_proofKv` (N7-kv, M1): the kv arm, at `Node.specWith NP`.
- `NodeMain.wp_proof` (F8): by the workload's kind, the triples of `NodeMain` itself that cover it: kv is
  `NodeMain.specKv` at `kvNodePreL` (the level token, the thread bound and `kvNodePre`); watch and cache are
  `NodeMainWatch.spec` (its share `nodeWatchPre` from `writerNodePre`, `nodeWatchPre_of`); auth is reached with a
  `False` share (D2); every other kind has no client machine (`NodeCount` is `0`: it returns).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.NodeMain
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.NodeMainWatch
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Rotate
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.NodeWith
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.NodeCount

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : client.Assumptions]

theorem NodeMain.wp_proofKv (NP : w64 → GoString → List GoString → IProp GF)
    (hNC : NodeCount.spec (GF := GF) (hG := hG))
    (hRot : Rotate.spec (GF := GF) (hG := hG))
    (hNode : Node.specWith (GF := GF) (hG := hG) NP) :
    NodeMain.specKv (GF := GF) (hG := hG) NP := by
  intro w c addr eps epsL
  wp_start as ⟨%Hp, #Heps, HNP⟩
  obtain ⟨Hk, Hb⟩ := Hp
  have hnc : w.goNodeCount = w.clients := by simp [Workload.goNodeCount, Hk]
  ihave %Hel := ownSlice_len _ _ _ $$ Heps
  wp_auto
  wp_if_destruct
  · iapply HΦ; ipureintro; trivial
  wp_apply hNC
  rw [hnc]
  wp_if_destruct
  · iapply HΦ; ipureintro; trivial
  wp_if_destruct
  · iapply HΦ; ipureintro; trivial
  simp only [Workload.val, Hk]
  wp_auto
  wp_apply (hRot (V := GoString) (T := go.string) eps DFrac.discard epsL c) as %out ⟨-, Hout⟩
  · iframe #
    ipureintro
    intro _
    have h0 : 0 ≤ sint.Z c := by word
    have h1 : sint.Z c < sint.Z w.clients := by word
    exact ⟨h0, Hb h0 h1⟩
  wp_apply (hNode c addr out _) $$ [Hout HNP]
  · iframe
  iapply HΦ; ipureintro; trivial

end proof

section proofFull
open Net client etcd_dist_client etcd_dist.view
open github_com.mit_pdos.etcd_grove.examples.lib.remote
open github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : client.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

theorem NodeMain.wp_proof
    (hNC : NodeCount.spec (GF := GF) (hG := hG))
    (hKv : ∀ [π : NetProtoGS] [ρ : RemoteGS],
      NodeMain.specKv (GF := GF) (hG := hG) (kvNodePreL (GF := GF) (ρ := ρ)))
    (hW : NodeMainWatch.spec (GF := GF) (hG := hG)) :
    NodeMain.spec (GF := GF) (hG := hG) := by
  intro π ρ w c addr eps epsL
  by_cases hk0 : w.kind = W64 0
  · -- kv: M1's arm
    rw [wlNodeShare_kv hk0]
    have hgn : w.goNodeCount = w.clients := by simp [Workload.goNodeCount, hk0]
    wp_start_folded as ⟨%Hp, Hlt, #Heps, Hsh⟩
    obtain ⟨hpure, hlen, hpl, hV, htb, hAs⟩ := Hp
    have hb := hpure.2.1
    rw [hgn] at hb
    wp_apply (hKv w c addr eps epsL) $$ [Hlt Hsh]
    · iframe #
      isplitr [Hlt Hsh]
      · ipureintro; exact ⟨hk0, fun _ _ => by omega⟩
      iunfold kvNodePreL
      iframe Hlt
      isplitr [Hsh]
      · ipureintro; exact htb
      iexact Hsh
    iapply HΦ; ipureintro; trivial
  by_cases hk12 : w.kind = W64 1 ∨ w.kind = W64 2
  · -- watch, cache: the writer
    rw [wlNodeShare_writer hk12]
    have hgn : w.goNodeCount = w.clients := by
      rcases hk12 with h | h <;> simp [Workload.goNodeCount, h]
    wp_start_folded as ⟨%Hp, Hlt, #Heps, Hsh⟩
    obtain ⟨hpure, hlen, hpl, hV, htb, hAs⟩ := Hp
    have hb := hpure.2.1
    rw [hgn] at hb
    wp_apply (hW w c addr eps epsL) $$ [Hlt Hsh]
    · iframe #
      isplitr [Hlt Hsh]
      · ipureintro; exact ⟨hk12, fun _ _ => by omega⟩
      iintro %_
      iapply (nodeWatchPre_of addr _ hV htb (plainEndpoints_rotateL hpl _) hAs)
      iframe
    iapply HΦ; ipureintro; trivial
  by_cases hk5 : w.kind = W64 5
  · -- auth: no share (D2)
    rw [wlNodeShare_auth hk5]
    wp_start_folded as ⟨%Hp, Hlt, #Heps, Hsh⟩
    iexfalso; iexact Hsh
  -- no client machine: `NodeCount` is `0`, `NodeMain` returns
  have hgn : w.goNodeCount = W64 0 := by
    unfold Workload.goNodeCount
    rw [if_neg (fun h => by
      rcases h with h | h | h
      · exact hk0 h
      · exact hk12 (Or.inl h)
      · exact hk12 (Or.inr h)), if_neg hk5]
  wp_start as ⟨%Hp, Hlt, #Heps, Hsh⟩
  wp_auto
  wp_if_destruct
  · iapply HΦ; ipureintro; trivial
  wp_apply hNC
  rw [hgn]
  wp_if_destruct
  · iapply HΦ; ipureintro; trivial
  exfalso
  word

end proofFull

end etcd_dist
end EtcdGrove
end Perennial
