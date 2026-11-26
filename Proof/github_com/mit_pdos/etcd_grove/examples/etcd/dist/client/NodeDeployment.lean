/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/client/NodeDeployment.lean`. Lean-first.
`NodeDeployment.wp_proofKv` (N7-kv, M1) and `NodeDeployment.wp_proof` (F8): the deployment check, then `NodeMain`
of the `n`-th client machine at its share (`nodeShareF_eq`), with the pure facts `WellFormed` gives
(`wellFormed_wlPure`, at most 64 members, `rotateL_plain`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.NodeDeployment
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.NodeMain
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.WellFormed
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.Deployment__Endpoints
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.Deployment__Node

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

theorem NodeDeployment.wp_proofKv (NP : w64 → GoString → List GoString → IProp GF)
    (hWF : WellFormed.spec (GF := GF) (hG := hG))
    (hEp : Deployment.Endpoints.spec (GF := GF) (hG := hG))
    (hNd : Deployment.Node.spec (GF := GF) (hG := hG))
    (hNM : NodeMain.specKv (GF := GF) (hG := hG) NP) :
    NodeDeployment.specKv (GF := GF) (hG := hG) NP := by
  intro v d n
  wp_start as ⟨%Hp, #Hd, Hsh⟩
  obtain ⟨Hkv, Hfips⟩ := Hp
  wp_auto
  wp_apply (hWF v d Hfips) as %err %Herr
  · iframe #
  cases err with
  | ok i =>
    wp_auto
    iapply HΦ; ipureintro; trivial
  | nil =>
    have hwf := Herr rfl
    have hkv := Hkv hwf
    have hnl := wellFormed_nodes_length hwf
    obtain ⟨hml, hclients⟩ := kvOnly_bounds hwf hkv
    ispecialize Hsh $$ %hwf
    wp_auto
    ihave #Hw := deploymentRepr_workloads v d $$ Hd
    ihave #Hn' := deploymentRepr_nodes v d $$ Hd
    icases Hn' with ⟨%ss, #Hn, #Hns⟩
    ihave %Hwl := ownSlice_len _ _ _ $$ Hw
    ihave %Hnl := ownSlice_len _ _ _ $$ Hn
    ihave %Hssl := BigSepL2.bigSepL2_length $$ Hns
    rw [List.length_map] at Hwl
    wp_method_call
    wp_call
    wp_auto
    wp_apply (hNd v d n) as %j %c %ok %Hok
    · iframe #
    cases ok with
    | false =>
      wp_auto
      iapply HΦ; ipureintro; trivial
    | true =>
      obtain ⟨hn0, hj0, hc0, w, ns, a, hw, hns, ha, hnl'⟩ := Hok rfl
      wp_auto
      have hjw : sint.nat j < d.workloads.length := (List.getElem?_eq_some_iff.1 hw).1
      have hjn : sint.nat j < d.nodes.length := (List.getElem?_eq_some_iff.1 hns).1
      have hcn : sint.nat c < ns.length := (List.getElem?_eq_some_iff.1 ha).1
      obtain ⟨s, hs⟩ : ∃ s, ss[sint.nat j]? = some s := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      ihave #Hs := BigSepL2.bigSepL2_lookup hs hns $$ Hns
      ihave %Hsl := ownSlice_len _ _ _ $$ Hs
      have hjl : sint.Z j < sint.Z v.Workloads'.len := by word
      have hjl' : sint.Z j < sint.Z v.Nodes'.len := by word
      have hcl : sint.Z c < sint.Z s.len := by word
      simp only [hj0, hjl, and_self, ↓reduceIte]
      wp_apply (wp_load_slice_index v.Workloads' (sint.Z j) (d.workloads.map Workload.val) DFrac.discard w.val hj0) $$ [] as -
      · iframe #; ipureintro; rw [List.getElem?_map, hw]; rfl
      simp only [hj0, hjl', and_self, ↓reduceIte]
      wp_apply (wp_load_slice_index v.Nodes' (sint.Z j) ss DFrac.discard s hj0) $$ [] as -
      · iframe #; ipureintro; exact hs
      simp only [hc0, hcl, and_self, ↓reduceIte]
      wp_apply (wp_load_slice_index s (sint.Z c) ns DFrac.discard a hc0) $$ [] as -
      · iframe #; ipureintro; exact ha
      wp_method_call
      wp_call
      wp_auto
      wp_apply (hEp v d) as %eps Heps
      · iframe #
      imod ownSlice_persist _ _ _ $$ Heps with #Heps
      have hk : w.kind = W64 0 := hkv w (List.mem_of_getElem? hw)
      have hwc := hclients w (List.mem_of_getElem? hw)
      have hcc : W64 ((sint.nat c : Nat) : Int) = c := by word
      rw [nodeShare_eq NP d n w (sint.nat c) a hn0 hnl', hcc]
      wp_apply (hNM w c a eps (d.members.map Member.client)) $$ [Hsh]
      · iframe #
        iframe
        ipureintro
        refine ⟨hk, fun _ _ => ?_⟩
        rw [List.length_map]
        omega
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

set_option maxHeartbeats 800000 in
theorem NodeDeployment.wp_proof
    (hWF : WellFormed.spec (GF := GF) (hG := hG))
    (hEp : Deployment.Endpoints.spec (GF := GF) (hG := hG))
    (hNd : Deployment.Node.spec (GF := GF) (hG := hG))
    (hNM : NodeMain.spec (GF := GF) (hG := hG)) :
    NodeDeployment.spec (GF := GF) (hG := hG) := by
  intro π ρ v d n
  wp_start as ⟨%Hp, Hlt, #Hd, Hsh⟩
  obtain ⟨Hfips, Hm⟩ := Hp
  wp_auto
  wp_apply (hWF v d Hfips) as %err %Herr
  · iframe #
  cases err with
  | ok i =>
    wp_auto
    iapply HΦ; ipureintro; trivial
  | nil =>
    have hwf := Herr rfl
    have hnl := wellFormed_nodes_length hwf
    have hml : d.members.length ≤ 64 := by
      have := (Deployment.WellFormed.members hwf).2.2.2.1
      simpa [typed.maxMembers] using this
    ispecialize Hsh $$ %hwf
    wp_auto
    ihave #Hw := deploymentRepr_workloads v d $$ Hd
    ihave #Hn' := deploymentRepr_nodes v d $$ Hd
    icases Hn' with ⟨%ss, #Hn, #Hns⟩
    ihave %Hwl := ownSlice_len _ _ _ $$ Hw
    ihave %Hnl := ownSlice_len _ _ _ $$ Hn
    ihave %Hssl := BigSepL2.bigSepL2_length $$ Hns
    rw [List.length_map] at Hwl
    wp_method_call
    wp_call
    wp_auto
    wp_apply (hNd v d n) as %j %c %ok %Hok
    · iframe #
    cases ok with
    | false =>
      wp_auto
      iapply HΦ; ipureintro; trivial
    | true =>
      obtain ⟨hn0, hj0, hc0, w, ns, a, hw, hns, ha, hnl'⟩ := Hok rfl
      wp_auto
      have hjw : sint.nat j < d.workloads.length := (List.getElem?_eq_some_iff.1 hw).1
      have hjn : sint.nat j < d.nodes.length := (List.getElem?_eq_some_iff.1 hns).1
      have hcn : sint.nat c < ns.length := (List.getElem?_eq_some_iff.1 ha).1
      obtain ⟨s, hs⟩ : ∃ s, ss[sint.nat j]? = some s := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      ihave #Hs := BigSepL2.bigSepL2_lookup hs hns $$ Hns
      ihave %Hsl := ownSlice_len _ _ _ $$ Hs
      have hjl : sint.Z j < sint.Z v.Workloads'.len := by word
      have hjl' : sint.Z j < sint.Z v.Nodes'.len := by word
      have hcl : sint.Z c < sint.Z s.len := by word
      simp only [hj0, hjl, and_self, ↓reduceIte]
      wp_apply (wp_load_slice_index v.Workloads' (sint.Z j) (d.workloads.map Workload.val) DFrac.discard w.val hj0) $$ [] as -
      · iframe #; ipureintro; rw [List.getElem?_map, hw]; rfl
      simp only [hj0, hjl', and_self, ↓reduceIte]
      wp_apply (wp_load_slice_index v.Nodes' (sint.Z j) ss DFrac.discard s hj0) $$ [] as -
      · iframe #; ipureintro; exact hs
      simp only [hc0, hcl, and_self, ↓reduceIte]
      wp_apply (wp_load_slice_index s (sint.Z c) ns DFrac.discard a hc0) $$ [] as -
      · iframe #; ipureintro; exact ha
      wp_method_call
      wp_call
      wp_auto
      wp_apply (hEp v d) as %eps Heps
      · iframe #
      imod ownSlice_persist _ _ _ $$ Heps with #Heps
      have hcc : W64 ((sint.nat c : Nat) : Int) = c := by word
      rw [nodeShareF_eq d n w (sint.nat c) a hn0 hnl', hcc]
      wp_apply (hNM w c a eps (d.members.map Member.client)) $$ [Hlt Hsh]
      · iframe #
        iframe
        ipureintro
        exact ⟨wellFormed_wlPure hwf (List.mem_of_getElem? hw), by rw [List.length_map]; exact hml,
          rotateL_plain hwf _, Hm⟩
      iapply HΦ; ipureintro; trivial

end proofFull

end etcd_dist
end EtcdGrove
end Perennial
