/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/client/MainDeployment.lean`. Lean-first; N7-kv.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.MainDeployment
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.MainReady
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.WellFormed
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.Deployment__Endpoints

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

theorem MainDeployment.wp_proof (OP : List GoString → w64 → IProp GF)
    (hWF : WellFormed.spec (GF := GF) (hG := hG))
    (hEp : Deployment.Endpoints.spec (GF := GF) (hG := hG))
    (hMR : MainReady.spec (GF := GF) (hG := hG) OP) :
    MainDeployment.spec (GF := GF) (hG := hG) OP := by
  intro v d j ready
  wp_start as ⟨%Hp, #Hd, #Hready, Hsh⟩
  obtain ⟨Hkv, Hfips⟩ := Hp
  wp_auto
  wp_apply (hWF v d Hfips) as %err %Herr
  · iframe #
  cases err with
  | ok i =>
    wp_auto
    wp_func_call; wp_call; wp_auto
    iapply HΦ; ipureintro; trivial
  | nil =>
    have hwf := Herr rfl
    have hnl := wellFormed_nodes_length hwf
    wp_auto
    ihave #Hd2 := Hd
    iunfold deploymentRepr at Hd2
    icases Hd2 with ⟨#Hm, %htok, %hcfg, #Hw, %ss, #Hn, #Hns⟩
    ihave %Hwl := ownSlice_len _ _ _ $$ Hw
    ihave %Hnl := ownSlice_len _ _ _ $$ Hn
    ihave %Hssl := BigSepL2.bigSepL2_length $$ Hns
    rw [List.length_map] at Hwl
    wp_if_destruct
    · wp_func_call; wp_call; wp_auto
      iapply HΦ; ipureintro; trivial
    wp_if_destruct
    · wp_func_call; wp_call; wp_auto
      iapply HΦ; ipureintro; trivial
    have hjw : sint.nat j < d.workloads.length := by word
    have hjn : sint.nat j < d.nodes.length := by omega
    have h0 : 0 ≤ sint.Z j := by word
    obtain ⟨w, hw⟩ : ∃ w, d.workloads[sint.nat j]? = some w := ⟨_, List.getElem?_eq_getElem hjw⟩
    obtain ⟨ns, hns⟩ : ∃ ns, d.nodes[sint.nat j]? = some ns := ⟨_, List.getElem?_eq_getElem hjn⟩
    obtain ⟨s, hs⟩ : ∃ s, ss[sint.nat j]? = some s := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    ihave #Hs := BigSepL2.bigSepL2_lookup hs hns $$ Hns
    have hjl : sint.Z j < sint.Z v.Workloads'.len := by word
    simp only [h0, hjl, and_self, ↓reduceIte]
    wp_apply (wp_load_slice_index v.Workloads' (sint.Z j) (d.workloads.map Workload.val) DFrac.discard w.val h0) $$ [] as -
    · iframe #; ipureintro; rw [List.getElem?_map, hw]; rfl
    wp_method_call
    wp_call
    wp_auto
    wp_apply (hEp v d) as %eps Heps
    · iframe #
    have hjn' : sint.Z j < sint.Z v.Nodes'.len := by word
    simp only [h0, hjn', and_self, ↓reduceIte]
    wp_apply (wp_load_slice_index v.Nodes' (sint.Z j) ss DFrac.discard s h0) $$ [] as -
    · iframe #; ipureintro; exact hs
    have hk : w.kind = W64 0 := Hkv w (List.mem_of_getElem? hw)
    have hsh : orchShare OP d j = OP ns w.ops := by
      unfold orchShare; rw [if_pos h0, hw, hns]
    rw [hsh]
    wp_apply (hMR w eps s ns ready) $$ [Hsh] as %r -
    · iframe #
      iframe
      ipureintro; exact hk
    iapply HΦ; ipureintro; trivial

end proof

end etcd_dist
end EtcdGrove
end Perennial
