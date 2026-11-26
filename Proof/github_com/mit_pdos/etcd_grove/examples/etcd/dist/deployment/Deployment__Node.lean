/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/deployment/Deployment__Node.lean`.
Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.Deployment__Node

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

/-- `nodeList`'s entries, one workload's client machines after another. -/
def nodeEntries (p : Workload × List GoString) : List (Workload × Nat × GoString) :=
  p.2.zipIdx.map (fun q => (p.1, q.2, q.1))

theorem nodeList_eq (d : Deployment) :
    d.nodeList = (d.workloads.zip d.nodes).flatMap nodeEntries := rfl

theorem nodeEntries_cons_get (w : Workload) (ns : List GoString)
    (rest : List (Workload × List GoString)) (k : Nat) :
    (((w, ns) :: rest).flatMap nodeEntries)[k]? =
      if k < ns.length then (ns[k]?).map (fun a => (w, k, a))
      else (rest.flatMap nodeEntries)[k - ns.length]? := by
  rw [List.flatMap_cons]
  have hl : (nodeEntries (w, ns)).length = ns.length := by simp [nodeEntries]
  split
  · rw [List.getElem?_append_left (by omega)]
    simp [nodeEntries, List.getElem?_zipIdx, Function.comp_def]
  · rw [List.getElem?_append_right (by omega), hl]

/-- The loop's step: past `j` workloads, the remaining index `k` into the rest. -/
theorem zip_drop_cons {α β : Type} (xs : List α) (ys : List β) (j : Nat)
    (hx : j < xs.length) (hy : j < ys.length) :
    (xs.zip ys).drop j = (xs[j], ys[j]) :: (xs.zip ys).drop (j + 1) := by
  rw [List.drop_eq_getElem_cons (by simp; omega)]
  simp [List.getElem_zip]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : deployment.Assumptions]

theorem Deployment.Node.wp_proof :
    etcd_dist.Deployment.Node.spec (GF := GF) (hG := hG) := by
  intro v d n0
  wp_start as #Hd
  wp_auto
  iunfold deploymentRepr at Hd
  icases Hd with ⟨#Hm, %htok, %hcfg, #Hw, %ss, #Hn, #Hns⟩
  ihave %Hwl := ownSlice_len _ _ _ $$ Hw
  ihave %Hnl := ownSlice_len _ _ _ $$ Hn
  ihave %Hssl := BigSepL2.bigSepL2_length $$ Hns
  rw [List.length_map] at Hwl
  wp_if_destruct
  · iapply HΦ
    ipureintro
    intro h; cases h
  ihave HI : (∃ (j : Nat) (k : w64),
      "j" ∷ j_ptr ↦ W64 j ∗ "n" ∷ n_ptr ↦ k ∗
      "%Hj" ∷ ⌜j ≤ d.workloads.length ∧ j ≤ d.nodes.length ∧ 0 ≤ sint.Z k ∧
        d.nodeList[sint.nat n0]? = (((d.workloads.zip d.nodes).drop j).flatMap nodeEntries)[sint.nat k]?⌝ :
      IProp GF)
    $$ [j n]
  · iexists 0, n0
    iframe
    ipureintro
    refine ⟨by omega, by omega, by word, ?_⟩
    rw [nodeList_eq, List.drop_zero]
  wp_for HI
  obtain ⟨Hj1, Hj2, Hk0, Hjk⟩ := Hj
  wp_if_destruct
  · have hjw : j < d.workloads.length := by word
    by_cases hjn' : sint.Z (W64 (j : Int)) < sint.Z v.Nodes'.len
    · have hjn : j < d.nodes.length := by word
      simp only [hjn', decide_true, ↓reduceIte]
      wp_auto
      obtain ⟨s, hs⟩ : ∃ s, ss[j]? = some s := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨ns, hns⟩ : ∃ ns, d.nodes[j]? = some ns := ⟨_, List.getElem?_eq_getElem hjn⟩
      obtain ⟨w, hw⟩ : ∃ w, d.workloads[j]? = some w := ⟨_, List.getElem?_eq_getElem hjw⟩
      ihave #Hs := BigSepL2.bigSepL2_lookup hs hns $$ Hns
      ihave %Hsl := ownSlice_len _ _ _ $$ Hs
      have h0 : 0 ≤ sint.Z (W64 (j : Int)) := by word
      have hsj : (sint.Z (W64 (j : Int))).toNat = j := by word
      have hdrop : (d.workloads.zip d.nodes).drop j = (w, ns) :: (d.workloads.zip d.nodes).drop (j + 1) := by
        rw [zip_drop_cons _ _ j hjw hjn]
        rw [List.getElem?_eq_getElem hjw] at hw
        rw [List.getElem?_eq_getElem hjn] at hns
        simp only [Option.some.injEq] at hw hns
        rw [hw, hns]
      rw [hdrop] at Hjk
      simp only [h0, hjn', and_self, ↓reduceIte]
      wp_apply (wp_load_slice_index v.Nodes' (sint.Z (W64 (j : Int))) ss DFrac.discard s h0) $$ [] as -
      · iframe #; ipureintro; rw [hsj]; exact hs
      wp_if_destruct
      · -- `n < len(d.Nodes[j])`: client machine `n` of workload `j`
        have hkn : sint.nat k < ns.length := by word
        obtain ⟨a, ha⟩ : ∃ a, ns[sint.nat k]? = some a := ⟨_, List.getElem?_eq_getElem hkn⟩
        rw [nodeEntries_cons_get, if_pos hkn, ha, Option.map_some] at Hjk
        wp_for_post
        iapply HΦ
        ipureintro
        intro _
        refine ⟨by word, by word, Hk0, w, ns, a, ?_, ?_, ha, ?_⟩
        · show d.workloads[sint.nat (W64 (j : Int))]? = some w
          rw [show sint.nat (W64 (j : Int)) = j by word]; exact hw
        · show d.nodes[sint.nat (W64 (j : Int))]? = some ns
          rw [show sint.nat (W64 (j : Int)) = j by word]; exact hns
        · exact Hjk
      · -- the next workload, `n - len(d.Nodes[j])` into its client machines
        have hkn : ¬ sint.nat k < ns.length := by word
        rw [nodeEntries_cons_get, if_neg hkn] at Hjk
        simp only [h0, hjn', and_self, ↓reduceIte]
        wp_apply (wp_load_slice_index v.Nodes' (sint.Z (W64 (j : Int))) ss DFrac.discard s h0) $$ [] as -
        · iframe #; ipureintro; rw [hsj]; exact hs
        have hwj : W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) := by
          rw [show ((j + 1 : Nat) : Int) = (j : Int) + 1 by omega, W64, W64, W64, BitVec.ofInt_add]
        wp_for_post
        iframe
        iexists (j + 1), k - s.len
        rw [hwj]
        iframe
        ipureintro
        refine ⟨by omega, by omega, by word, ?_⟩
        rw [Hjk]
        congr 1
        word
    · simp only [hjn', decide_false, Bool.false_eq_true, ↓reduceIte]
      wp_auto
      iapply HΦ
      ipureintro
      intro h; cases h
  · iapply HΦ
    ipureintro
    intro h; cases h

end proof

end etcd_dist
end EtcdGrove
end Perennial
