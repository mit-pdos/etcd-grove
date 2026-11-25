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
    simp [nodeEntries, List.getElem?_zipIdx]
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
  · -- both conditions hold
    have hjw : j < d.workloads.length := by word
    have hjn : j < d.nodes.length := by word
    obtain ⟨s, hs⟩ : ∃ s, ss[j]? = some s := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have h0 : 0 ≤ sint.Z (W64 (j : Int)) := by word
    have hsj : (sint.Z (W64 (j : Int))).toNat = j := by word
    ihave %Hsl := BigSepL2.bigSepL2_lookup_iff ⟨_, _⟩ $$ Hns
    sorry
  · sorry

end proof

end etcd_dist
end EtcdGrove
end Perennial
