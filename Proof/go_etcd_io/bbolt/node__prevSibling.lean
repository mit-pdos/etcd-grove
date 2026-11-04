/-
The proof of `Spec/go_etcd_io/bbolt/node__prevSibling.lean`: U8 (`notes/bbolt-proof-plan.md`).
-/
module

public import Spec.go_etcd_io.bbolt.node__prevSibling
public import Spec.go_etcd_io.bbolt.node__childIndex
public import Spec.go_etcd_io.bbolt.node__childAt
public import Proof.go_etcd_io.bbolt.Rebalance.Heap
public import Proof.go_etcd_io.bbolt.Rebalance.Base
public import Proof.go_etcd_io.bbolt.Read.Base
public import Proof.go_etcd_io.bbolt.Inv.WtxBase

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem node.prevSibling.wp_proof (hCI : node.childIndex.spec (GF := GF) (hG := hG))
    (hCA : node.childAt.spec (GF := GF) (hG := hG)) :
    node.prevSibling.spec (GF := GF) (hG := hG) := by
  intro K tx r m X bl B n rn hb hn hbl hnl hbll hnodes hpar
  wp_start as Hw
  ihave %Hbase := wtxW_base_pos K tx r m X $$ Hw
  unfold wtxW wtxCore
  icases Hw with ⟨⟨#Hpkg', #Hcore, %Hr, #Hreg, Hh, Hfills, Hbk, Hnl, Hdb, Hview, Hst⟩, Hcells, Hmap⟩
  ihave %Hok := wtxHeap_heapOK tx (DFrac.own 1) X $$ Hh
  ihave %Ho := wtxHeap_objs_node tx (DFrac.own 1) X bl B n rn hb hn $$ Hh
  icases wtxHeap_node_ptr_acc tx (DFrac.own 1) X bl n rn Ho $$ Hh with ⟨Hn, Hback⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn⟩
  iStructNamed Hn
  wp_auto
  ihave Hn : (n ↦ rn.nv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  ihave Hh := Hback $$ Hn
  by_cases hp0 : rn.nv.parent' = null
  · rw [decide_eq_true hp0]
    wp_auto
    iapply HΦ
    iexists X
    iframe; iframe #
    ipureintro
    exact ⟨Hr, Or.inl ⟨rfl, rfl, Or.inl hp0⟩⟩
  rw [decide_eq_false hp0]
  wp_auto
  obtain ⟨hkey, hks, rp, hrp, hpleaf, hpbl, hpl, hps, hplive, hready⟩ := hpar hp0
  have hne : n ≠ rn.nv.parent' := fun h => Hok.2.2.2.1 bl B n rn hb hn h.symm
  icases wtxHeap_two_nodes_acc tx (DFrac.own 1) X bl B n rn.nv.parent' rn rp hb hn hrp hnl hpl hne
    $$ Hh with ⟨Hon, Hop, Hback⟩
  unfold objOwn
  icases Hon with ⟨Hn, Hns, Hncap, Hnws, Hnch, Hnchcap, Hnkey⟩
  rw [if_pos (show true = true ∧ rn.nv.key' ≠ slice.nil from ⟨rfl, hkey⟩)]
  icases Hnkey with #Hnkey
  ihave Hop : objOwn X.v rn.nv.parent' (DFrac.own 1) true (.node bl rp) $$ [Hop]
  · unfold objOwn; iexact Hop
  icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn'⟩
  iStructNamed Hn
  wp_auto
  ihave Hn : (n ↦ rn.nv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  wp_apply hCI X.v rn.nv.parent' bl rp (DFrac.own 1) wq n rn.nv (DFrac.own 1) rn.ksrc rn.key
    hps hplive hks Hbase $$ [Hop Hcells Hn] as ⟨Hop, Hcells, Hn⟩
  · iframe; iframe #
  try wp_auto
  unfold objOwn
  icases Hop with ⟨Hp, Hps, Hpcap, Hpws, Hpch, Hpchcap, Hpkey⟩
  ihave %Hpsl := ownSlice_len _ _ _ $$ Hps
  ihave %Hpwl := BigSepL2.bigSepL2_length $$ Hpws
  have Hlen : sint.Z rp.nv.inodes'.len = (rp.ws.length : Int) := by word
  have Hidx : wsIdx rp.ws rn.key ≤ rp.ws.length := by
    unfold wsIdx; exact (List.takeWhile_sublist _).length_le
  ihave Hh := Hback $$ [Hn Hns Hncap Hnws Hnch Hnchcap] [Hp Hps Hpcap Hpws Hpch Hpchcap Hpkey]
  · iframe
    rw [if_pos (show True ∧ rn.nv.key' ≠ slice.nil from ⟨trivial, hkey⟩)]
    iexact Hnkey
  · iframe
    simp only
    iexact Hpkey
  wp_if_destruct
  · iapply HΦ
    iexists X
    iframe; iframe #
    ipureintro
    refine ⟨Hr, Or.inl ⟨rfl, rfl, Or.inr ⟨rp, hrp, ?_⟩⟩⟩
    word
  · have Hpos : 0 < wsIdx rp.ws rn.key := by
      rcases Nat.eq_zero_or_pos (wsIdx rp.ws rn.key) with h | h
      · exfalso; apply Hif; rw [h]; rfl
      · exact h
    have Hlt : wsIdx rp.ws rn.key - 1 < rp.ws.length := by omega
    obtain ⟨w, hw⟩ : ∃ w, rp.ws[wsIdx rp.ws rn.key - 1]? = some w :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    icases wtxHeap_node_ptr_acc tx (DFrac.own 1) X bl n rn Ho $$ Hh with ⟨Hn, Hback⟩
    iStructNamed Hn
    wp_auto
    ihave Hn : (n ↦ rn.nv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ihave Hh := Hback $$ Hn
    wp_apply hCA K tx r m X bl B rn.nv.parent' rp (W64 ((wsIdx rp.ws rn.key : Int)) - W64 1) w
      hb hrp hpbl hpleaf hpl hbll hnodes (by word)
      (by rw [show sint.nat (W64 ((wsIdx rp.ws rn.key : Int)) - W64 1) = wsIdx rp.ws rn.key - 1
            by word]; exact hw)
      (hready w Hpos hw).1 (hready w Hpos hw).2 $$ [Hh Hfills Hbk Hnl Hdb Hview Hst Hcells Hmap]
      as %l ⟨%X', Hw, %Hpost⟩
    · unfold wtxW wtxCore; iframe; iframe #; ipureintro; exact Hr
    try wp_auto
    iapply HΦ
    iexists X'
    unfold wtxW wtxCore
    iframe
    ipureintro
    exact Or.inr ⟨rp, w, hrp, Hpos, hw, Hpost⟩

end proof

end bbolt
end EtcdGrove
end Perennial
