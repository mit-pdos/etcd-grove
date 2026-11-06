/-
The proof of `Spec/go_etcd_io/bbolt/node__childAt.lean`: U8 (`notes/bbolt-proof-plan.md`), over `Rebalance/Heap`'s
`wtxHeap_objsDisj` (a `sorry` pending a shared fix).
-/
module

public import Spec.go_etcd_io.bbolt.node__childAt
public import Spec.go_etcd_io.bbolt.Bucket__node
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Pgid
public import Proof.go_etcd_io.bbolt.Rebalance.Heap
public import Proof.go_etcd_io.bbolt.Read.Base

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

theorem node.childAt.wp_proof (hPg : internal.common.Inode.Pgid.spec (GF := GF) (hG := hG))
    (hN : Bucket.node.spec (GF := GF) (hG := hG)) :
    node.childAt.spec (GF := GF) (hG := hG) := by
  intro K tx r m X bl B n rn i w hb hn hbl hleaf hnl hbll hnodes hi hw hnm hready hpg0
  wp_start as Hw
  unfold wtxW wtxCore
  icases Hw with ⟨⟨#Hpkg', #Hcore, %Hr, #Hreg, Hh, Hfills, Hbk, Hnl, Hdb, Hview, Hst⟩, Hcells, Hmap⟩
  icases wtxHeap_live_node_acc tx (DFrac.own 1) X bl B n rn hb hn hnl $$ Hh with ⟨Ho, Hback⟩
  unfold objOwn
  icases Ho with ⟨Hn, Hs, Hcap, Hws, Hch, Hchcap, Hkey⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  ihave %Hwl := BigSepL2.bigSepL2_length $$ Hws
  iStructNamed Hn
  wp_auto
  rw [hleaf]
  wp_auto
  have Hilt : sint.nat i < rn.ins.length := by
    have := (List.getElem?_eq_some_iff.1 hw).1; omega
  rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z rn.nv.inodes'.len
    from ⟨hi, by word⟩))]
  list_elem rn.ins (sint.Z i).toNat as it
  icases ownSlice_elem_acc (sint.Z i) it _ _ rn.ins hi Hit_lookup $$ Hs with ⟨Hit, Hsback⟩
  wp_apply hPg $$ [$Hit] as Hit
  try wp_auto
  icases BigSepL2.bigSepL2_lookup_acc Hit_lookup hw $$ Hws with ⟨Hw1, Hwsback⟩
  unfold wOwn
  icases Hw1 with ⟨%Hfp, Hik⟩
  ihave Hws := Hwsback $$ [Hik]
  · iframe; ipureintro; exact Hfp
  ihave Hs := Hsback $$ Hit
  rw [list_set_lookup_self _ _ _ Hit_lookup, Hfp.2]
  ihave Hn : (n ↦ rn.nv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    rw [hleaf]
    iframe
  ihave Hh := Hback $$ [Hn Hs Hcap Hws Hch Hchcap Hkey]
  · iframe
  rw [hbl]
  wp_apply hN K tx r m X bl B w.pgid n hb hbll hnodes hnm
    (fun h => ⟨hready h, Or.inr ⟨rn, hn, hleaf, hnl⟩⟩) (fun _ => hpg0) $$ [Hh Hfills Hbk Hnl Hdb Hview Hst Hcells Hmap]
    as %l ⟨%X', Hw, %Hpost⟩
  · unfold wtxW wtxCore; iframe; iframe #; ipureintro; exact Hr
  iapply HΦ
  iexists X'
  unfold wtxW wtxCore
  iframe
  ipureintro; exact Hpost

end proof

end bbolt
end EtcdGrove
end Perennial
