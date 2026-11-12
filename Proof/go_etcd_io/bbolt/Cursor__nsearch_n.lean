/-
The proof of `Spec/go_etcd_io/bbolt/Cursor__nsearch_n.lean` (U6d, `notes/bbolt-proof-plan.md`):
`sort.Search` over the node's inodes, comparing each inode's key (read through its source) with
the key, as `node.put`'s search (U7).
-/
module

public import Spec.go_etcd_io.bbolt.Cursor__nsearch_n
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Key
public import Perennial.Spec.sort.Search
public import Perennial.Spec.bytes.Compare
public import Proof.go_etcd_io.bbolt.Rebalance.Base
public import Proof.go_etcd_io.bbolt.Write.NodeEnts
public import Proof.go_etcd_io.bbolt.Read.WKey

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

theorem Cursor.nsearch_n.wp_proofQ
    (hK : internal.common.Inode.Key.spec (GF := GF) (hG := hG))
    (hS : sort.Search.spec (GF := GF) (hG := hG)) (hC : bytes.Compare.spec (GF := GF) (hG := hG)) :
    Cursor.nsearch_n.specQ (GF := GF) (hG := hG) := by
  intro c b stk els e v bl rn qn q key kr kb hnode Hsorted Hlive Hbase
  wp_start as ⟨Hc, Hs, Ho, Hv, Hkp⟩
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  isimp only [objOwn] at Ho
  icases Ho with ⟨Hn, Hins, Hcap, Hws, Hch, Hchcap, Hkey⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hins
  ihave %Hwl := BigSepL2.bigSepL2_length $$ Hws
  icases (viewCells_halves q v).1 $$ Hv with ⟨Hv1, Hv2⟩
  icases keyR_cells_acc q.half v Hbase key kr kb $$ [Hkp Hv1] with ⟨%dk, Hk, Hkb⟩
  · iframe
  ihave %Hstl := ownSlice_len _ _ _ $$ Hs
  wp_auto
  have hidx : sint.Z (stk.len - W64 1) = (els.length : Int) := by
    simp only [List.length_append, List.length_singleton] at Hstl; word
  rw [if_pos (show 0 ≤ sint.Z (stk.len - W64 1) ∧ sint.Z (stk.len - W64 1) < sint.Z stk.len by
    rw [hidx]; word)]
  icases ownSlice_elem_acc (sint.Z (stk.len - W64 1)) e _ _ (els ++ [e]) (by omega)
    (by rw [hidx]; simp) $$ Hs with ⟨He, Hsback⟩
  rw [hidx]
  wp_auto
  rw [decide_eq_false hnode]
  wp_auto
  icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn⟩
  iStructNamed Hn
  try wp_auto
  ihave Hn : (e.node' ↦{DFrac.own qn} rn.nv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  have Hlen : sint.Z rn.nv.inodes'.len = (rn.ws.length : Int) := by word
  wp_apply hS rn.nv.inodes'.len _ (Write.gePred rn.ws kb)
    iprop(n_ptr ↦ e.node' ∗ key_ptr ↦ key ∗ e.node' ↦{DFrac.own qn} rn.nv ∗ rn.nv.inodes' ↦*{DFrac.own qn} rn.ins ∗
      ([∗list] it;w ∈ rn.ins;rn.ws, wOwn v true it w) ∗ viewCells q.half v ∗
      key ↦*{dk} kb) $$ [n key Hn Hins Hws Hv2 Hk]
  · iframe
    isplitl []
    · ipureintro; word
    isplitl []
    · unfold sort.predImplements
      iintro %i
      wp_start as ⟨⟨Hnp, Hkp', Hn, Hins, Hws, Hv2, Hk⟩, %Hb⟩
      iStructNamed Hn
      wp_auto
      ihave Hn : (e.node' ↦{DFrac.own qn} rn.nv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
      · iapply typedPointsto_combine _ _ _ Hnn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hb.1, Hb.2⟩)]
      list_elem rn.ins (sint.Z i).toNat as it
      list_elem rn.ws (sint.Z i).toNat as w
      icases ownSlice_elem_acc (sint.Z i) it _ _ rn.ins Hb.1 Hit_lookup $$ Hins with ⟨Hit, Hsb⟩
      wp_apply hK $$ [$Hit] as Hit
      try wp_auto
      icases BigSepL2.bigSepL2_lookup_acc Hit_lookup Hw_lookup $$ Hws with ⟨Hw1, Hwsback⟩
      unfold wOwn
      simp only [↓reduceIte]
      icases Hw1 with ⟨%Hfp, Hik, Hiv⟩
      have Hwks : w.ks ≠ Src.stale := (Hlive w (List.mem_of_getElem? Hw_lookup)).1
      icases srcOwn_acc q.half v it.key' w.ks w.key Hwks Hbase $$ [Hik Hv2] with ⟨%dik, Hik, Hikb⟩
      · iframe
      wp_apply hC $$ [Hik Hk] as ⟨Hik, Hk⟩
      · iframe
      try wp_auto
      icases Hikb $$ Hik with ⟨Hik, Hv2⟩
      ihave Hws := Hwsback $$ [Hik Hiv]
      · iframe; ipureintro; exact Hfp
      ihave Hins := Hsb $$ Hit
      rw [list_set_lookup_self _ _ _ Hit_lookup]
      iapply HΦ
      iframe
      ipureintro
      have Hek : wKey rn.ws (sint.Z i).toNat = w.key := by
        unfold wKey; rw [Hw_lookup]; rfl
      simp only [Write.gePred, Hek, bytes.compareResult]
      by_cases hlt : go.GoStringLt w.key kb
      · simp [hlt]
      · simp only [hlt, ↓reduceIte]
        split <;> decide
    ipureintro; rw [Hlen]; exact Write.gePred_mono rn.ws kb Hsorted
  iintro %idx ⟨⟨Hnp, Hkp', Hn, Hins, Hws, Hv2, Hk⟩, %H0, %Hfound, %Hoob, %Hgt⟩
  rw [Hlen] at Hfound Hoob
  have Hle : sint.Z idx ≤ (rn.ws.length : Int) := by
    rcases Int.lt_or_le (rn.ws.length : Int) (sint.Z idx) with hc | hc
    · have := Hoob (fun k hk => Hgt k ⟨hk.1, by omega⟩)
      omega
    · exact hc
  have Hidx : wsIdx rn.ws kb = sint.nat idx := by
    apply Write.wsIdx_of_bounds rn.ws kb _ (by word)
    · intro k hk
      have := Hgt (k : Int) ⟨by omega, by word⟩
      simpa [Write.gePred] using this
    · intro hk
      have := Hfound (by word)
      simpa [Write.gePred, show ((sint.Z idx).toNat) = sint.nat idx from rfl] using this
  wp_auto
  ihave Hs := Hsback $$ He
  have hW : W64 (wsIdx rn.ws kb : Int) = idx := by rw [Hidx]; word
  rw [hW]
  rw [show (els ++ [e]).set (↑els.length : Int).toNat
      ({ page' := e.page', node' := e.node', index' := idx } : elemRef) =
      els ++ [{ page' := e.page', node' := e.node', index' := idx }] by simp]
  icases Hkb $$ Hk with ⟨Hkp, Hv1⟩
  iapply HΦ
  iframe
  isplitl [Hn Hins Hcap Hws Hch Hchcap Hkey]
  · simp only [objOwn]; iframe
  iapply (viewCells_halves q v).2
  iframe

/-- `nsearch` on a node owned whole (`qn = 1`). -/
theorem Cursor.nsearch_n.wp_proof
    (hK : internal.common.Inode.Key.spec (GF := GF) (hG := hG))
    (hS : sort.Search.spec (GF := GF) (hG := hG)) (hC : bytes.Compare.spec (GF := GF) (hG := hG)) :
    Cursor.nsearch_n.spec (GF := GF) (hG := hG) := by
  intro c b stk els e v bl rn q
  exact Cursor.nsearch_n.wp_proofQ hK hS hC c b stk els e v bl rn 1 q

end proof

end bbolt
end EtcdGrove
end Perennial
