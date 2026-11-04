/-
The proof of `Spec/go_etcd_io/bbolt/Cursor__search_w.lean` (U6d, `notes/bbolt-proof-plan.md`): by
Löb induction, `search` gets the position's node or page (`pageNode_w`), pushes it, and searches a
leaf (`nsearch_n`, `nsearch_p`) or a branch (`searchNode`, `searchPage`, inlined: the element
routing the key by `sort.Search` with its evaluated indices, then `search` below).
-/
module

public import Spec.go_etcd_io.bbolt.Cursor__search_w
public import Spec.go_etcd_io.bbolt.Cursor__nsearch_n
public import Spec.go_etcd_io.bbolt.Bucket__pageNode_w
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsLeafPage
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsBranchPage
public import Spec.go_etcd_io.bbolt.internal.common.Page__BranchPageElements
public import Spec.go_etcd_io.bbolt.internal.common.Page__Count
public import Spec.go_etcd_io.bbolt.internal.common.branchPageElement__Key
public import Spec.go_etcd_io.bbolt.internal.common.branchPageElement__Pgid
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Key
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Pgid
public import Perennial.Spec.bytes.Compare
public import Proof.go_etcd_io.bbolt.Read.SearchEv
public import Proof.go_etcd_io.bbolt.Read.WSearch
public import Proof.go_etcd_io.bbolt.Read.Bytes
public import Proof.go_etcd_io.bbolt.Cursor__search_r
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout

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

theorem Cursor.search_w.wp_aux
    (hpn : Bucket.pageNode_w.spec (GF := GF) (hG := hG))
    (hnp : Cursor.nsearch_p.spec (GF := GF) (hG := hG))
    (hnn : Cursor.nsearch_n.spec (GF := GF) (hG := hG))
    (hIL : internal.common.Page.IsLeafPage.spec (GF := GF) (hG := hG))
    (hIB : internal.common.Page.IsBranchPage.spec (GF := GF) (hG := hG))
    (hBE : internal.common.Page.BranchPageElements.spec (GF := GF) (hG := hG))
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG))
    (hBK : internal.common.branchPageElement.Key.spec (GF := GF) (hG := hG))
    (hBP : internal.common.branchPageElement.Pgid.spec (GF := GF) (hG := hG))
    (hIK : internal.common.Inode.Key.spec (GF := GF) (hG := hG))
    (hIP : internal.common.Inode.Pgid.spec (GF := GF) (hG := hG))
    (hS : Read.sort.SearchEv.spec (GF := GF) (hG := hG))
    (hC : bytes.Compare.spec (GF := GF) (hG := hG)) :
    ⊢ (∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc) (B : BRec) (c : Loc)
        (stk : GoSlice) (els : List elemRef) (pid : w64) (key : GoSlice) (ks : Src) (kb : List w8),
      ⌜X.t.bs !! bl = some B ∧ bktLocalOK X bl ∧ pmFresh X ∧ inlSrcOK X bl ∧ ks ≠ Src.stale ∧
        posOK X bl B pid ∧ (B.ib.root' = W64 0 → pid = W64 0)⌝ →
      ∀ Φ, (wtxW K tx r m X ∗ c ↦ Cursor.mk bl stk ∗ stk ↦* els ∗
          ownSliceCap elemRef stk (DFrac.own 1) ∗ srcOwn X.v key ks kb) -∗
        ▷ (∀ (stk' : GoSlice) (path : List elemRef) (pids : List w64),
          (wtxW K tx r m X ∗ c ↦ Cursor.mk bl stk' ∗ stk' ↦* (els ++ path) ∗
            ownSliceCap elemRef stk' (DFrac.own 1) ∗
            ⌜lPathFrom X bl pid path pids ∧ lRoutes X bl path pids kb⌝) -∗ Φ #()) -∗
        WP (App (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"search")) (Val #key))
          (Val #pid)) {{ Φ }}
      : IProp GF) := by
  iloeb as IH
  iintro %K %tx %r %m %X %bl %B %c %stk %els %pid %key %ks %kb %Hh %Φ ⟨Hw, Hc, Hs, Hcap, #Hkey⟩ HΦ
  obtain ⟨hB, hloc, hpm, hinl, hks, hpos, hpid0⟩ := Hh
  have hlive : bl ∈ X.liveB := hloc.1
  have hnmnn := bktLocalOK_nm_nonnull X bl B hloc hB
  obtain ⟨-, B0, hB0, hclean, hkeys, hpgl, hnsl, hvw⟩ := id hloc
  rw [hB] at hB0; cases hB0
  icases wtxW_pkgInit K tx r m X $$ Hw with ⟨Hw, #Hpkg⟩
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  icases wtxW_nodes_nonnull K tx r m X bl B hB $$ Hw with ⟨Hw, %Hnodes⟩
  ihave %Hmax := wtxW_page_maxMap K tx r m X $$ Hw
  wp_method_call; wp_call
  wp_auto
  rcases hpos with ⟨l, rn, hres, hrn⟩ | hpage
  · -- a materialized node
    have hlv : l ∈ X.live := hnsl l rn hrn
    wp_apply hpn K tx r m X bl B pid hB hlive hpid0 (fun h => absurd h Hnodes) hnmnn
      (fun h => by rw [hres] at h; cases h) $$ [Hw] as %p %n ⟨Hw, %Hpn⟩
    · iexact Hw
    rw [hres] at Hpn
    obtain ⟨rfl, rfl⟩ := Hpn
    have hnn0 : n ≠ null := by
      by_cases h0 : B.ib.root' = W64 0
      · unfold resolve at hres; rw [if_pos h0] at hres
        by_cases h1 : B.bv.rootNode' = null
        · rw [if_pos h1] at hres; cases hres
        · rw [if_neg h1] at hres; cases hres; exact h1
      · rw [resolve_tree B pid h0] at hres; exact hnmnn _ _ hres
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_slice_append $$ [$Hs $Hcap $Hsl] as %s1 ⟨Hs, Hcap, -⟩
    try wp_auto
    wp_method_call; wp_call
    wp_auto
    rw [decide_eq_false hnn0]
    wp_auto
    icases wtxW_node_cells_acc K tx r m X bl B n rn hB hrn hlv $$ Hw with ⟨%Hbase, Ho, Hcells, Hwb⟩
    isimp only [objOwn] at Ho
    icases Ho with ⟨Hn, Hins, Hcapn, Hws, Hch, Hchcap, Hnk⟩
    icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn⟩
    iStructNamed Hn
    wp_auto
    ihave Hn : (n ↦ rn.nv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ihave %Hinl := ownSlice_len _ _ _ $$ Hins
    ihave %Hwl := BigSepL2.bigSepL2_length $$ Hws
    have hnc := hclean.2.2.2.2.2.2.2.1 n rn hrn
    have hlen63 : rn.ws.length < 2 ^ 63 := by have := Hinl.2; rw [← Hwl, Hinl.1]; word
    ihave Ho : objOwn X.v n (DFrac.own 1) true (.node bl rn) $$ [Hn Hins Hcapn Hws Hch Hchcap Hnk]
    · simp only [objOwn]; iframe
    have hlt : ltree X bl pid = some (rn.nv.isLeaf', rn.ws) := ltree_node X bl B pid n rn hB hres hrn
    have hra : refAt X bl pid ⟨null, n, W64 0⟩ := refAt_node X bl B pid n _ hB hres rfl
    cases hleaf : rn.nv.isLeaf'
    · -- a branch node: `searchNode`, inlined
      wp_auto
      rw [decide_eq_false hnn0]
      wp_auto
      wp_method_call; wp_call
      wp_auto
      isimp only [objOwn] at Ho
      icases Ho with ⟨Hn, Hins, Hcapn, Hws, Hch, Hchcap, Hnk⟩
      iStructNamed Hn
      wp_auto
      ihave Hn : (n ↦ rn.nv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
      · iapply typedPointsto_combine _ _ _ Hnn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      icases (viewCells_halves wq X.v).1 $$ Hcells with ⟨Hv1, Hv2⟩
      icases srcOwn_acc wq.half X.v key ks kb hks Hbase $$ [Hv1] with ⟨%dk, Hk, Hkb⟩
      · iframe; iframe #
      have Hlen : sint.Z rn.nv.inodes'.len = (rn.ws.length : Int) := by word
      have hsorted := hnc.2.2.2.1
      have hwsl := hnc.2.2.2.2.2.1
      wp_apply hS rn.nv.inodes'.len _ (Write.gePred rn.ws kb)
        (fun L => iprop(n_ptr ↦ n ∗ key_ptr ↦ key ∗ n ↦ rn.nv ∗ rn.nv.inodes' ↦* rn.ins ∗
          ([∗list] it;w ∈ rn.ins;rn.ws, wOwn X.v true it w) ∗ viewCells wq.half X.v ∗
          key ↦*{dk} kb ∗ exact_ptr ↦ snExact rn.ws kb L ∗
          ⌜∀ j ∈ L, 0 ≤ j ∧ j < (rn.ws.length : Int)⌝))
        $$ [n key Hn Hins Hws Hv2 Hk exact]
      · iframe
        isplitl []
        · ipureintro; word
        isplitl []
        · unfold Read.predImplementsL
          iintro %L %i
          wp_start as ⟨⟨Hnp, Hkp, Hn, Hins, Hws, Hv2, Hk, Hex, %HL⟩, %Hbi⟩
          rw [Hlen] at Hbi
          iStructNamed Hn
          wp_auto
          ihave Hn : (n ↦ rn.nv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
          · iapply typedPointsto_combine _ _ _ Hnn
            simp only [TypedPointsto.typedPointstoDef]
            iframe
          rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hbi.1, by rw [Hlen]; exact Hbi.2⟩)]
          list_elem rn.ins (sint.Z i).toNat as it
          list_elem rn.ws (sint.Z i).toNat as w
          icases ownSlice_elem_acc (sint.Z i) it _ _ rn.ins Hbi.1 Hit_lookup $$ Hins with ⟨Hit, Hsb⟩
          wp_apply hIK $$ [$Hit] as Hit
          try wp_auto
          icases BigSepL2.bigSepL2_lookup_acc Hit_lookup Hw_lookup $$ Hws with ⟨Hw1, Hwsback⟩
          unfold wOwn
          simp only [↓reduceIte]
          icases Hw1 with ⟨%Hfp, Hik, Hiv⟩
          have Hwks : w.ks ≠ Src.stale := (hwsl w (List.mem_of_getElem? Hw_lookup)).1
          icases srcOwn_acc wq.half X.v it.key' w.ks w.key Hwks Hbase $$ [Hik Hv2] with ⟨%dik, Hik, Hikb⟩
          · iframe
          wp_apply hC $$ [Hik Hk] as ⟨Hik, Hk⟩
          · iframe
          icases Hikb $$ Hik with ⟨Hik, Hv2⟩
          ihave Hws := Hwsback $$ [Hik Hiv]
          · iframe; ipureintro; exact Hfp
          ihave Hins := Hsb $$ Hit
          rw [list_set_lookup_self _ _ _ Hit_lookup]
          have Hek : wKey rn.ws (sint.Z i).toNat = w.key := by
            unfold wKey; rw [Hw_lookup]; rfl
          have hcr0 : bytes.compareResult w.key kb = W64 0 ↔ w.key = kb := by
            unfold bytes.compareResult
            constructor
            · intro h; split at h
              · cases h
              · split at h
                · assumption
                · cases h
            · intro h; subst h; simp [go.goStringLt_irrefl]
          have hcrm : bytes.compareResult w.key kb = W64 (-1) ↔ go.GoStringLt w.key kb := by
            unfold bytes.compareResult
            constructor
            · intro h; split at h
              · assumption
              · split at h <;> cases h
            · intro h; simp [h]
          wp_if_destruct
          · try wp_auto
            iapply HΦ
            iframe
            isplitl
            · have : snExact rn.ws kb (sint.Z i :: L) = true := by
                unfold snExact; simp only [decide_eq_true_eq]
                exact ⟨sint.Z i, List.mem_cons_self .., by rw [Hek]; exact hcr0.1 Hif⟩
              rw [this]; iframe
              ipureintro; intro j hj
              rcases List.mem_cons.mp hj with rfl | hj
              · omega
              · exact HL j hj
            ipureintro
            unfold Write.gePred
            rw [Hek]
            by_cases hlt : go.GoStringLt w.key kb
            · exact absurd (hcr0.1 Hif ▸ hlt) (go.goStringLt_irrefl _)
            · simp [hlt, show ¬ bytes.compareResult w.key kb = W64 (-1) from fun h => hlt (hcrm.1 h)]
          · try wp_auto
            iapply HΦ
            iframe
            isplitl
            · have : snExact rn.ws kb (sint.Z i :: L) = snExact rn.ws kb L := by
                unfold snExact
                congr 1
                apply propext
                constructor
                · rintro ⟨j, hj, hjk⟩
                  rcases List.mem_cons.mp hj with rfl | hj
                  · exfalso; apply Hif; apply hcr0.2; rw [Hek] at hjk; exact hjk
                  · exact ⟨j, hj, hjk⟩
                · rintro ⟨j, hj, hjk⟩; exact ⟨j, List.mem_cons_of_mem _ hj, hjk⟩
              rw [this]; iframe
              ipureintro; intro j hj
              rcases List.mem_cons.mp hj with rfl | hj
              · omega
              · exact HL j hj
            ipureintro
            unfold Write.gePred
            rw [Hek]
            by_cases hlt : go.GoStringLt w.key kb
            · simp [hlt, hcrm.2 hlt]
            · simp [hlt, show ¬ bytes.compareResult w.key kb = W64 (-1) from fun h => hlt (hcrm.1 h)]
        isplitl []
        · ipureintro; simp [snExact]
        ipureintro; rw [Hlen]; exact Write.gePred_mono rn.ws kb hsorted
      iintro %idx ⟨%L, ⟨Hnp, Hkp, Hn, Hins, Hws, Hv2, Hk, Hex, %HL⟩, %H0, %Hfound, %Hoob, %Hgt, %Hev⟩
      rw [Hlen] at Hfound Hoob Hev
      sorry
    · -- a leaf node
      wp_auto
      wp_apply hnn c bl s1 els ⟨null, n, W64 0⟩ X.v bl rn wq key ks kb hnn0 hnc.2.2.2.1
        hnc.2.2.2.2.2.1 hks Hbase $$ [Hc Hs Ho Hcells] as ⟨Hc, Hs, Ho, Hcells⟩
      · iframe; iframe #
      ihave Hw := Hwb $$ Ho Hcells
      try wp_auto
      iapply HΦ $$ %s1 %([⟨null, n, W64 (wsIdx rn.ws kb : Int)⟩] : List elemRef) %([pid] : List w64)
      iframe
      ipureintro
      rw [hleaf] at hlt
      have hix : wsIdx rn.ws kb ≤ rn.ws.length := by
        unfold wsIdx; exact (List.takeWhile_sublist _).length_le
      refine ⟨lPathFrom_leaf X bl pid _ rn.ws (refAt_node X bl B pid n _ hB hres rfl) hlt,
        lRoutes_leaf X bl pid _ rn.ws kb hlt ?_⟩
      show (W64 (wsIdx rn.ws kb : Int)).toNat = wsIdx rn.ws kb
      simp; omega
  · sorry

end proof

end bbolt
end EtcdGrove
end Perennial
