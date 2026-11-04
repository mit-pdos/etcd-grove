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
        · ipureintro; simp
        ipureintro; rw [Hlen]; exact Write.gePred_mono rn.ws kb hsorted
      iintro %idx ⟨%L, ⟨Hnp, Hkp, Hn, Hins, Hws, Hv2, Hk, Hex, %HL⟩, %H0, %Hfound, %Hoob, %Hgt, %Hev⟩
      rw [Hlen] at Hfound Hoob Hev
      have hbr := hnc.2.2.2.2.2.2.2.2.2.2.2.2.1 hleaf
      have hR := sn_route rn.ws kb L (sint.Z idx) hbr.1 hsorted H0 Hfound Hoob Hgt Hev HL
      wp_auto
      wp_join iprop(∃ ri : w64, index_ptr ↦ ri ∗
          ⌜sint.Z ri = (if snExact rn.ws kb L = true then sint.Z idx
            else if 0 < sint.Z idx then sint.Z idx - 1 else sint.Z idx)⌝)
        at next with [index] as ⟨%ri, index, %Hri⟩
      · cases hex : snExact rn.ws kb L
        · wp_auto
          wp_if_destruct
          · wp_join_done
            iexists _; iframe; ipureintro
            rw [if_pos (by word)]; word
          · wp_join_done
            iexists _; iframe; ipureintro
            rw [if_neg (by word)]
        · wp_auto
          wp_join_done
          iexists _; iframe; ipureintro; simp
      rw [← Hri] at hR
      ihave %Hsl := ownSlice_len _ _ _ $$ Hs
      have hsidx : sint.Z (s1.len - W64 1) = (els.length : Int) := by
        simp only [List.length_append, List.length_singleton] at Hsl; word
      rw [if_pos (show 0 ≤ sint.Z (s1.len - W64 1) ∧ sint.Z (s1.len - W64 1) < sint.Z s1.len by
        rw [hsidx]; word)]
      icases ownSlice_elem_acc (sint.Z (s1.len - W64 1)) (⟨null, n, W64 0⟩ : elemRef) _ _
        (els ++ [⟨null, n, W64 0⟩]) (by omega) (by rw [hsidx]; simp) $$ Hs with ⟨He, Hsback⟩
      rw [hsidx]
      wp_auto
      ihave Hs := Hsback $$ He
      simp only [show ∀ (a x : elemRef), (els ++ [a]).set (↑els.length : Int).toNat x = els ++ [x]
        from fun a x => by simp]
      iStructNamed Hn
      try wp_auto
      ihave Hn : (n ↦ rn.nv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
      · iapply typedPointsto_combine _ _ _ Hnn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      obtain ⟨k, hk⟩ : ∃ k : Nat, sint.Z ri = (k : Int) := ⟨(sint.Z ri).toNat, by omega⟩
      rw [if_pos (show 0 ≤ sint.Z ri ∧ sint.Z ri < sint.Z rn.nv.inodes'.len by
        rw [Hlen]; omega)]
      list_elem rn.ins (sint.Z ri).toNat as it
      list_elem rn.ws (sint.Z ri).toNat as w
      icases ownSlice_elem_acc (sint.Z ri) it _ _ rn.ins (by omega) Hit_lookup $$ Hins with ⟨Hit, Hsb⟩
      wp_apply hIP $$ [$Hit] as Hit
      icases BigSepL2.bigSepL2_lookup_acc Hit_lookup Hw_lookup $$ Hws with ⟨Hw1, Hwsback⟩
      isimp only [wOwn] at Hw1
      icases Hw1 with ⟨%Hfp, Hwr⟩
      ihave Hws := Hwsback $$ [Hwr]
      · isimp only [wOwn]; iframe; ipureintro; exact Hfp
      ihave Hins := Hsb $$ Hit
      rw [list_set_lookup_self _ _ _ Hit_lookup]
      icases Hkb $$ Hk with ⟨-, Hv1⟩
      ihave Hcells : viewCells wq X.v $$ [Hv1 Hv2]
      · iapply (viewCells_halves wq X.v).2; iframe
      ihave Ho : objOwn X.v n (DFrac.own 1) true (.node bl rn) $$ [Hn Hins Hcapn Hws Hch Hchcap Hnk]
      · simp only [objOwn]; iframe
      ihave Hw := Hwb $$ Ho Hcells
      rw [Hfp.2]
      have hk' : (sint.Z ri).toNat = k := by omega
      obtain ⟨hR1, -, -⟩ := hR
      rw [hk'] at Hw_lookup hR1
      have hroot : B.ib.root' ≠ W64 0 := by
        intro h0
        have := hclean.2.2.2.2.2.2.1 h0 n rn hrn
        rw [hleaf] at this; cases this
      have Hch' : X.t.bs !! bl = some B ∧ bktLocalOK X bl ∧ pmFresh X ∧ inlSrcOK X bl ∧
          ks ≠ Src.stale ∧ posOK X bl B w.pgid ∧ (B.ib.root' = W64 0 → w.pgid = W64 0) :=
        ⟨hB, hloc, hpm, hinl, hks, posOK_node_child X bl B n rn k w hloc hB hrn hleaf Hw_lookup,
          fun h => absurd h hroot⟩
      wp_apply IH $$ %K %tx %r %m %X %bl %B %c %s1 %(els ++ [⟨null, n, ri⟩]) %w.pgid %key %ks %kb
        %Hch' [Hw Hc Hs Hcap] as %stk'' %path' %pids' ⟨Hw, Hc, Hs, Hcap, %Hrt⟩
      · iframe; iframe #
      iapply HΦ $$ %stk'' %((⟨null, n, ri⟩ : elemRef) :: path') %(pid :: pids')
      rw [List.append_assoc]
      iframe
      ipureintro
      have hri : ri.toNat = k := by word
      rw [hleaf] at hlt
      refine ⟨lPathFrom_cons X bl pid ⟨null, n, ri⟩ rn.ws w path' pids'
          (refAt_node X bl B pid n _ hB hres rfl) hlt (by rw [hri]; exact Hw_lookup) Hrt.1,
        lRoutes_cons X bl pid ⟨null, n, ri⟩ rn.ws path' pids' kb hlt ?_ Hrt.2⟩
      show ri.toNat < _ ∧ _
      rw [hri]; exact nRoute_lroute rn.ws kb k hR1
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
  · -- a page: the inline page, or a view page
    obtain ⟨hres, pa, pg, hw, h16, hsrc, hpa, hpre, hkind⟩ :=
      posOK_page_facts X bl B pid hB hloc hpm hinl Hmax hpage
    icases wtxW_page_srcLoc K tx r m X bl B pid pa pg hB hlive hw hsrc hpa $$ Hw with ⟨Hw, #Hsrc⟩
    wp_apply hpn K tx r m X bl B pid hB hlive hpid0 (fun h => absurd h Hnodes) hnmnn
      (fun _ => ⟨pa, pg, hw, hsrc, hpre⟩) $$ [Hw] as %p %n ⟨Hw, %Hpn⟩
    · iexact Hw
    rw [hres] at Hpn
    obtain ⟨rfl, pg', hw'⟩ := Hpn
    rw [hw] at hw'
    simp only [Option.some.injEq, Prod.mk.injEq] at hw'
    obtain ⟨rfl, rfl⟩ := hw'
    icases wtxW_cells_acc K tx r m X $$ Hw with ⟨%Hbase, Hcells, Hwb⟩
    icases cells_page_key_acc wq X.v Hbase pa (pgSrc B) pg key ks kb hks $$ [Hcells]
      with ⟨%dq, %dk, Hp, Hk, Hpb⟩
    · iframe; iframe #
    icases Read.bytesPointsto_bounds pa dq pg (by intro e; simp [e] at h16) $$ Hp with ⟨Hp, %Hlb⟩
    have hlnn : pa ≠ null := by intro e; subst e; simp [null] at Hlb
    icases bytesPointsto_view_read (V := Page) pa dq pg 0 pa (by simp) (by omega) Hlb.1 $$ Hp
      with ⟨Hh, Hhb⟩
    rw [show (decode (List.take 16 (List.drop 0 pg)) : Page) = pageHdr pg from rfl]
    obtain ⟨hd, hH⟩ : ∃ hd, pageHdr pg = hd := ⟨_, rfl⟩
    have hfz : pageFlags pg = hd.flags'.toNat := by unfold pageFlags; rw [hH]
    rw [hH]
    rw [decide_eq_false hlnn]
    wp_auto
    wp_apply hIB pa hd dq $$ [Hh] as Hh
    · iexact Hh
    have hra : refAt X bl pid ⟨pa, null, W64 0⟩ := refAt_page X bl B pid pg _ hB hres rfl hw
    rcases hkind with ⟨hlf, hlwf⟩ | ⟨hbr, hroot, hpgv, hbwf, htw, hnmf⟩
    · -- a leaf page
      have hf2 : hd.flags' = W16 2 := by
        apply BitVec.eq_of_toNat_eq; rw [← hfz, hlf]; rfl
      rw [hf2]
      wp_auto
      wp_apply hIL pa hd dq $$ [Hh] as Hh
      · iexact Hh
      rw [hf2]
      wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_apply wp_slice_append $$ [$Hs $Hcap $Hsl] as %s1 ⟨Hs, Hcap, -⟩
      try wp_auto
      wp_method_call; wp_call
      wp_auto
      wp_apply hIL pa hd dq $$ [Hh] as Hh
      · iexact Hh
      rw [hf2]
      wp_auto
      ihave Hp := Hhb $$ Hh
      wp_apply hnp c bl s1 els ⟨pa, null, W64 0⟩ dq pg key dk kb rfl hlf hlwf
        $$ [Hc Hs Hp Hk] as ⟨Hc, Hs, Hp, Hk⟩
      · iframe
      ihave Hcells := Hpb $$ Hp Hk
      ihave Hw := Hwb $$ Hcells
      try wp_auto
      iapply HΦ $$ %s1 %([⟨pa, null, W64 (pageSeekIdx pg kb : Int)⟩] : List elemRef) %([pid] : List w64)
      iframe
      ipureintro
      have hlt : ltree X bl pid = some (true, pageWs pg) := by
        rw [ltree_page X bl B pid pa pg hB hres hw, hlf]; rfl
      have hix := pageSeekIdx_le pg kb
      refine ⟨lPathFrom_leaf X bl pid _ (pageWs pg) (refAt_page X bl B pid pg _ hB hres rfl hw) hlt,
        lRoutes_leaf X bl pid _ (pageWs pg) kb hlt ?_⟩
      show (W64 (pageSeekIdx pg kb : Int)).toNat = wsIdx (pageWs pg) kb
      rw [← pageSeekIdx_wsIdx pg kb hlf]
      simp; omega
    · -- a branch page: `searchPage`, inlined
      have hf1 : hd.flags' = W16 1 := by
        apply BitVec.eq_of_toNat_eq; rw [← hfz, hbr]; rfl
      rw [hf1]
      wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_apply wp_slice_append $$ [$Hs $Hcap $Hsl] as %s1 ⟨Hs, Hcap, -⟩
      try wp_auto
      wp_method_call; wp_call
      wp_auto
      wp_apply hIL pa hd dq $$ [Hh] as Hh
      · iexact Hh
      rw [show decide (hd.flags' = W16 2) = false by rw [hf1]; decide]
      wp_auto
      wp_method_call; wp_call
      wp_auto
      obtain ⟨hc0, -, hcnt, helems, hsorted⟩ := hbwf
      have hcz : uint.Z hd.count' = (pageCount pg : Int) := by unfold pageCount; rw [hH]
      have hcnt16 : pageCount pg < 2 ^ 16 := by unfold pageCount; exact BitVec.isLt _
      wp_apply hBE pa hd dq Hlb.1 (by unfold elemOff at hcnt; rw [hcz]; omega) $$ [Hh] as Hh
      · iexact Hh
      have hcnz : hd.count' ≠ W16 0 := by
        intro h
        have : (pageCount pg : Int) = 0 := by rw [← hcz, h]; rfl
        omega
      rw [if_neg hcnz]
      wp_apply hCnt pa hd dq $$ [Hh] as Hh
      · iexact Hh
      ihave Hp := Hhb $$ Hh
      have hn' : sint.Z (W64 (uint.Z hd.count')) = (pageCount pg : Int) := by rw [hcz]; word
      wp_apply hS (W64 (uint.Z hd.count')) _ (spPred pg kb)
        (fun L => iprop(key_ptr ↦ key ∗
          inodes_ptr ↦ slice.mk (pa +ₗ 16) (W64 (uint.Z hd.count')) (W64 (uint.Z hd.count')) ∗
          exact_ptr ↦ spExact pg kb L ∗ bytesPointsto pa dq pg ∗ key ↦*{dk} kb ∗
          ⌜∀ j ∈ L, 0 ≤ j ∧ j < (pageCount pg : Int)⌝))
        $$ [key inodes exact Hp Hk]
      · iframe
        isplitl []
        · ipureintro; word
        isplitl []
        · unfold Read.predImplementsL
          iintro %L %i
          wp_start as ⟨⟨Hkp, Hin, Hex, Hp, Hk, %HL⟩, %Hbi⟩
          rw [hn'] at Hbi
          wp_auto
          rw [if_pos ⟨Hbi.1, by rw [hn']; exact Hbi.2⟩]
          obtain ⟨k, hk⟩ : ∃ k : Nat, sint.Z i = (k : Int) := ⟨(sint.Z i).toNat, by omega⟩
          have hkc : k < pageCount pg := by omega
          have hloc : sliceIndexRef branchPageElement (sint.Z i)
              (slice.mk (pa +ₗ 16) (W64 (uint.Z hd.count')) (W64 (uint.Z hd.count'))) =
              pa +ₗ ((elemOff k : Nat) : Int) := by
            rw [sliceIndexRef_plain branchPageElement.ty branchPageElement.layout _ i
              (by simp [Loc.add]; omega) Hbi.1]
            simp only [sint.nat, hk, Int.toNat_natCast, loc_add_assoc, elemOff]
            congr 1; push_cast; omega
          rw [hloc]
          obtain ⟨he1, he2, -⟩ := helems k hkc
          icases bytesPointsto_view_read (V := branchPageElement) pa dq pg (elemOff k)
            (pa +ₗ ((elemOff k : Nat) : Int)) rfl (by unfold elemOff at hcnt ⊢; omega) Hlb.1
            $$ Hp with ⟨Hel, Helb⟩
          rw [show (decode (List.take 16 (List.drop (elemOff k) pg)) : branchPageElement) =
            branchElem pg k from rfl]
          obtain ⟨be, hbe⟩ : ∃ be, branchElem pg k = be := ⟨_, rfl⟩
          have hpos : uint.Z be.pos' = (branchPos pg k : Int) := by unfold branchPos; rw [hbe]
          have hks' : uint.Z be.ksize' = (branchKsize pg k : Int) := by unfold branchKsize; rw [hbe]
          rw [hbe]
          wp_apply hBK (pa +ₗ ((elemOff k : Nat) : Int)) be dq (by simp [Loc.add]; omega)
            (by simp only [Loc.add]; rw [hpos, hks']; omega) $$ [Hel] as Hel
          · iexact Hel
          ihave Hp := Helb $$ Hel
          have hkl : (branchKey pg k).length = branchKsize pg k := by
            unfold branchKey bytesAt; simp only [List.length_take, List.length_drop]; omega
          icases Read.bytesPointsto_sub_acc pa dq pg (branchKey pg k) (elemOff k + branchPos pg k)
            (by rw [hkl]; omega) (by rw [hkl]; rfl) $$ Hp with ⟨Hkb, Hpb2⟩
          have hkloc : (pa +ₗ ((elemOff k : Nat) : Int)) +ₗ uint.Z be.pos' =
              pa +ₗ ((elemOff k + branchPos pg k : Nat) : Int) := by
            rw [loc_add_assoc, hpos]; push_cast; rfl
          have hksz : W64 (uint.Z be.ksize') = W64 ((branchKey pg k).length : Int) := by
            rw [hks', hkl]
          rw [hkloc, hksz]
          icases (Read.bytesPointsto_ownSlice (pa +ₗ ((elemOff k + branchPos pg k : Nat) : Int)) dq
            (branchKey pg k) (by simp [Loc.add]; omega)
            (by rw [hkl]; unfold maxAllocSize at he2; omega)).1 $$ Hkb with Hkb
          wp_apply hC $$ [Hkb Hk] as ⟨Hkb, Hk⟩
          · iframe
          icases (Read.bytesPointsto_ownSlice (pa +ₗ ((elemOff k + branchPos pg k : Nat) : Int)) dq
            (branchKey pg k) (by simp [Loc.add]; omega)
            (by rw [hkl]; unfold maxAllocSize at he2; omega)).2 $$ Hkb with Hkb
          ihave Hp := Hpb2 $$ Hkb
          have hcr0 : bytes.compareResult (branchKey pg k) kb = W64 0 ↔ branchKey pg k = kb := by
            unfold bytes.compareResult
            constructor
            · intro h; split at h
              · cases h
              · split at h
                · assumption
                · cases h
            · intro h; subst h; simp [go.goStringLt_irrefl]
          have hcrm : bytes.compareResult (branchKey pg k) kb = W64 (-1) ↔
              go.GoStringLt (branchKey pg k) kb := by
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
            · have : spExact pg kb (sint.Z i :: L) = true := by
                unfold spExact; simp only [decide_eq_true_eq]
                exact ⟨sint.Z i, List.mem_cons_self .., by rw [hk]; simpa using hcr0.1 Hif⟩
              rw [this]; iframe
              ipureintro; intro j hj
              rcases List.mem_cons.mp hj with rfl | hj
              · omega
              · exact HL j hj
            ipureintro
            unfold spPred
            rw [hk]; simp only [Int.toNat_natCast]
            by_cases hlt : go.GoStringLt (branchKey pg k) kb
            · exact absurd (hcr0.1 Hif ▸ hlt) (go.goStringLt_irrefl _)
            · simp [hlt, show ¬ bytes.compareResult (branchKey pg k) kb = W64 (-1) from fun h => hlt (hcrm.1 h)]
          · try wp_auto
            iapply HΦ
            iframe
            isplitl
            · have : spExact pg kb (sint.Z i :: L) = spExact pg kb L := by
                unfold spExact
                congr 1
                apply propext
                constructor
                · rintro ⟨j, hj, hjk⟩
                  rcases List.mem_cons.mp hj with rfl | hj
                  · exfalso; apply Hif; apply hcr0.2; rw [hk] at hjk; simpa using hjk
                  · exact ⟨j, hj, hjk⟩
                · rintro ⟨j, hj, hjk⟩; exact ⟨j, List.mem_cons_of_mem _ hj, hjk⟩
              rw [this]; iframe
              ipureintro; intro j hj
              rcases List.mem_cons.mp hj with rfl | hj
              · omega
              · exact HL j hj
            ipureintro
            unfold spPred
            rw [hk]; simp only [Int.toNat_natCast]
            by_cases hlt : go.GoStringLt (branchKey pg k) kb
            · simp [hlt, hcrm.2 hlt]
            · simp [hlt, show ¬ bytes.compareResult (branchKey pg k) kb = W64 (-1) from fun h => hlt (hcrm.1 h)]
        isplitl []
        · ipureintro; simp
        ipureintro; rw [hn']
        intro x y hxy hx
        obtain ⟨h0, hxy, hyn⟩ := hxy
        simp only [spPred, decide_eq_true_eq] at hx ⊢
        intro hy
        apply hx
        exact go.goStringLt_trans (hsorted x.toNat y.toNat (by omega) (by omega)) hy
      iintro %idx ⟨%L, ⟨Hkp, Hin, Hex, Hp, Hk, %HL⟩, %H0, %Hfound, %Hoob, %Hgt, %Hev⟩
      rw [hn'] at Hfound Hoob Hev
      have hR := sp_route pg kb L (sint.Z idx) hc0 hsorted H0 Hfound Hoob Hgt Hev HL
      wp_auto
      wp_join iprop(∃ ri : w64, index_ptr ↦ ri ∗
          ⌜sint.Z ri = (if spExact pg kb L = true then sint.Z idx
            else if 0 < sint.Z idx then sint.Z idx - 1 else sint.Z idx)⌝)
        at next with [index] as ⟨%ri, index, %Hri⟩
      · cases hex : spExact pg kb L
        · wp_auto
          wp_if_destruct
          · wp_join_done
            iexists _; iframe; ipureintro
            rw [if_pos (by word)]; word
          · wp_join_done
            iexists _; iframe; ipureintro
            rw [if_neg (by word)]
        · wp_auto
          wp_join_done
          iexists _; iframe; ipureintro; simp
      rw [← Hri] at hR
      obtain ⟨hR1, hR2, hR3⟩ := hR
      ihave %Hsl := ownSlice_len _ _ _ $$ Hs
      have hsidx : sint.Z (s1.len - W64 1) = (els.length : Int) := by
        simp only [List.length_append, List.length_singleton] at Hsl; word
      rw [if_pos (show 0 ≤ sint.Z (s1.len - W64 1) ∧ sint.Z (s1.len - W64 1) < sint.Z s1.len by
        rw [hsidx]; word)]
      icases ownSlice_elem_acc (sint.Z (s1.len - W64 1)) (⟨pa, null, W64 0⟩ : elemRef) _ _
        (els ++ [⟨pa, null, W64 0⟩]) (by omega) (by rw [hsidx]; simp) $$ Hs with ⟨He, Hsback⟩
      rw [hsidx]
      wp_auto
      ihave Hs := Hsback $$ He
      simp only [show ∀ (a x : elemRef), (els ++ [a]).set (↑els.length : Int).toNat x = els ++ [x]
        from fun a x => by simp]
      obtain ⟨k, hk⟩ : ∃ k : Nat, sint.Z ri = (k : Int) := ⟨(sint.Z ri).toNat, by omega⟩
      have hkc : k < pageCount pg := by omega
      rw [if_pos ⟨hR2, by rw [hn']; exact hR3⟩]
      have hloc2 : sliceIndexRef branchPageElement (sint.Z ri)
          (slice.mk (pa +ₗ 16) (W64 (uint.Z hd.count')) (W64 (uint.Z hd.count'))) =
          pa +ₗ ((elemOff k : Nat) : Int) := by
        rw [sliceIndexRef_plain branchPageElement.ty branchPageElement.layout _ ri
          (by simp [Loc.add]; omega) hR2]
        simp only [sint.nat, hk, Int.toNat_natCast, loc_add_assoc, elemOff]
        congr 1; push_cast; omega
      rw [hloc2]
      icases bytesPointsto_view_read (V := branchPageElement) pa dq pg (elemOff k)
        (pa +ₗ ((elemOff k : Nat) : Int)) rfl (by unfold elemOff at hcnt ⊢; omega) Hlb.1
        $$ Hp with ⟨Hel, Helb⟩
      rw [show (decode (List.take 16 (List.drop (elemOff k) pg)) : branchPageElement) =
        branchElem pg k from rfl]
      obtain ⟨be2, hbe2⟩ : ∃ be, branchElem pg k = be := ⟨_, rfl⟩
      rw [hbe2]
      wp_apply hBP (pa +ₗ ((elemOff k : Nat) : Int)) be2 dq $$ [Hel] as Hel
      · iexact Hel
      ihave Hp := Helb $$ Hel
      ihave Hcells := Hpb $$ Hp Hk
      ihave Hw := Hwb $$ Hcells
      have hchild : be2.pgid'.toNat = branchPgid pg k := by unfold branchPgid; rw [hbe2]
      have hpw : be2.pgid' = (pageW pg k).pgid := by
        rw [(pageW_branch pg k hbr).2, ← hchild, Write.w64_ofNat_toNat]
      rw [hpw]
      have Hch' : X.t.bs !! bl = some B ∧ bktLocalOK X bl ∧ pmFresh X ∧ inlSrcOK X bl ∧
          ks ≠ Src.stale ∧ posOK X bl B (pageW pg k).pgid ∧
          (B.ib.root' = W64 0 → (pageW pg k).pgid = W64 0) :=
        ⟨hB, hloc, hpm, hinl, hks, by
          rw [(pageW_branch pg k hbr).2]
          exact posOK_page_child X bl B pid pg k hroot htw hnmf hpgv hbr hkc,
          fun h => absurd h hroot⟩
      wp_apply IH $$ %K %tx %r %m %X %bl %B %c %s1 %(els ++ [⟨pa, null, ri⟩]) %(pageW pg k).pgid
        %key %ks %kb %Hch' [Hw Hc Hs Hcap] as %stk'' %path' %pids' ⟨Hw, Hc, Hs, Hcap, %Hrt⟩
      · iframe; iframe #
      iapply HΦ $$ %stk'' %((⟨pa, null, ri⟩ : elemRef) :: path') %(pid :: pids')
      rw [List.append_assoc]
      iframe
      ipureintro
      have hri : ri.toNat = k := by word
      have hlt : ltree X bl pid = some (false, pageWs pg) := by
        rw [ltree_page X bl B pid pa pg hB hres hw, hbr]; rfl
      refine ⟨lPathFrom_cons X bl pid ⟨pa, null, ri⟩ (pageWs pg) (pageW pg k) path' pids'
          (refAt_page X bl B pid pg _ hB hres rfl hw) hlt
          (by show (pageWs pg)[ri.toNat]? = _; rw [hri]; exact pageWs_get pg k hkc) Hrt.1,
        lRoutes_cons X bl pid ⟨pa, null, ri⟩ (pageWs pg) path' pids' kb hlt ?_ Hrt.2⟩
      show ri.toNat < _ ∧ _
      have hsk : (sint.Z ri).toNat = k := by omega
      rw [hri]; rw [hsk] at hR1
      exact branchRoute_lroute pg kb k hbr hR1

end proof

section proof'
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem Cursor.search_w.wp_proof
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
    Cursor.search_w.spec (GF := GF) (hG := hG) := by
  intro K tx r m X bl B c stk els pid key ks kb hB hloc hpm hinl hks hpos hpid0
  iintro %Φ Hpre HΦ
  have hP : X.t.bs !! bl = some B ∧ bktLocalOK X bl ∧ pmFresh X ∧ inlSrcOK X bl ∧
      ks ≠ Src.stale ∧ posOK X bl B pid ∧ (B.ib.root' = W64 0 → pid = W64 0) :=
    ⟨hB, hloc, hpm, hinl, hks, hpos, hpid0⟩
  iapply (Cursor.search_w.wp_aux hpn hnp hnn hIL hIB hBE hCnt hBK hBP hIK hIP hS hC) $$ %K %tx %r %m
    %X %bl %B %c %stk %els %pid %key %ks %kb %hP Hpre
  inext
  iintro %stk' %path %pids H
  iapply HΦ
  iexists stk', path, pids
  iexact H

end proof'

end bbolt
end EtcdGrove
end Perennial
