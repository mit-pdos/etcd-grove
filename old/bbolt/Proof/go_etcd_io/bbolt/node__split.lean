module
public import Spec.go_etcd_io.bbolt.node__split

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax] [go_gctx : GoGlobalContext] [GoSemanticsFunctions]

/-- The loop of `n.split` after a split: the parts made `ys`, the node `c` being split (struct
`cv`, inodes `cins`), under the parent `pl` (struct `pv'`, children `pcs'`). -/
def splitB (nl : Loc) (nv pv : node) (pcs : List Loc) (ins : List Inode)
    (ys : List (Loc × node × List Inode)) (c : Loc) (cv : node) (cins : List Inode) (pl : Loc)
    (pv' : node) (pcs' : List Loc) : Prop :=
  ys ≠ [] ∧ splitPieces nl nv pl ins (ys ++ [(c, cv, cins)]) ∧ cv.parent' = pl ∧ pl ≠ null ∧
  ((nv.parent' = null ∧ pv' = newParent nv pv'.children' ∧
      pcs' = (ys ++ [(c, cv, cins)]).map (fun x => x.1)) ∨
   (nv.parent' ≠ null ∧ pl = nv.parent' ∧ pv' = { pv with children' := pv'.children' } ∧
      pcs' = pcs ++ ((ys ++ [(c, cv, cins)]).drop 1).map (fun x => x.1)))

theorem splitB_cur (nl : Loc) (nv pv : node) (pcs : List Loc) (ins : List Inode)
    (ys : List (Loc × node × List Inode)) (c : Loc) (cv : node) (cins : List Inode) (pl : Loc)
    (pv' : node) (pcs' : List Loc) (h : splitB nl nv pv pcs ins ys c cv cins pl pv' pcs') :
    c ≠ null ∧
      cv = ({ zero_val node with bucket' := nv.bucket', isLeaf' := nv.isLeaf', parent' := pl, inodes' := cv.inodes' } : node) := by
  obtain ⟨hne, ⟨-, ⟨x0, rest, hxs, -, -, hrest⟩, -⟩, -⟩ := h
  obtain ⟨y0, ys', rfl⟩ := List.exists_cons_of_ne_nil hne
  simp only [List.cons_append, List.cons.injEq] at hxs
  obtain ⟨-, rfl⟩ := hxs
  exact hrest (c, cv, cins) (by simp)

theorem splitB_first (nl nx : Loc) (nv pv : node) (pcs : List Loc) (ins : List Inode) (k : Nat)
    (pl : Loc) (pv' : node) (pcs' : List Loc) (hk : 2 ≤ k) (hk3 : k + 3 ≤ ins.length)
    (hnx : nx ≠ null) (hpl : pl ≠ null) (hsp : splitParent nl nx nv pv pcs pl pv' pcs') :
    splitB nl nv pv pcs ins [(nl, splitLeft nv pl k, ins.take k)] nx (splitRight nv pl k)
      (ins.drop k) pl pv' pcs' := by
  refine ⟨by simp, ⟨?_, ⟨_, _, rfl, rfl, rfl, ?_⟩, ?_⟩, rfl, hpl, ?_⟩
  · simp
  · intro x hx
    obtain rfl : x = (nx, splitRight nv pl k, ins.drop k) := by simpa using hx
    exact ⟨hnx, rfl⟩
  · intro _ x hx
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, _root_.or_false] at hx
    rcases hx with rfl | rfl
    · simp only [List.length_take]; omega
    · simp only [List.length_drop]; omega
  · rcases hsp with ⟨hp, hpv, hpc⟩ | ⟨hp, hpl', hpv, hpc⟩
    · exact Or.inl ⟨hp, hpv, by rw [hpc]; rfl⟩
    · exact Or.inr ⟨hp, hpl', hpv, by rw [hpc]; rfl⟩

theorem splitB_step (nl : Loc) (nv pv : node) (pcs : List Loc) (ins : List Inode)
    (ys : List (Loc × node × List Inode)) (c : Loc) (cv : node) (cins : List Inode) (pl : Loc)
    (pv' : node) (pcs' : List Loc) (h : splitB nl nv pv pcs ins ys c cv cins pl pv' pcs')
    (k : Nat) (nx : Loc) (pv'' : node) (pcs'' : List Loc) (hk : 2 ≤ k) (hk3 : k + 3 ≤ cins.length)
    (hnx : nx ≠ null) (hsp : splitParent c nx cv pv' pcs' pl pv'' pcs'') :
    splitB nl nv pv pcs ins (ys ++ [(c, splitLeft cv pl k, cins.take k)]) nx
      (splitRight cv pl k) (cins.drop k) pl pv'' pcs'' := by
  have hcur := splitB_cur nl nv pv pcs ins ys c cv cins pl pv' pcs' h
  obtain ⟨hne, ⟨hfl, ⟨x0, rest, hxs, hx0, hx0v, hrest⟩, hlen⟩, hcp, hpl, hrel⟩ := h
  obtain ⟨y0, ys', rfl⟩ := List.exists_cons_of_ne_nil hne
  simp only [List.cons_append, List.cons.injEq] at hxs
  obtain ⟨rfl, rfl⟩ := hxs
  have hsp' : pv'' = { pv' with children' := pv''.children' } ∧ pcs'' = pcs' ++ [nx] := by
    rcases hsp with ⟨hp, -, -⟩ | ⟨-, -, hpv, hpc⟩
    · exact absurd hcp (by rw [hp]; exact Ne.symm hpl)
    · exact ⟨hpv, hpc⟩
  obtain ⟨hpv, hpc⟩ := hsp'
  refine ⟨by simp, ⟨?_, ⟨y0, ys' ++ [(c, splitLeft cv pl k, cins.take k)] ++
    [(nx, splitRight cv pl k, cins.drop k)], by simp, hx0, hx0v, ?_⟩, ?_⟩, rfl, hpl, ?_⟩
  · simp only [List.cons_append, List.map_cons, List.flatten_cons, List.map_append,
      List.flatten_append, List.map_nil, List.flatten_nil, List.append_nil] at hfl ⊢
    rw [← hfl]
    simp [List.append_assoc]
  · intro x hx
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, _root_.or_false] at hx
    rcases hx with (hx | rfl) | rfl
    · exact hrest x (by simp [hx])
    · refine ⟨hcur.1, ?_⟩
      rw [hcur.2]; rfl
    · refine ⟨hnx, ?_⟩
      unfold splitRight
      rw [hcur.2]
  · intro _ x hx
    have hold := hlen (by simp)
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_nil_iff, _root_.or_false]
      at hx hold
    rcases hx with rfl | (hx | rfl) | rfl
    · exact hold _ (Or.inl rfl)
    · exact hold _ (Or.inr (Or.inl hx))
    · simp only [List.length_take]; omega
    · simp only [List.length_drop]; omega
  · rcases hrel with ⟨hp, hpv0, hpc0⟩ | ⟨hp, hpl', hpv0, hpc0⟩
    · refine Or.inl ⟨hp, ?_, ?_⟩
      · rw [hpv, hpv0]; rfl
      · rw [hpc, hpc0]; simp
    · refine Or.inr ⟨hp, hpl', ?_, ?_⟩
      · rw [hpv, hpv0]
      · rw [hpc, hpc0]; simp

theorem split_stats (st : TxStats) (n : Nat) :
    ({ ({ st with Split' := st.Split' + W64 (n : Int) } : TxStats) with
        Split' := ({ st with Split' := st.Split' + W64 (n : Int) } : TxStats).Split' + W64 1 } : TxStats) =
      { st with Split' := st.Split' + W64 ((n + 1 : Nat) : Int) } := by
  simp only
  congr 1
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp
  omega

end pure

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem node.split.wp_proof (hST : node.splitTwo.spec (GF := GF) (hG := hG)) :
    node.split.spec (GF := GF) (hG := hG) := by
  intro nl nv ins bv dqb st pv pcs ps
  wp_start as ⟨Hn, Hins, Hcap, Hb, Hst, Hpar⟩
  wp_auto
  ihave IH : iprop(∃ (c : Loc) (s : GoSlice) (ys : List (Loc × node × List Inode)),
      "node" ∷ node_ptr ↦ c ∗ "nodes" ∷ nodes_ptr ↦ s ∗ "pageSize" ∷ pageSize_ptr ↦ ps ∗
      "Hs" ∷ s ↦* ys.map (fun x => x.1) ∗ "Hscap" ∷ ownSliceCap Loc s (DFrac.own 1) ∗
      "Hb" ∷ nv.bucket' ↦{dqb} bv ∗
      "Hph" ∷ ((⌜ys = [] ∧ c = nl⌝ ∗ nl ↦ nv ∗ nv.inodes' ↦* ins ∗
          ownSliceCap Inode nv.inodes' (DFrac.own 1) ∗ structFieldRef Tx go!"stats" bv.tx' ↦ st ∗
          parentOwn nv.parent' pv pcs) ∨
        (∃ (cv : node) (cins : List Inode) (pl : Loc) (pv' : node) (pcs' : List Loc),
          ⌜splitB nl nv pv pcs ins ys c cv cins pl pv' pcs'⌝ ∗ c ↦ cv ∗ cv.inodes' ↦* cins ∗
          ownSliceCap Inode cv.inodes' (DFrac.own 1) ∗
          ([∗list] y ∈ ys, y.1 ↦ y.2.1 ∗ y.2.1.inodes' ↦* y.2.2) ∗
          pl ↦ pv' ∗ pv'.children' ↦* pcs' ∗ ownSliceCap Loc pv'.children' (DFrac.own 1) ∗
          structFieldRef Tx go!"stats" bv.tx' ↦
            ({ st with Split' := st.Split' + W64 (ys.length : Int) } : TxStats)))) $$
      [node nodes pageSize Hb Hn Hins Hcap Hst Hpar]
  · ihave Hnil := ownSlice_nil (V := Loc) (GF := GF) (DFrac.own 1)
    ihave Hnilc := ownSliceCap_nil (V := Loc) (GF := GF)
    iexists nl, slice.nil, []
    simp only [List.map_nil]
    iframe node nodes pageSize Hb
    isplitl [Hnil]
    · iexact Hnil
    isplitl [Hnilc]
    · iexact Hnilc
    ileft
    iframe
    ipureintro; simp
  wp_for IH
  try wp_auto
  icases Hph with (⟨%Hy, Hn, Hins, Hcap, Hst, Hpar⟩ | ⟨%cv, %cins, %pl, %pv', %pcs', %HB, Hc, Hcins,
    Hccap, Hys, Hpl, Hpcs, Hpcap, Hst⟩)
  · obtain ⟨rfl, Hc⟩ := Hy
    subst c
    wp_apply hST nl nv ins bv dqb st pv pcs ps $$ [Hn Hins Hcap Hb Hst Hpar] as %nx ⟨Hb, Hpost⟩
    · iframe
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_slice_append $$ [$Hs $Hscap $Hsl] as %s' ⟨Hs, Hscap, -⟩
    try wp_auto
    icases Hpost with (⟨%Hnx, Hn, Hins, Hcap, Hst, Hpar⟩ | ⟨%k, %pl, %pv', %pcs', %Hk, Hn, HL, Hnx,
      HR, HRcap, Hpl, Hpcs, Hpcap, Hst⟩)
    · subst Hnx
      try wp_auto
      wp_for_post
      try wp_auto
      ispecialize HΦ $$ %s' %([(nl, nv, ins)])
      iapply HΦ
      isimp only [List.map_nil, List.nil_append, List.map_cons] at Hs
      iframe
      ileft
      iframe
      ipureintro; rfl
    · obtain ⟨hk2, hk3, hnx, hpl, hsp⟩ := Hk
      rw [decide_eq_false hnx]
      try wp_auto
      wp_for_post
      iframe
      iexists nx, s', [(nl, splitLeft nv pl k, ins.take k)]
      isimp only [List.map_nil, List.nil_append, List.map_cons] at Hs
      iframe
      iright
      iexists (splitRight nv pl k), (ins.drop k), pl, pv', pcs'
      isplitr
      · ipureintro; exact splitB_first nl nx nv pv pcs ins k pl pv' pcs' hk2 hk3 hnx hpl hsp
      simp only [List.length_singleton, List.map_cons, List.map_nil]
      rw [show (splitRight nv pl k).inodes' = inodesR nv k from rfl]
      isplitl [Hnx]
      · iexact Hnx
      isplitl [HR]
      · iexact HR
      isplitl [HRcap]
      · iexact HRcap
      isplitl [Hn HL]
      · iapply BigSepL.bigSepL_singleton.2
        iframe
      iframe
  · have hcur := splitB_cur nl nv pv pcs ins ys c cv cins pl pv' pcs' HB
    have hb' : cv.bucket' = nv.bucket' := by rw [hcur.2]
    have hpar : cv.parent' = pl := HB.2.2.1
    have hpl : pl ≠ null := HB.2.2.2.1
    have hne : ys ≠ [] := HB.1
    wp_apply hST c cv cins bv dqb ({ st with Split' := st.Split' + W64 (ys.length : Int) } : TxStats)
      pv' pcs' ps $$ [Hc Hcins Hccap Hb Hst Hpl Hpcs Hpcap] as %nx ⟨Hb, Hpost⟩
    · rw [hb', hpar]
      unfold parentOwn
      rw [if_neg hpl]
      iframe
    isimp only [hb'] at Hb
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_slice_append $$ [$Hs $Hscap $Hsl] as %s' ⟨Hs, Hscap, -⟩
    try wp_auto
    icases Hpost with (⟨%Hnx, Hc, Hcins, Hccap, Hst, Hpar⟩ | ⟨%k, %pl2, %pv'', %pcs'', %Hk, Hc, HL,
      Hnx, HR, HRcap, Hpl, Hpcs, Hpcap, Hst⟩)
    · subst Hnx
      try wp_auto
      wp_for_post
      try wp_auto
      ispecialize HΦ $$ %s' %(ys ++ [(c, cv, cins)])
      iapply HΦ
      rw [hpar] at *
      unfold parentOwn
      rw [if_neg hpl]
      icases Hpar with ⟨Hpl, Hpcs, Hpcap⟩
      simp only [List.map_append, List.map_cons, List.map_nil, List.length_append,
        List.length_singleton, Nat.add_sub_cancel]
      iframe
      iright
      iexists pl, pv', pcs', (c, cv, cins)
      isplitr
      · ipureintro
        refine ⟨?_, HB.2.1, by simp, hpl, by simpa using HB.2.2.2.2⟩
        have : 0 < ys.length := by
          cases ys with
          | nil => exact absurd rfl hne
          | cons => simp
        simp; omega
      isplitl [Hys Hc Hcins]
      · iapply BigSepL.bigSepL_snoc.2
        iframe
      iframe
    · obtain ⟨hk2, hk3, hnx, hpl2, hsp⟩ := Hk
      have hpl2e : pl2 = pl := by
        rcases hsp with ⟨hp, -, -⟩ | ⟨-, hp, -, -⟩
        · exact absurd (hpar.symm.trans hp) hpl
        · rw [hp, hpar]
      subst hpl2e
      rw [decide_eq_false hnx]
      try wp_auto
      wp_for_post
      iframe
      iexists nx, s', ys ++ [(c, splitLeft cv pl2 k, cins.take k)]
      simp only [List.map_append, List.map_cons, List.map_nil, List.length_append,
        List.length_singleton]
      iframe
      iright
      iexists (splitRight cv pl2 k), (cins.drop k), pl2, pv'', pcs''
      isplitr
      · ipureintro
        exact splitB_step nl nv pv pcs ins ys c cv cins pl2 pv' pcs' HB k nx pv'' pcs'' hk2 hk3 hnx hsp
      rw [show (splitRight cv pl2 k).inodes' = inodesR cv k from rfl]
      isplitl [Hnx]
      · iexact Hnx
      isplitl [HR]
      · iexact HR
      isplitl [HRcap]
      · iexact HRcap
      isplitl [Hys Hc HL]
      · iapply BigSepL.bigSepL_snoc.2
        iframe
      rw [← split_stats]
      iframe

end proof

end bbolt
end EtcdGrove
end Perennial
