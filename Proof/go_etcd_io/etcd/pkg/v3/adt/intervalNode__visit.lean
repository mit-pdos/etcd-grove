module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalNode__visit
public import Spec.go_etcd_io.etcd.pkg.v3.adt.Interval__Compare

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3.adt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

theorem adt.intervalNode.visit.wp_proof
    (h_Interval_Compare : adt.Interval.Compare.spec (GF := GF) (hG := hG)) :
    adt.intervalNode.visit.spec (GF := GF) (hG := hG) := by
  intro s q p x Tx ivp dq b e nv S I acc hs hq hS
  induction Tx generalizing p x acc with
  | leaf =>
    wp_start as ⟨Hx, Hiv, #Hnv, HI⟩
    icases adt.ownNode_leaf_open _ _ _ _ $$ Hx with %Hx
    subst Hx
    wp_auto
    iapply HΦ
    iexists []
    simp only [List.zip_nil_left, List.append_nil]
    iframe
    rw [adt.ownNodeH_leaf]
    ipureintro; exact ⟨rfl, rfl⟩
  | node c l z r ihl ihr =>
    wp_start as ⟨Hx, Hivp, #Hnv, HI⟩
    icases adt.ownNode_node_open _ _ _ _ c l z r $$ Hx with
      ⟨%lp, %rp, %Hn, Hiv, Hmx, Hl, Hr', Hp, Hc', Hnl, Hnr⟩
    wp_auto
    wp_if_destruct
    · exfalso; first | exact Hn.1 ‹_› | exact Hn.1 rfl
    icases adt.iv_open_ivl _ _ _ _ _ $$ Hiv with ⟨Hivl, Hivb⟩
    wp_apply h_Interval_Compare ivp dq b e _ (DFrac.own q) z.1.1 z.1.2
      $$ [$Hivl $Hivp] as ⟨Hivp, Hivl⟩
    ihave Hiv := Hivb $$ Hivl
    have hz : ∀ v : Int, -1 ≤ v → v ≤ 1 → sint.Z (W64 v) = v := by
      intro v h1 h2; word
    have hvb : -1 ≤ adt.ivlCmp (b, e) z.1 ∧ adt.ivlCmp (b, e) z.1 ≤ 1 := by
      unfold adt.ivlCmp; split <;> (try split) <;> simp
    have h0 : sint.Z (W64 0) = 0 := rfl
    simp only [Prod.eta]
    rw [hz _ hvb.1 hvb.2, h0]
    obtain ⟨hsl, hsr, -, -⟩ := adt.ivSorted_node hs
    have hvis := adt.visit_stab (b, e) hq (.node c l z r) hs
    rw [adt.stab_node] at hvis
    have hvl := adt.visit_stab (b, e) hq l hsl
    have hvr := adt.visit_stab (b, e) hq r hsr
    unfold adt.RbT.visitL at hvis
    rw [hvl, hvr] at hvis
    have hS' := hS
    rw [adt.stab_node] at hS'
    have hSl : acc.map Prod.snd ++ adt.stab (b, e) l.inorder <+: S :=
      (List.prefix_append _ _).trans (by simpa only [List.append_assoc] using hS')
    by_cases hneg : adt.ivlCmp (b, e) z.1 < 0
    · -- left only
      have hne : ¬ adt.ivlCmp (b, e) z.1 = 0 := by omega
      simp only [hneg, ↓reduceIte, hne] at hvis
      have hr0 : adt.stab (b, e) r.inorder = [] := by simpa using hvis
      wp_if_destruct
      · wp_apply (ihl x lp acc hsl hSl) $$ [$Hnl $Hivp $HI $Hnv] as ⟨%nsl, Hnl, Hivp, HI⟩
        iapply HΦ
        iexists nsl
        rw [adt.stab_node, hr0]
        simp only [hne, ↓reduceIte, List.append_nil]
        iframe Hivp HI
        rw [adt.ownNodeH_node]
        icases adt.ownNode_holes_nil s q (b, e) x rp r hr0 $$ Hnr with Hnr
        iexists lp, rp, nsl, []
        simp only [hne, ↓reduceIte, List.append_nil]
        iframe
        ipureintro; exact ⟨Hn.1, Hn.2, trivial⟩
      · exfalso; exact Hif (by simp [hneg])
    simp only [hneg, ↓reduceIte] at hvis
    wp_if_destruct
    · exfalso; apply hneg; simpa using Hif
    by_cases hpos : adt.ivlCmp (b, e) z.1 > 0
    · have hne : ¬ adt.ivlCmp (b, e) z.1 = 0 := by omega
      simp only [hpos, ↓reduceIte] at hvis
      icases adt.iv_open _ _ _ _ _ $$ Hiv with ⟨Hb, He, Hv, Hivb⟩
      wp_if_destruct
      · rename_i maxiv_ptr
        wp_apply h_Interval_Compare maxiv_ptr (DFrac.own 1) z.1.1 (adt.nodeMax l z r) ivp dq b e
          $$ [maxiv $Hivp] as ⟨maxiv, Hivp⟩
        · unfold adt.affIvl adt.maxW; iexact maxiv
        ihave Hiv := Hivb $$ [Hb He Hv]
        · iframe
        have hmb : -1 ≤ adt.ivlCmp (z.1.1, adt.nodeMax l z r) (b, e) ∧
            adt.ivlCmp (z.1.1, adt.nodeMax l z r) (b, e) ≤ 1 := by
          unfold adt.ivlCmp; split <;> (try split) <;> simp
        have hmw : W64 (adt.ivlCmp (z.1.1, adt.nodeMax l z r) (b, e)) = W64 0 ↔
            adt.ivlCmp (z.1.1, adt.nodeMax l z r) (b, e) = 0 := by
          constructor <;> intro h <;> word
        simp only [hne, ↓reduceIte, List.append_nil] at hvis
        wp_if_destruct
        · -- both subtrees
          have hm := hmw.1 Hif
          wp_apply (ihl x lp acc hsl hSl) $$ [$Hnl $Hivp $HI $Hnv] as ⟨%nsl, Hnl, Hivp, HI⟩
          ihave %hl1 := adt.ownNodeH_length _ _ _ _ _ _ _ $$ Hnl
          have hSr : (acc ++ nsl.zip (adt.stab (b, e) l.inorder)).map Prod.snd ++
              adt.stab (b, e) r.inorder <+: S := by
            rw [List.map_append, List.map_snd_zip (by omega)]
            simpa only [hne, ↓reduceIte, List.append_nil, List.append_assoc] using hS'
          wp_apply (ihr x rp _ hsr hSr) $$ [$Hnr $Hivp $HI $Hnv] as ⟨%nsr, Hnr, Hivp, HI⟩
          iapply HΦ
          iexists nsl ++ nsr
          rw [adt.stab_node]
          simp only [hne, ↓reduceIte, List.append_nil, List.append_assoc]
          rw [List.zip_append hl1]
          iframe Hivp HI
          rw [adt.ownNodeH_node]
          iexists lp, rp, nsl, nsr
          simp only [hne, ↓reduceIte, List.append_nil]
          iframe
          ipureintro; exact ⟨Hn.1, Hn.2, trivial⟩
        · -- neither
          have hm : ¬ adt.ivlCmp (z.1.1, adt.nodeMax l z r) (b, e) = 0 :=
            fun h => Hif (hmw.2 h)
          simp only [hm, ↓reduceIte] at hvis
          have hl0 : adt.stab (b, e) l.inorder = [] := by
            simpa using (List.append_eq_nil_iff.1 hvis.symm).1
          have hr0 : adt.stab (b, e) r.inorder = [] := by
            simpa using (List.append_eq_nil_iff.1 hvis.symm).2
          iapply HΦ
          iexists []
          rw [adt.stab_node, hl0, hr0]
          simp only [hne, ↓reduceIte, List.append_nil, List.zip_nil_left]
          iframe Hivp HI
          rw [adt.ownNodeH_node]
          icases adt.ownNode_holes_nil s q (b, e) x lp l hl0 $$ Hnl with Hnl
          icases adt.ownNode_holes_nil s q (b, e) x rp r hr0 $$ Hnr with Hnr
          iexists lp, rp, [], []
          simp only [hne, ↓reduceIte, List.append_nil]
          iframe
          ipureintro; exact ⟨Hn.1, Hn.2, trivial⟩
      · exfalso; apply Hif; simp [hz _ hvb.1 hvb.2, h0, hpos]
    have hz0 : adt.ivlCmp (b, e) z.1 = 0 := by omega
    wp_if_destruct
    · exfalso; apply hpos; simpa [hz _ hvb.1 hvb.2, h0] using Hif
    wp_apply (ihl x lp acc hsl hSl) $$ [$Hnl $Hivp $HI $Hnv] as ⟨%nsl, Hnl, Hivp, HI⟩
    ihave %hl1 := adt.ownNodeH_length _ _ _ _ _ _ _ $$ Hnl
    have hSz : (acc ++ nsl.zip (adt.stab (b, e) l.inorder)).map Prod.snd ++ [z] <+: S := by
      rw [List.map_append, List.map_snd_zip (by omega)]
      exact (List.prefix_append _ _).trans
        (by simpa only [hz0, ↓reduceIte, List.append_assoc, List.singleton_append] using hS')
    have hSr : ((acc ++ nsl.zip (adt.stab (b, e) l.inorder)) ++ [(x, z)]).map Prod.snd ++
        adt.stab (b, e) r.inorder <+: S := by
      rw [List.map_append, List.map_append, List.map_snd_zip (by omega)]
      simpa only [hz0, ↓reduceIte, List.append_assoc, List.map_cons, List.map_nil,
        List.singleton_append, List.cons_append, List.nil_append] using hS'
    ihave Hnv' := Hnv
    iunfold adt.nodeVisitorOk at Hnv'
    wp_apply Hnv' $$ %x %z %(acc ++ nsl.zip (adt.stab (b, e) l.inorder)) [HI Hiv] as HI
    · iframe
      ipureintro; exact hSz
    wp_apply (ihr x rp _ hsr hSr) $$ [$Hnr $Hivp $HI $Hnv] as ⟨%nsr, Hnr, Hivp, HI⟩
    iapply HΦ
    iexists nsl ++ [x] ++ nsr
    rw [adt.stab_node]
    simp only [hz0, ↓reduceIte, List.append_assoc, List.cons_append, List.nil_append]
    rw [List.zip_append hl1]
    simp only [List.zip_cons_cons, List.append_assoc, List.cons_append, List.nil_append]
    iframe Hivp HI
    rw [adt.ownNodeH_node]
    iexists lp, rp, nsl, nsr
    simp only [hz0, ↓reduceIte]
    iframe
    ipureintro; exact ⟨Hn.1, Hn.2, by simp⟩

end proof

end EtcdGrove
end Perennial
