/-
`intervalNode.visit` (`interval_tree.go`), over a comparator, for a visitor that may stop and a
query that may be degenerate: the proof of `Spec/.../adt/intervalNode__visit.lean`. Lean-first
(no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalNode__visit
public import Spec.go_etcd_io.etcd.pkg.v3.adt.Interval__Compare

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3.adt

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

theorem adt.intervalNode.visit.wp_proof
    (h_Interval_Compare : adt.Interval.Compare.spec (GF := GF) (hG := hG)) :
    adt.intervalNode.visit.spec (GF := GF) (hG := hG) := by
  intro K hK s q p x Tx ivp dq vb ve db de b e nv S I J acc hS
  induction Tx generalizing p x acc with
  | leaf =>
    wp_start as ⟨Hx, Hivp, Hkb, Hke, #Hnv, HI⟩
    icases adt.ownNode_leaf_open K _ _ _ _ $$ Hx with %Hx
    subst Hx
    wp_auto
    iapply HΦ
    iframe Hivp Hkb Hke
    iexists [], []
    simp only [↓reduceIte]
    isplitl []
    · ipureintro; rfl
    rw [adt.ownNodeH_leaf]
    isplitl []
    · ipureintro; exact ⟨rfl, rfl, rfl⟩
    simp only [List.zip_nil_left, List.append_nil]
    iexact HI
  | node c l z r ihl ihr =>
    wp_start as ⟨Hx, Hivp, Hkb, Hke, #Hnv, HI⟩
    icases adt.ownNode_node_open K _ _ _ _ c l z r $$ Hx with
      ⟨%lp, %rp, %Hn, Hiv, Hmx, Hl, Hr', Hp, Hc', Hnl, Hnr⟩
    wp_auto
    wp_if_destruct
    · exfalso; first | exact Hn.1 ‹_› | exact Hn.1 rfl
    icases K.ivAt_open_ivl _ _ _ $$ Hiv with ⟨%zb, %ze, Hivl, #Hkzb, #Hkze, Hivb⟩
    wp_apply (h_Interval_Compare K hK) ivp dq vb ve db de b e _ q zb ze .discard .discard
      z.1.1 z.1.2 $$ [Hivp Hkb Hke Hivl] as ⟨Hivp, Hkb, Hke, Hivl, -, -⟩
    · iframe ∗ #
    ihave Hiv := Hivb $$ Hivl
    have hz : ∀ v : Int, -1 ≤ v → v ≤ 1 → sint.Z (W64 v) = v := by
      intro v h1 h2; word
    have hvb : -1 ≤ adt.ivlCmp (b, e) z.1 ∧ adt.ivlCmp (b, e) z.1 ≤ 1 := by
      unfold adt.ivlCmp; split <;> (try split) <;> simp
    have h0 : sint.Z (W64 0) = 0 := rfl
    simp only [Prod.eta]
    rw [hz _ hvb.1 hvb.2, h0]
    -- the node, repacked, with the lent subtrees: not lent itself, or lent
    ihave Hpack : (∀ (nsl nsr : List Loc) (esl esr : List adt.Entry),
        K.ivAt x.[intervalNode, go!"iv"] q z -∗
        K.maxAt x.[intervalNode, go!"max"] q (adt.nodeMax l z r) -∗
        x.[intervalNode, go!"left"] ↦{q} lp -∗ x.[intervalNode, go!"right"] ↦{q} rp -∗
        x.[intervalNode, go!"parent"] ↦{q} p -∗ x.[intervalNode, go!"c"] ↦{q} adt.colorW c -∗
        adt.ownNodeH K s q x lp l nsl esl -∗ adt.ownNodeH K s q x rp r nsr esr -∗
        adt.ownNodeH K s q p x (.node c l z r) (nsl ++ nsr) (esl ++ esr)) $$ []
    · iintro %nsl %nsr %esl %esr Hiv Hmx Hl Hr Hp Hc Hnl Hnr
      rw [adt.ownNodeH_node]
      iexists lp, rp, nsl, nsr, esl, esr, false
      simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
      iframe
      ipureintro; exact ⟨Hn.1, Hn.2, trivial, trivial⟩
    ihave Hpackz : (∀ (nsl nsr : List Loc) (esl esr : List adt.Entry),
        K.maxAt x.[intervalNode, go!"max"] q (adt.nodeMax l z r) -∗
        x.[intervalNode, go!"left"] ↦{q} lp -∗ x.[intervalNode, go!"right"] ↦{q} rp -∗
        x.[intervalNode, go!"parent"] ↦{q} p -∗ x.[intervalNode, go!"c"] ↦{q} adt.colorW c -∗
        adt.ownNodeH K s q x lp l nsl esl -∗ adt.ownNodeH K s q x rp r nsr esr -∗
        adt.ownNodeH K s q p x (.node c l z r) (nsl ++ [x] ++ nsr) (esl ++ [z] ++ esr)) $$ []
    · iintro %nsl %nsr %esl %esr Hmx Hl Hr Hp Hc Hnl Hnr
      rw [adt.ownNodeH_node]
      iexists lp, rp, nsl, nsr, esl, esr, true
      simp only [↓reduceIte]
      iframe
      ipureintro; exact ⟨Hn.1, Hn.2, trivial, trivial⟩
    by_cases hneg : adt.ivlCmp (b, e) z.1 < 0
    · -- left only
      have hvn : (adt.RbT.node c l z r).visitL (b, e) = l.visitL (b, e) := by
        simp [adt.RbT.visitL, hneg]
      have hSl : acc.map Prod.snd ++ l.visitL (b, e) <+: S := by rw [← hvn]; exact hS
      wp_if_destruct
      · wp_apply (ihl x lp acc hSl) $$ [$Hnl $Hivp $Hkb $Hke $HI $Hnv]
          as %rl ⟨Hivp, Hkb, Hke, %nsl, %esl, %Hel, Hnl, HIl⟩
        icases adt.ownNode_holes_nil K s q x rp r $$ Hnr with Hnr
        ihave Hnode := Hpack $$ %nsl %([] : List Loc) %esl %([] : List adt.Entry)
          Hiv Hmx Hl Hr' Hp Hc' Hnl Hnr
        cases rl with
        | true =>
          simp only [Bool.false_eq_true, ↓reduceIte] at Hel ⊢
          wp_auto
          iapply HΦ
          iframe Hivp Hkb Hke
          iexists nsl, esl
          simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
          iframe
          ipureintro
          rw [hvn]; exact Hel
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at Hel ⊢
          wp_auto
          iapply HΦ
          iframe Hivp Hkb Hke
          iexists nsl, esl
          simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
          iframe
          ipureintro
          rw [hvn]; exact Hel
      · exfalso; exact Hif (by simp [hneg])
    wp_if_destruct
    · exfalso; apply hneg; simpa using Hif
    by_cases hpos : adt.ivlCmp (b, e) z.1 > 0
    · icases K.ivAt_open _ _ _ $$ Hiv with ⟨%zb', %ze', Hb, He, Hv, #Hkzb', #Hkze', Hivb⟩
      icases K.maxAt_open _ _ _ $$ Hmx with ⟨%vm, Hmx, #Hkm⟩
      wp_if_destruct
      · rename_i maxiv_ptr
        wp_apply (h_Interval_Compare K hK) maxiv_ptr (DFrac.own 1) zb' vm .discard .discard
          z.1.1 (adt.nodeMax l z r) ivp dq vb ve db de b e $$ [maxiv Hivp Hkb Hke]
          as ⟨maxiv, -, -, Hivp, Hkb, Hke⟩
        · unfold adt.KeyRep.ivl; iframe ∗ #
        ihave Hiv := Hivb $$ [Hb He Hv]
        · iframe
        ihave Hmx := K.maxAt_intro _ _ _ vm $$ [Hmx]
        · iframe ∗ #
        have hmb : -1 ≤ adt.ivlCmp (z.1.1, adt.nodeMax l z r) (b, e) ∧
            adt.ivlCmp (z.1.1, adt.nodeMax l z r) (b, e) ≤ 1 := by
          unfold adt.ivlCmp; split <;> (try split) <;> simp
        have hmw : W64 (adt.ivlCmp (z.1.1, adt.nodeMax l z r) (b, e)) = W64 0 ↔
            adt.ivlCmp (z.1.1, adt.nodeMax l z r) (b, e) = 0 := by
          constructor <;> intro h <;> word
        wp_if_destruct
        · -- both subtrees
          have hm := hmw.1 Hif
          have hvn : (adt.RbT.node c l z r).visitL (b, e) = l.visitL (b, e) ++ r.visitL (b, e) := by
            simp [adt.RbT.visitL, hneg, hpos, hm]
          have hSl : acc.map Prod.snd ++ l.visitL (b, e) <+: S :=
            (List.prefix_append _ _).trans (by rw [List.append_assoc, ← hvn]; exact hS)
          wp_apply (ihl x lp acc hSl) $$ [$Hnl $Hivp $Hkb $Hke $HI $Hnv]
            as %rl ⟨Hivp, Hkb, Hke, %nsl, %esl, %Hel, Hnl, HIl⟩
          cases rl with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at Hel ⊢
            wp_auto
            icases adt.ownNode_holes_nil K s q x rp r $$ Hnr with Hnr
            ihave Hnode := Hpack $$ %nsl %([] : List Loc) %esl %([] : List adt.Entry)
              Hiv Hmx Hl Hr' Hp Hc' Hnl Hnr
            iapply HΦ
            iframe Hivp Hkb Hke
            iexists nsl, esl
            simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
            iframe
            ipureintro
            rw [hvn]
            exact ⟨Hel.1.trans (List.prefix_append _ _), Hel.2⟩
          | true =>
            simp only [↓reduceIte] at Hel ⊢
            ihave %hl1 := adt.ownNodeH_length K _ _ _ _ _ _ _ $$ Hnl
            have hSr : (acc ++ nsl.zip esl).map Prod.snd ++ r.visitL (b, e) <+: S := by
              rw [List.map_append, List.map_snd_zip (by omega), Hel, List.append_assoc, ← hvn]
              exact hS
            wp_auto
            wp_apply (ihr x rp _ hSr) $$ [$Hnr $Hivp $Hkb $Hke $HIl $Hnv]
              as %rr ⟨Hivp, Hkb, Hke, %nsr, %esr, %Her, Hnr, HIr⟩
            ihave Hnode := Hpack $$ %nsl %nsr %esl %esr Hiv Hmx Hl Hr' Hp Hc' Hnl Hnr
            cases rr with
            | true =>
              simp only [↓reduceIte] at Her ⊢
              wp_auto
              iapply HΦ
              iframe Hivp Hkb Hke
              iexists nsl ++ nsr, esl ++ esr
              simp only [↓reduceIte]
              rw [List.zip_append hl1, ← List.append_assoc]
              iframe
              ipureintro
              rw [hvn, Hel, Her]
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte] at Her ⊢
              wp_auto
              iapply HΦ
              iframe Hivp Hkb Hke
              iexists nsl ++ nsr, esl ++ esr
              simp only [Bool.false_eq_true, ↓reduceIte]
              rw [List.zip_append hl1, ← List.append_assoc]
              iframe
              ipureintro
              rw [hvn, Hel]
              obtain ⟨t, ht⟩ := Her.1
              exact ⟨⟨t, by rw [List.append_assoc, ht]⟩, by simp [Her.2]⟩
        · -- neither
          have hm : ¬ adt.ivlCmp (z.1.1, adt.nodeMax l z r) (b, e) = 0 :=
            fun h => Hif (hmw.2 h)
          have hvn : (adt.RbT.node c l z r).visitL (b, e) = [] := by
            simp [adt.RbT.visitL, hneg, hpos, hm]
          iapply HΦ
          iframe Hivp Hkb Hke
          iexists [], []
          simp only [↓reduceIte]
          icases adt.ownNode_holes_nil K s q x lp l $$ Hnl with Hnl
          icases adt.ownNode_holes_nil K s q x rp r $$ Hnr with Hnr
          ihave Hnode := Hpack $$ %([] : List Loc) %([] : List Loc) %([] : List adt.Entry)
            %([] : List adt.Entry) Hiv Hmx Hl Hr' Hp Hc' Hnl Hnr
          simp only [List.zip_nil_right, List.append_nil]
          iframe
          ipureintro
          rw [hvn]
      · exfalso; apply Hif; simp [hz _ hvb.1 hvb.2, h0, hpos]
    have hz0 : adt.ivlCmp (b, e) z.1 = 0 := by omega
    wp_if_destruct
    · exfalso; apply hpos; simpa [hz _ hvb.1 hvb.2, h0] using Hif
    have hvn : (adt.RbT.node c l z r).visitL (b, e) = l.visitL (b, e) ++ z :: r.visitL (b, e) := by
      simp [adt.RbT.visitL, hz0]
    have hSl : acc.map Prod.snd ++ l.visitL (b, e) <+: S :=
      (List.prefix_append _ _).trans (by rw [List.append_assoc, ← hvn]; exact hS)
    wp_apply (ihl x lp acc hSl) $$ [$Hnl $Hivp $Hkb $Hke $HI $Hnv]
      as %rl ⟨Hivp, Hkb, Hke, %nsl, %esl, %Hel, Hnl, HIl⟩
    ihave %hl1 := adt.ownNodeH_length K _ _ _ _ _ _ _ $$ Hnl
    cases rl with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at Hel ⊢
      wp_auto
      icases adt.ownNode_holes_nil K s q x rp r $$ Hnr with Hnr
      ihave Hnode := Hpack $$ %nsl %([] : List Loc) %esl %([] : List adt.Entry)
        Hiv Hmx Hl Hr' Hp Hc' Hnl Hnr
      iapply HΦ
      iframe Hivp Hkb Hke
      iexists nsl, esl
      simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
      iframe
      ipureintro
      rw [hvn]
      exact ⟨Hel.1.trans (List.prefix_append _ _), Hel.2⟩
    | true =>
      simp only [↓reduceIte] at Hel ⊢
      have hpz : (acc ++ nsl.zip esl).map Prod.snd ++ [z] <+: S := by
        rw [List.map_append, List.map_snd_zip (by omega), Hel]
        refine (List.prefix_append _ (r.visitL (b, e))).trans ?_
        simpa only [hvn, List.append_assoc, List.singleton_append] using hS
      ihave Hnv' := Hnv
      iunfold adt.nodeVisitorOk at Hnv'
      wp_auto
      wp_apply Hnv' $$ %x %z %(acc ++ nsl.zip esl) [HIl Hiv] as %rv HIv
      · iframe
        ipureintro; exact ⟨hpz.sublist, fun _ => hpz⟩
      cases rv with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        wp_auto
        icases adt.ownNode_holes_nil K s q x rp r $$ Hnr with Hnr
        ihave Hnode := Hpackz $$ %nsl %([] : List Loc) %esl %([] : List adt.Entry)
          Hmx Hl Hr' Hp Hc' Hnl Hnr
        iapply HΦ
        iframe Hivp Hkb Hke
        iexists nsl ++ [x] ++ [], esl ++ [z] ++ []
        simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
        rw [List.zip_append hl1]
        simp only [List.zip_cons_cons, List.zip_nil_right, List.append_assoc]
        iframe
        ipureintro
        rw [hvn, Hel]
        exact ⟨⟨r.visitL (b, e), by simp⟩, by simp⟩
      | true =>
        simp only [↓reduceIte]
        have hSr : ((acc ++ nsl.zip esl) ++ [(x, z)]).map Prod.snd ++ r.visitL (b, e) <+: S := by
          rw [List.map_append, List.map_append, List.map_snd_zip (by omega), Hel]
          simpa only [hvn, List.map_cons, List.map_nil, List.append_assoc,
            List.singleton_append] using hS
        wp_auto
        wp_apply (ihr x rp _ hSr) $$ [$Hnr $Hivp $Hkb $Hke $HIv $Hnv]
          as %rr ⟨Hivp, Hkb, Hke, %nsr, %esr, %Her, Hnr, HIr⟩
        ihave Hnode := Hpackz $$ %nsl %nsr %esl %esr Hmx Hl Hr' Hp Hc' Hnl Hnr
        cases rr with
        | true =>
          simp only [↓reduceIte] at Her ⊢
          wp_auto
          iapply HΦ
          iframe Hivp Hkb Hke
          iexists nsl ++ [x] ++ nsr, esl ++ [z] ++ esr
          simp only [↓reduceIte]
          rw [List.zip_append (by simp [hl1]), List.zip_append hl1]
          simp only [List.zip_cons_cons, List.zip_nil_right, List.append_assoc,
            List.singleton_append, List.cons_append, List.nil_append]
          iframe
          ipureintro
          rw [hvn, Hel, Her]
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at Her ⊢
          wp_auto
          iapply HΦ
          iframe Hivp Hkb Hke
          iexists nsl ++ [x] ++ nsr, esl ++ [z] ++ esr
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [List.zip_append (by simp [hl1]), List.zip_append hl1]
          simp only [List.zip_cons_cons, List.zip_nil_right, List.append_assoc,
            List.singleton_append, List.cons_append, List.nil_append]
          iframe
          ipureintro
          rw [hvn, Hel]
          obtain ⟨t, ht⟩ := Her.1
          exact ⟨⟨t, by rw [List.append_assoc, List.cons_append, ht]⟩, by simp⟩

end proof

end EtcdGrove
end Perennial
