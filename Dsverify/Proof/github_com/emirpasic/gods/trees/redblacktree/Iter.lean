/-
The proofs of gods' red-black tree iterator (`iterator.go`; `Next` as the model `models/gods`
rewrites it without `goto`) and of `Tree.Left` (`Specs.lean`).
-/
module

public import Dsverify.Spec.github_com.emirpasic.gods.trees.redblacktree.Specs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.emirpasic.gods.trees.redblacktree

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [redblacktree.Assumptions] [go.BasicIntoValInj]

theorem not_of_not_decide_val {P : Prop} [Decidable P] (h : (#(!decide P) : val) = #true) : ¬P := by
  intro hp
  simp only [hp, decide_true, Bool.not_true] at h
  exact Bool.false_ne_true (go.intoVal_inj h)

theorem of_not_not_decide_val {P : Prop} [Decidable P] (h : ¬ (#(!decide P) : val) = #true) : P := by
  revert h; by_cases hp : P <;> simp [hp]

theorem not_decide_val_false {P : Prop} [Decidable P] (hp : P) : (#(!decide P) : val) = #false := by
  simp [hp]

theorem Tree.Iterator.wp_proof : Tree.Iterator.spec (GF := GF) := by
  intro tr
  wp_start as -
  wp_auto
  wp_end

theorem Iterator.Value.wp_proof : Iterator.Value.spec (GF := GF) := by
  intro q tr enc cmp T h D rest k v
  wp_start as Hown
  unfold ownIterT
  icases Hown with ⟨%nd, %pos, Hq, Htr, %Hat⟩
  rcases Hat with ⟨-, hc, -⟩ | ⟨-, hc, -⟩ | ⟨hpos, C, k', v', L, R, hT, hc, hrest⟩
  · cases hc
  · cases hc
  simp only [Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  unfold treeRaw
  icases Htr with ⟨%sz, Htr, Hns, %Hrep⟩
  obtain ⟨hrep, hperm, hnd⟩ := Hrep
  have hrep' := hrep
  rw [hT] at hrep'
  obtain ⟨hh, -⟩ := Rep_plug_node hrep'
  have hmem : nd ∈ D := hperm.symm.subset (hT ▸ mem_plug_node)
  ihave ⟨Hn, Hback⟩ := ownNodes_read' h D nd _ hmem hh $$ Hns
  wp_auto
  ihave Hns := Hback $$ Hn
  iapply HΦ
  iexists nd, pos
  iframe Hq
  isplitl [Htr Hns]
  · iexists sz; iframe; ipureintro; exact ⟨hrep, hperm, hnd⟩
  ipureintro
  exact Or.inr (Or.inr ⟨hpos, C, k, v, L, R, hT, rfl, hrest⟩)

theorem Iterator.Key.wp_proof : Iterator.Key.spec (GF := GF) := by
  intro q tr enc cmp T h D rest k v
  wp_start as Hown
  unfold ownIterT
  icases Hown with ⟨%nd, %pos, Hq, Htr, %Hat⟩
  rcases Hat with ⟨-, hc, -⟩ | ⟨-, hc, -⟩ | ⟨hpos, C, k', v', L, R, hT, hc, hrest⟩
  · cases hc
  · cases hc
  simp only [Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  unfold treeRaw
  icases Htr with ⟨%sz, Htr, Hns, %Hrep⟩
  obtain ⟨hrep, hperm, hnd⟩ := Hrep
  have hrep' := hrep
  rw [hT] at hrep'
  obtain ⟨hh, -⟩ := Rep_plug_node hrep'
  have hmem : nd ∈ D := hperm.symm.subset (hT ▸ mem_plug_node)
  ihave ⟨Hn, Hback⟩ := ownNodes_read' h D nd _ hmem hh $$ Hns
  wp_auto
  ihave Hns := Hback $$ Hn
  iapply HΦ
  iexists nd, pos
  iframe Hq
  isplitl [Htr Hns]
  · iexists sz; iframe; ipureintro; exact ⟨hrep, hperm, hnd⟩
  ipureintro
  exact Or.inr (Or.inr ⟨hpos, C, k, v, L, R, hT, rfl, hrest⟩)

theorem Tree.Left.wp_proof : Tree.Left.spec (GF := GF) := by
  intro tr enc cmp T h D
  wp_start as Htr
  unfold treeRaw
  icases Htr with ⟨%sz, Htr, Hns, %Hrep⟩
  obtain ⟨hrep, hperm, hnd⟩ := Hrep
  wp_auto
  ihave HI : (∃ (C : Ctx GoInterface) (S : RB GoInterface),
      "parent" ∷ parent_ptr ↦ Ctx.parent C null ∗
      "current" ∷ current_ptr ↦ S.loc ∗
      "%HCS" ∷ ⌜T = Ctx.plug C S ∧ Ctx.pre C = []⌝ : IProp GF) $$ [parent current]
  · iexists [], T; iframe; ipureintro; exact ⟨rfl, rfl⟩
  wp_for HI
  obtain ⟨hTCS, hpre⟩ := HCS
  have hrepS : Rep enc h S (Ctx.parent C null) := ((Rep_plug C S null).mp (hTCS ▸ hrep)).2
  wp_if_destruct
  · have hS : S.loc ≠ null := not_of_not_decide_val Hif
    cases S with
    | leaf => exact absurd rfl hS
    | node n k v L R =>
    obtain ⟨-, hh, -, -⟩ := hrepS
    have hmem : n ∈ D := hperm.symm.subset (hTCS ▸ mem_plug (by simp))
    ihave ⟨Hn, Hback⟩ := ownNodes_read' h D n _ hmem hh $$ Hns
    simp only [RB.loc_node]
    wp_auto
    ihave Hns := Hback $$ Hn
    wp_for_post
    iframe
    iexists (.L n k v R :: C), L
    iframe
    ipureintro
    exact ⟨hTCS, by simp [Ctx.pre, Frame.pre, hpre]⟩
  · have hS : S.loc = null := of_not_not_decide_val Hif
    rw [if_pos (decide_eq_true (not_decide_val_false hS))]
    have hSl : S = .leaf := (Rep_loc_eq_null hrepS).mp hS
    subst hSl
    wp_auto
    iapply HΦ
    isplitl [Htr Hns]
    · iexists sz; iframe; ipureintro; exact ⟨hrep, hperm, hnd⟩
    ipureintro
    cases C with
    | nil => left; exact ⟨hTCS, rfl⟩
    | cons f C =>
      obtain ⟨⟨n, k, v, r, rfl⟩, hpre'⟩ := Ctx.pre_cons_nil hpre
      right
      exact ⟨C, k, v, r, hTCS, hpre'⟩

theorem Iterator.Next.wp_proof (wp_Left : Tree.Left.spec (GF := GF)) :
    Iterator.Next.spec (GF := GF) := by
  intro q tr enc cmp T h D rest cur
  wp_start as Hown
  unfold ownIterT
  icases Hown with ⟨%nd, %pos, Hq, Htr, %Hat⟩
  wp_auto
  wp_if_destruct
  · -- past the end: stays there
    dsimp only [«end»]
    wp_auto
    rcases Hat with ⟨h0, -, -⟩ | ⟨-, hc, hr⟩ | ⟨h1, -⟩
    · exact absurd h0 (by decide)
    · subst hc hr
      iapply HΦ
      isplitr; · ipureintro; simp
      iexists null, W8 2
      iframe
      ipureintro; right; left; exact ⟨rfl, rfl, rfl⟩
    · exact absurd h1 (by decide)
  · ihave ⟨Htr, %Hraw⟩ := treeRaw_pure tr enc cmp T h D $$ Htr
    obtain ⟨hrep, hperm, hnd⟩ := Hraw
    wp_if_destruct
    · -- before the first entry: the leftmost node, if any
      rcases Hat with ⟨-, hc, hr⟩ | ⟨h2, -⟩ | ⟨h1, -⟩
      rotate_left
      · exact absurd h2 (by decide)
      · exact absurd h1 (by decide)
      subst hc hr
      wp_apply (wp_Left tr enc cmp T h D) $$ [$Htr]
      iintro %m ⟨Htr, %Hm⟩
      wp_auto
      by_cases hm : m = null
      · simp only [hm, _root_.decide_true, Bool.not_true]
        wp_auto
        rcases Hm with ⟨hT0, -⟩ | ⟨C, k, v, R, hT, hpre⟩
        · subst hT0
          dsimp only [«end»]
          wp_auto
          iapply HΦ
          simp only [RB.entries_leaf]
          isplitr; · ipureintro; simp
          iexists null, W8 2
          iframe
          ipureintro; right; left; exact ⟨rfl, rfl, rfl⟩
        · exfalso
          rw [hT] at hrep
          exact (Rep_plug_node hrep).2.1 hm
      · simp only [hm, _root_.decide_false, Bool.not_false]
        rcases Hm with ⟨-, hm0⟩ | ⟨C, k, v, R, hT, hpre⟩
        · exact absurd hm0 hm
        dsimp only [between]
        wp_auto
        have hrest : T.entries = (k, v) :: (R.entries ++ Ctx.post C) := by
          rw [hT, Ctx.plug_entries, hpre]; simp
        iapply HΦ
        rw [hrest]
        isplitr; · ipureintro; simp
        iexists m, W8 1
        iframe
        ipureintro; right; right; exact ⟨rfl, C, k, v, .leaf, R, hT, rfl, rfl⟩
    · -- at a node
      rcases Hat with ⟨h0, -⟩ | ⟨h2, -⟩ | ⟨hpos, C, k, v, L, R, hT, hc, hr⟩
      · exact absurd h0 Hif
      · exact absurd h2 ‹¬pos = W8 2›
      subst hc hr hpos
      have hrep' := hrep
      rw [hT] at hrep'
      obtain ⟨hh, hndn, hrepL, hrepR, hrepC⟩ := Rep_plug_node hrep'
      have hmem : nd ∈ D := hperm.symm.subset (hT ▸ mem_plug_node)
      unfold treeRaw
      icases Htr with ⟨%sz, Htr, Hns, -⟩
      ihave ⟨Hn, Hback⟩ := ownNodes_read' h D nd _ hmem hh $$ Hns
      wp_auto
      wp_if_destruct
      · -- no right subtree: up to the first ancestor of which it is in the left subtree
        ihave Hns := Hback $$ Hn
        have hR : R = .leaf := (Rep_loc_eq_null hrepR).mp Hif
        subst hR
        ihave HI : (∃ (C' : Ctx GoInterface) (S : RB GoInterface),
            "Hq" ∷ q ↦ Iterator.mk tr S.loc (W8 1) ∗
            "%Hinv" ∷ ⌜T = Ctx.plug C' S ∧ S ≠ .leaf ∧ Ctx.post C' = Ctx.post C⌝ : IProp GF) $$ [Hq]
        · iexists C, (RB.node nd k v L .leaf)
          iframe
          ipureintro; exact ⟨hT, by simp, rfl⟩
        wp_for HI
        obtain ⟨hTS, hSn, hpost⟩ := Hinv
        cases S with
        | leaf => exact absurd rfl hSn
        | node s ks vs SL SR =>
        simp only [RB.loc_node]
        have hrepS : Rep enc h (Ctx.plug C' (.node s ks vs SL SR)) null := hTS ▸ hrep
        obtain ⟨hhs, hsn, -, -, hrepC'⟩ := Rep_plug_node hrepS
        have hmems : s ∈ D := hperm.symm.subset (hTS ▸ mem_plug_node)
        ihave ⟨Hs, Hback⟩ := ownNodes_read' h D s _ hmems hhs $$ Hns
        wp_auto
        ihave Hns := Hback $$ Hs
        wp_if_destruct
        · -- a parent
          have hpar : Ctx.parent C' null ≠ null := not_of_not_decide_val Hif
          cases C' with
          | nil => exact absurd rfl hpar
          | cons f C'' =>
          obtain ⟨hf, -⟩ := hrepC'
          simp only [Ctx.parent_cons] at hhs hf
          ihave ⟨Hs, Hback⟩ := ownNodes_read' h D s _ hmems hhs $$ Hns
          wp_auto
          ihave Hns := Hback $$ Hs
          have hmemf : f.loc ∈ D := hperm.symm.subset (hTS ▸ mem_plug_ctx (C := f :: C'')
            (by cases f <;> simp [Ctx.locs, Frame.locs, Frame.loc]))
          cases f with
          | L fn fk fv fr =>
            obtain ⟨-, hhf, -⟩ := hf
            simp only [Frame.loc] at hmemf ⊢
            ihave ⟨Hf, Hback⟩ := ownNodes_read' h D fn _ hmemf hhf $$ Hns
            wp_auto
            ihave Hns := Hback $$ Hf
            dsimp only [between]
            wp_auto
            wp_for_post
            iapply HΦ
            rw [RB.entries_leaf, List.nil_append, ← hpost]
            simp only [Ctx.post, Frame.post, List.cons_append]
            isplitr; · ipureintro; simp
            iexists fn, W8 1
            iframe
            ipureintro
            refine ⟨⟨hrep, hperm, hnd⟩, ?_⟩
            right; right
            exact ⟨rfl, C'', fk, fv, .node s ks vs SL SR, fr, hTS, rfl, rfl⟩
          | R fn fk fv fl =>
            obtain ⟨-, hhf, -⟩ := hf
            simp only [Frame.loc] at hmemf ⊢
            ihave ⟨Hf, Hback⟩ := ownNodes_read' h D fn _ hmemf hhf $$ Hns
            wp_auto
            ihave Hns := Hback $$ Hf
            have hne : s ≠ fl.loc := by
              have hndT : (Ctx.plug (Frame.R fn fk fv fl :: C'') (.node s ks vs SL SR)).locs.Nodup :=
                hperm.nodup_iff.mp hnd |> (hTS ▸ ·)
              obtain ⟨-, -, hdis⟩ := nodup_plug hndT
              have hsn' := hdis s (by simp)
              intro hsl
              rcases loc_null_or_mem fl with h0 | h0
              · exact hsn (hsl.trans h0)
              · exact hsn' (by simp [Ctx.locs, Frame.locs, hsl, h0])
            simp only [hne, _root_.decide_false]
            wp_auto
            wp_for_post
            iframe
            iexists C'', (RB.node fn fk fv fl (.node s ks vs SL SR))
            iframe
            ipureintro
            exact ⟨hTS, by simp, by rw [← hpost]; simp [Ctx.post, Frame.post]⟩
        · -- the root: past the last entry
          have hC : C' = [] := by
            cases C' with
            | nil => rfl
            | cons f C'' =>
              exact absurd (of_not_not_decide_val Hif) (RepC_parent_ne_null hrepC' (by simp))
          subst hC
          rw [if_pos (decide_eq_true (not_decide_val_false (of_not_not_decide_val Hif)))]
          dsimp only [«end»]
          wp_auto
          iapply HΦ
          rw [RB.entries_leaf, List.nil_append, ← hpost]
          simp only [Ctx.post]
          isplitr; · ipureintro; simp
          iexists null, W8 2
          iframe
          ipureintro
          refine ⟨⟨hrep, hperm, hnd⟩, ?_⟩
          right; left; exact ⟨rfl, rfl, rfl⟩
      · -- a right subtree: its leftmost node
        cases R with
        | leaf => exact absurd rfl Hif
        | node r kr vr RL RR =>
        ihave Hns := Hback $$ Hn
        ihave HI : (∃ (C' : Ctx GoInterface) (S : RB GoInterface),
            "Hq" ∷ q ↦ Iterator.mk tr S.loc (W8 1) ∗
            "%Hinv" ∷ ⌜T = Ctx.plug C' S ∧ S ≠ .leaf ∧
              S.entries ++ Ctx.post C' = (RB.node r kr vr RL RR).entries ++ Ctx.post C⌝ : IProp GF) $$ [Hq]
        · iexists (.R nd k v L :: C), (RB.node r kr vr RL RR)
          simp only [RB.loc_node]
          iframe
          ipureintro; exact ⟨hT, by simp, by simp [Ctx.post, Frame.post]⟩
        wp_for HI
        obtain ⟨hTS, hSn, hent⟩ := Hinv
        cases S with
        | leaf => exact absurd rfl hSn
        | node s ks vs SL SR =>
        simp only [RB.loc_node]
        have hrepS : Rep enc h (Ctx.plug C' (.node s ks vs SL SR)) null := hTS ▸ hrep
        obtain ⟨hhs, hsn, hrepSL, -, -⟩ := Rep_plug_node hrepS
        have hmems : s ∈ D := hperm.symm.subset (hTS ▸ mem_plug_node)
        ihave ⟨Hs, Hback⟩ := ownNodes_read' h D s _ hmems hhs $$ Hns
        wp_auto
        wp_if_destruct
        · -- a left child: down
          have hSL : SL.loc ≠ null := not_of_not_decide_val Hif
          ihave Hns := Hback $$ Hs
          wp_for_post
          iframe
          iexists (.L s ks vs SR :: C'), SL
          iframe
          ipureintro
          refine ⟨hTS, ?_, ?_⟩
          · intro h0; subst h0; exact hSL rfl
          · rw [← hent]; simp [Ctx.post, Frame.post]
        · -- the leftmost node
          have hSL : SL.loc = null := of_not_not_decide_val Hif
          rw [if_pos (decide_eq_true (not_decide_val_false hSL))]
          ihave Hns := Hback $$ Hs
          have hSL' : SL = .leaf := (Rep_loc_eq_null hrepSL).mp hSL
          subst hSL'
          dsimp only [between]
          wp_auto
          iapply HΦ
          rw [← hent]
          simp only [RB.entries_node, RB.entries_leaf, List.nil_append, List.cons_append]
          isplitr; · ipureintro; simp
          iexists s, W8 1
          iframe
          ipureintro
          refine ⟨⟨hrep, hperm, hnd⟩, ?_⟩
          right; right
          exact ⟨rfl, C', ks, vs, .leaf, SR, hTS, rfl, rfl⟩

end proof

end Perennial.github_com.emirpasic.gods.trees.redblacktree
