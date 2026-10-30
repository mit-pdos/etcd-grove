module
public import Spec.go_etcd_io.bbolt.Bucket__dereference_x
public import Spec.go_etcd_io.bbolt.node__root
public import Spec.go_etcd_io.bbolt.node__dereference_w
public import Proof.go_etcd_io.bbolt.SpillDeref

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- An inline page in the view is stale after the remap. -/
theorem pageOwn_staleX (W : WView) (B : BRec) (M : GMap Loc NRec) :
    pageOwn (GF := GF) W B ⊢ pageOwn W { B with ns := M, isrc := staleOf B.isrc } := by
  unfold pageOwn
  simp only
  by_cases h : B.bv.page' = null
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    cases B.isrc with
    | view => iintro -; simp only [staleOf]; ipureintro; trivial
    | own dq => simp only [staleOf]; iintro H; iexact H
    | stale => simp only [staleOf]; iintro H; iexact H

/-- `x.dereference()` with the buckets `bs` (see `WriteDerefB`), by induction on the depth. -/
theorem deref_recX (hroot : node.root.spec (GF := GF) (hG := hG))
    (hnd : node.dereference.wspec (GF := GF) (hG := hG)) (W : WView) (hc : W.data.locCar ≠ 0)
    (txl : Loc) (dep : Loc → Nat) :
    ∀ (n : Nat) (x : Loc) (bs : GMap Loc BRec) (st : TxStats), dep x < n → depOK dep bs →
    readyAtX bs x → txOK txl bs →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ([∗map] bl ↦ B ∈ bs, bktOwnX W bl B) ∗
        structFieldRef Tx go!"stats" txl ↦ st ∗ pagesView W.data W.ps W.q W.pages }}
      (App (Val (x @!! go.GoType.PointerType Bucket.ty @!! go!"dereference")) (Val #()))
    {{ RET #(); ∃ (bs' : GMap Loc BRec) (st' : TxStats), ⌜derefMX bs bs' ∧ derefFromX bs bs' x ∧ keepM bs bs'⌝ ∗
        ([∗map] bl ↦ B ∈ bs', bktOwnX W bl B) ∗ structFieldRef Tx go!"stats" txl ↦ st' ∗
        pagesView W.data W.ps W.q W.pages }} := by
  intro n
  induction n with
  | zero => intro x bs st h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro x bs st hn hdep hready htx
    obtain ⟨B, hB, hrd⟩ := hready x reachB.root
    have htxB : B.bv.tx' = txl := htx x B hB
    wp_start as ⟨Hbs, Hst, Hpv⟩
    icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun bl B => bktOwnX (GF := GF) W bl B)
      (show Std.get? bs x = some B from hB)).1 $$ Hbs with ⟨Hx, Hbs⟩
    isimp only [bktOwnX] at Hx
    icases Hx with ⟨Hbv, Hib, Hnm, Hbm, Hpo, Hns⟩
    try wp_auto
    wp_join iprop(b_ptr ↦ x ∗ ∃ (B1 : BRec) (st1 : TxStats), ⌜derefBktX B B1 ∧ ∀ l r r', B.ns !! l = some r → B1.ns !! l = some r' →
        r'.nv = { r.nv with key' := r'.nv.key' }⌝ ∗ x ↦ B.bv ∗ pageOwn W B1 ∗
        ([∗map] l ↦ r ∈ B1.ns, nodeOwnX W l r) ∗ structFieldRef Tx go!"stats" txl ↦ st1 ∗
        pagesView W.data W.ps W.q W.pages)
      at next with [b Hbv Hpo Hns Hst Hpv] as ⟨b, %B1, %st1, %HB1x, Hbv, Hpo, Hns, Hst, Hpv⟩
    · by_cases hrn : B.bv.rootNode' = null
      · rw [decide_eq_true hrn]
        try wp_auto
        isplitl []
        · ipureintro; rfl
        isplitl [b]
        · iexact b
        iexists { B with ns := Iris.Std.PartialMap.map staleRec B.ns, isrc := staleOf B.isrc }, st
        iframe
        have hlk : ∀ l, (Iris.Std.PartialMap.map staleRec B.ns : GMap Loc NRec) !! l =
            (B.ns !! l).map staleRec := by
          intro l
          change Iris.Std.PartialMap.get? (Iris.Std.PartialMap.map staleRec B.ns) l = _
          rw [Iris.Std.LawfulPartialMap.get?_map (M := GMap Loc)]; rfl
        isplitr
        · ipureintro
          refine ⟨own_step_nilX B hrn, fun l r r' hr h => ?_⟩
          change (Iris.Std.PartialMap.map staleRec B.ns : GMap Loc NRec) !! l = some r' at h
          rw [hlk, hr] at h; cases h; rfl
        isplitl [Hpo]
        · iapply pageOwn_staleX; iexact Hpo
        iapply (BiEntails.of_eq (BigSepM.bigSepM_map (M := GMap Loc)
          (Φ := fun l r => nodeOwnX (GF := GF) W l r) (m := B.ns) (f := staleRec))).2
        iapply (BigSepM.bigSepM_mono (M := GMap Loc) (Φ := fun l r => nodeOwnX (GF := GF) W l r)
          (Ψ := fun l r => nodeOwnX (GF := GF) W l (staleRec r)) (fun {_ _} _ => nodeOwnX_stale W _ _)) $$ Hns
      · rw [decide_eq_false hrn]
        rcases hrd with hrd | ⟨S, hl, hok⟩
        · exact absurd hrd hrn
        obtain ⟨p, top, hup, hpnd, hk, hpS⟩ := hl
        obtain ⟨hpp, rest, hrest, hlast⟩ := chain_parentPath B.ns _ p top hup
        icases chain_accX W B.ns _ p top hup hpnd B.ns (fun _ _ => rfl) $$ Hns with ⟨Hch, Hchback⟩
        rw [hrest] at hpp
        rw [hrest]
        try wp_auto
        wp_apply hroot _ _ rest (DFrac.own 1) hpp $$ [Hch] as Hch
        · iframe
        rw [hlast]
        ihave Hns := Hchback $$ Hch
        dsimp only
        have hQ : ∀ l, l ∈ p.filter (fun l => decide (l ∉ S)) ↔ l ∈ p ∧ l ∉ S := by
          intro l; simp
        have hQnd : (p.filter (fun l => decide (l ∉ S))).Nodup := hpnd.filter _
        have hQdom : ∀ l ∈ p.filter (fun l => decide (l ∉ S)), (B.ns !! l).isSome := by
          intro l hl; obtain ⟨r, hr, -⟩ := hpS l ((hQ l).1 hl).1 ((hQ l).1 hl).2; rw [hr]; rfl
        icases map_split (fun l r => nodeOwnX (GF := GF) W l r) _ B.ns hQnd hQdom $$ Hns
          with ⟨HQ, %ns', %Hns', Hns⟩
        have hns'S : ∀ l ∈ S, ns' !! l = B.ns !! l := by
          intro l hl; rw [Hns' l, if_neg (fun h => ((hQ l).1 h).2 hl)]
        have hk' : kidsTree ns' top S := kidsTree_mono B.ns ns' S.length top S (Nat.le_refl _)
          (fun l hl r hr => ⟨r, by rw [hns'S l hl]; exact hr, rfl, rfl⟩) hk
        have hok' : ∀ l ∈ S, ∃ r, ns' !! l = some r ∧ derefOK x r := by
          intro l hl; rw [hns'S l hl]; exact hok l hl
        ihave HQ := (BigSepL.bigSepL_mono (Ψ := fun _ l => iprop(∃ v, ⌜B.ns !! l = some v ∧ noViewRec v⌝ ∗
            nodeOwnX (GF := GF) W l v)) ?_) $$ HQ
        · intro k l hl
          iintro ⟨%v, %hv, Hv⟩
          iexists v; iframe; ipureintro
          have hm := (hQ l).1 (List.mem_of_getElem? hl)
          obtain ⟨r, hr, hnv⟩ := hpS l hm.1 hm.2
          rw [hr] at hv; cases hv
          exact ⟨hr, hnv⟩
        icases bkt_tree_accX W hc x ns' top S hk' hok' W.q $$ [Hpv Hns] with ⟨Htree, Htback⟩
        · iframe
        wp_apply hnd (gOf ns' S W.q) S.length top x B.bv (DFrac.own 1) st $$ [Htree Hbv Hst]
          as %k ⟨Htree, Hbv, Hst⟩
        · rw [htxB]; iframe
        ihave Htb := Htback $$ Htree
        icases Htb with ⟨%M, %HM, Hpv, Hns⟩
        have hMQ : ∀ l ∈ p.filter (fun l => decide (l ∉ S)), M !! l = none := by
          intro l hl
          cases h : M !! l with
          | none => rfl
          | some _ =>
            have := (HM.1 l).1 (by rw [h]; rfl)
            rw [Hns' l, if_pos hl] at this; cases this
        icases list_into_map (fun l r => nodeOwnX (GF := GF) W l r)
          (fun l v => B.ns !! l = some v ∧ noViewRec v) _ M hQnd hMQ $$ [Hns HQ] with ⟨%M', %HM', Hns⟩
        · iframe
        try wp_auto
        isplitl []
        · ipureintro; rfl
        isplitl [b]
        · iexact b
        iexists { B with ns := M', isrc := staleOf B.isrc }, _
        rw [htxB]
        iframe
        isplitr
        · ipureintro
          have hfromM : ∀ l r', M !! l = some r' → ∃ r, B.ns !! l = some r ∧
              ((l ∈ S ∧ derefNodeK r r') ∨ (l ∉ S ∧ r' = staleRec r)) := by
            intro l r' h
            obtain ⟨r, hr, hd⟩ := HM.2 l r' h
            have hlQ : l ∉ p.filter (fun l => decide (l ∉ S)) := by
              intro hq; have := (HM.1 l).1 (by rw [h]; rfl); rw [Hns' l, if_pos hq] at this; cases this
            rw [Hns' l, if_neg hlQ] at hr
            exact ⟨r, hr, hd⟩
          have hSdom : ∀ l, l ∈ S ∨ l ∈ p → (B.ns !! l).isSome := by
            intro l hl
            by_cases hlS : l ∈ S
            · obtain ⟨r, hr, -⟩ := hok l hlS; rw [hr]; rfl
            · rcases hl with hl | hl
              · exact absurd hl hlS
              · obtain ⟨r, hr, -⟩ := hpS l hl hlS; rw [hr]; rfl
          have hdom : ∀ l, (M' !! l).isSome ↔ (B.ns !! l).isSome := by
            intro l
            rw [HM'.1 l, HM.1 l, Hns' l]
            by_cases hq : l ∈ p.filter (fun l => decide (l ∉ S))
            · rw [if_pos hq]; simp only [Option.isSome_none, Bool.false_eq_true, false_or]
              exact ⟨fun _ => hQdom l hq, fun _ => hq⟩
            · rw [if_neg hq]; simp only [hq, or_false]
          refine ⟨own_stepX B S p top M' hup hk hSdom hdom (fun l r' h => ?_) (fun l hl r r' hr hr' => ?_), ?_⟩
          · rcases HM'.2 l r' h with h1 | ⟨h1, h2⟩
            · obtain ⟨r, hr, hd | hd⟩ := hfromM l r' h1
              · exact ⟨r, hr, Or.inl hd.2.1⟩
              · exact ⟨r, hr, Or.inr (Or.inr hd.2)⟩
            · exact ⟨r', h1, Or.inr (Or.inl ⟨rfl, h2⟩)⟩
          · rcases HM'.2 l r' hr' with h1 | ⟨h1, h2⟩
            · obtain ⟨r0, hr0, hd | hd⟩ := hfromM l r' h1
              · rw [hr] at hr0; cases hr0; exact Or.inl hd.2.1
              · exfalso
                have hlp : l ∈ p := by
                  rcases hl with hl | hl
                  · exact absurd hl hd.1
                  · exact hl
                have := hMQ l ((hQ l).2 ⟨hlp, hd.1⟩); rw [h1] at this; cases this
            · rw [hr] at h1; cases h1; exact Or.inr ⟨rfl, h2⟩
          · intro l r r' hr hr'
            rcases HM'.2 l r' hr' with h1 | ⟨h1, -⟩
            · obtain ⟨r0, hr0, hd | hd⟩ := hfromM l r' h1
              · rw [hr] at hr0; cases hr0; exact hd.2.2
              · rw [hr] at hr0; cases hr0; rw [hd.2]; rfl
            · rw [hr] at h1; cases h1; rfl
        iapply pageOwn_staleX; iexact Hpo
    have hRm0 := derefMX_refl (GMap.delete x bs)
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply wp_map_for_range (fun (keys : List GoString) (i : Int) => iprop(∃ (R : GMap Loc BRec)
        (st2 : TxStats) (cv : Loc),
        "%Hi" ∷ ⌜0 ≤ i ∧ derefMX (GMap.delete x bs) R ∧ keepM (GMap.delete x bs) R ∧ ∀ (k : Nat) name c, k < i.toNat →
          keys[k]? = some name → B.bm !! name = some c → derefFromX (GMap.delete x bs) R c⌝ ∗
        "HR" ∷ ([∗map] bl ↦ B ∈ R, bktOwnX W bl B) ∗
        "Hst" ∷ structFieldRef Tx go!"stats" txl ↦ st2 ∗
        "Hpv" ∷ pagesView W.data W.ps W.q W.pages ∗
        "child" ∷ child_ptr ↦ cv)) $$ Hbm
    iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
    isplitl [Hbs Hst Hpv child]
    · iexists (GMap.delete x bs), st1, _
      iframe
      ipureintro
      exact ⟨Int.le_refl _, hRm0, keepM_refl _, fun k _ _ hk _ _ => by simp at hk⟩
    isplitr
    · imodintro
      iintro %i %key %c ⟨%Hkey, %Hc⟩ HP
      iNamed HP
      obtain ⟨Hi0, HRm, HRk, Hdone⟩ := Hi
      obtain ⟨hcx, hdR, hrdR, htxR⟩ := child_preX dep txl x bs R B key c hB hdep hready htx HRm Hc
      obtain ⟨-, hdep0, -, -⟩ := child_preX dep txl x bs (GMap.delete x bs) B key c hB hdep hready htx
        hRm0 Hc
      try wp_auto
      wp_apply ih c R st2 (by omega) hdR hrdR htxR $$ [HR Hst Hpv] as ⟨%R', %st3, %HR', HR, Hst, Hpv⟩
      · iframe
      try wp_auto
      obtain ⟨hM', hF', hprev⟩ := child_postX dep (GMap.delete x bs) R R' c hdep0 HRm HR'.1 HR'.2.1
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists R', st3, c
      iframe
      ipureintro
      refine ⟨by omega, hM', keepM_trans _ _ _ HRm HR'.1 HRk HR'.2.2, fun k name c' hk hkn hc' => ?_⟩
      by_cases e : k = i.toNat
      · subst e; rw [Hkey] at hkn; cases hkn; rw [Hc] at hc'; cases hc'; exact hF'
      · exact hprev c' (Hdone k name c' (by omega) hkn hc')
    iintro HP Hbm
    iNamed HP
    obtain ⟨Hi0, HRm, HRk, Hdone⟩ := Hi
    have hall : ∀ name c, B.bm !! name = some c → derefFromX (GMap.delete x bs) R c := by
      intro name c hc
      have hmem : name ∈ keys := (Hkset name).2 (by rw [hc]; rfl)
      obtain ⟨k, hk, hkn⟩ := List.getElem_of_mem hmem
      exact Hdone k name c (by omega) (by rw [List.getElem?_eq_getElem hk, hkn]) hc
    obtain ⟨HB1, HB1k⟩ := HB1x
    obtain ⟨hM, hF⟩ := finalX dep x bs R B B1 hB hdep HB1 HRm hall
    have hRx : R !! x = none := by
      cases h : R !! x with
      | none => rfl
      | some _ =>
        have := (HRm.1 x).2 (by rw [h]; rfl)
        rw [GMap.lookup_delete] at this; cases this
    try wp_auto
    iapply HΦ
    iexists (<[x := B1]> R), st2
    isplitl []
    · ipureintro
      refine ⟨hM, hF, fun y Y Y' l r r' hY hY' hr hr' => ?_⟩
      by_cases e : x = y
      · subst e; rw [hB] at hY; cases hY; rw [GMap.lookup_insert] at hY'; cases hY'
        exact HB1k l r r' hr hr'
      · rw [GMap.lookup_insert_ne _ _ e] at hY'
        exact HRk y Y Y' l r r' (by rw [GMap.lookup_delete_ne _ e]; exact hY) hY' hr hr'
    iframe
    iapply (BigSepM.bigSepM_insert (M := GMap Loc) (Φ := fun bl B => bktOwnX (GF := GF) W bl B)
      (show Std.get? R x = none from hRx)).2
    iframe
    unfold bktOwnX
    obtain ⟨e1, e2, e3, e4, -⟩ := HB1
    rw [e1, e2, e3, e4]
    iframe

theorem Bucket.dereference.wp_xproof (hroot : node.root.spec (GF := GF) (hG := hG))
    (hnd : node.dereference.wspec (GF := GF) (hG := hG)) :
    Bucket.dereference.xspec (GF := GF) (hG := hG) := by
  intro W txl T hready hc htx
  obtain ⟨dep, hdep, hrd⟩ := top_preX T _ hready
  iintro %Φ Hpre HΦ
  iapply (deref_recX hroot hnd W hc txl dep (dep (structFieldRef Tx go!"root" txl) + 1) _ T.bs
    T.t.stats' (Nat.lt_succ_self _) hdep hrd htx) $$ Hpre
  inext
  iintro ⟨%bs', %st', %H, Hbs, Hst, Hpv⟩
  iapply HΦ
  iexists { T with bs := bs', t := { T.t with stats' := st' } }
  iframe
  ipureintro; exact ⟨top_postX T _ bs' st' hready H.1 H.2.1, H.2.2⟩

end proof

end bbolt
end EtcdGrove
end Perennial
