module
public import Spec.go_etcd_io.bbolt.Bucket__dereference
public import Spec.go_etcd_io.bbolt.node__root
public import Spec.go_etcd_io.bbolt.node__dereference_w
public import Proof.go_etcd_io.bbolt.WriteDeref
public import Proof.go_etcd_io.bbolt.WriteDerefB

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
theorem pageOwn_stale (W : WView) (B : BRec) (M : GMap Loc NRec) :
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
theorem deref_rec (hroot : node.root.spec (GF := GF) (hG := hG))
    (hnd : node.dereference.wspec (GF := GF) (hG := hG)) (W : WView) (hc : W.data.locCar ≠ 0)
    (txl : Loc) (dep : Loc → Nat) :
    ∀ (n : Nat) (x : Loc) (bs : GMap Loc BRec) (st : TxStats), dep x < n → depOK dep bs →
    readyAt bs x → txOK txl bs →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ([∗map] bl ↦ B ∈ bs, bktOwn W bl B) ∗
        structFieldRef Tx go!"stats" txl ↦ st ∗ pagesView W.data W.ps W.q W.pages }}
      (App (Val (x @!! go.GoType.PointerType Bucket.ty @!! go!"dereference")) (Val #()))
    {{ RET #(); ∃ (bs' : GMap Loc BRec) (st' : TxStats), ⌜derefM bs bs' ∧ derefFrom bs bs' x⌝ ∗
        ([∗map] bl ↦ B ∈ bs', bktOwn W bl B) ∗ structFieldRef Tx go!"stats" txl ↦ st' ∗
        pagesView W.data W.ps W.q W.pages }} := by
  intro n
  induction n with
  | zero => intro x bs st h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro x bs st hn hdep hready htx
    obtain ⟨B, hB, hrd⟩ := hready x reachB.root
    have htxB : B.bv.tx' = txl := htx x B hB
    wp_start as ⟨Hbs, Hst, Hpv⟩
    icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun bl B => bktOwn (GF := GF) W bl B)
      (show Std.get? bs x = some B from hB)).1 $$ Hbs with ⟨Hx, Hbs⟩
    isimp only [bktOwn] at Hx
    icases Hx with ⟨Hbv, Hib, Hnm, Hbm, Hpo, Hns⟩
    try wp_auto
    wp_join iprop(b_ptr ↦ x ∗ ∃ (B1 : BRec) (st1 : TxStats), ⌜derefBkt B B1⌝ ∗ x ↦ B.bv ∗ pageOwn W B1 ∗
        ([∗map] l ↦ r ∈ B1.ns, nodeOwn W l r) ∗ structFieldRef Tx go!"stats" txl ↦ st1 ∗
        pagesView W.data W.ps W.q W.pages)
      at next with [b Hbv Hpo Hns Hst Hpv] as ⟨b, %B1, %st1, %HB1, Hbv, Hpo, Hns, Hst, Hpv⟩
    · by_cases hrn : B.bv.rootNode' = null
      · rw [decide_eq_true hrn]
        try wp_auto
        isplitl []
        · ipureintro; rfl
        isplitl [b]
        · iexact b
        iexists { B with ns := ∅, isrc := staleOf B.isrc }, st
        iframe
        isplitr
        · ipureintro; exact own_step_nil B hrn
        isplitl [Hpo]
        · iapply pageOwn_stale; iexact Hpo
        iapply BigSepM.bigSepM_empty.2; iempintro
      · rw [decide_eq_false hrn]
        rcases hrd with hrd | ⟨S, hl, hok⟩
        · exact absurd hrd hrn
        obtain ⟨p, top, hup, hpnd, hk, hpS⟩ := hl
        obtain ⟨hpp, rest, hrest, hlast⟩ := chain_parentPath B.ns _ p top hup
        icases chain_acc W B.ns _ p top hup hpnd B.ns (fun _ _ => rfl) $$ Hns with ⟨Hch, Hchback⟩
        rw [hrest] at hpp
        rw [hrest]
        try wp_auto
        wp_apply hroot _ _ rest (DFrac.own 1) hpp $$ [Hch] as Hch
        · iframe
        rw [hlast]
        ihave Hns := Hchback $$ Hch
        dsimp only
        icases bkt_tree_acc W hc x B.ns top S hk hok W.q $$ [Hpv Hns] with ⟨Htree, Htback⟩
        · iframe
        wp_apply hnd (gOf B.ns S W.q) S.length top x B.bv (DFrac.own 1) st $$ [Htree Hbv Hst]
          as %k ⟨Htree, Hbv, Hst⟩
        · rw [htxB]; iframe
        ihave Htb := Htback $$ Htree
        icases Htb with ⟨%M, %HM, Hpv, Hns⟩
        try wp_auto
        isplitl []
        · ipureintro; rfl
        isplitl [b]
        · iexact b
        iexists { B with ns := M, isrc := staleOf B.isrc }, _
        rw [htxB]
        iframe
        isplitr
        · ipureintro; exact own_step B S M ⟨p, top, hup, hpnd, hk, hpS⟩ HM
        iapply pageOwn_stale; iexact Hpo
    have hRm0 := derefM_refl (GMap.delete x bs)
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply wp_map_for_range (fun (keys : List GoString) (i : Int) => iprop(∃ (R : GMap Loc BRec)
        (st2 : TxStats) (cv : Loc),
        "%Hi" ∷ ⌜0 ≤ i ∧ derefM (GMap.delete x bs) R ∧ ∀ (k : Nat) name c, k < i.toNat →
          keys[k]? = some name → B.bm !! name = some c → derefFrom (GMap.delete x bs) R c⌝ ∗
        "HR" ∷ ([∗map] bl ↦ B ∈ R, bktOwn W bl B) ∗
        "Hst" ∷ structFieldRef Tx go!"stats" txl ↦ st2 ∗
        "Hpv" ∷ pagesView W.data W.ps W.q W.pages ∗
        "child" ∷ child_ptr ↦ cv)) $$ Hbm
    iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
    isplitl [Hbs Hst Hpv child]
    · iexists (GMap.delete x bs), st1, _
      iframe
      ipureintro
      exact ⟨Int.le_refl _, hRm0, fun k _ _ hk _ _ => by simp at hk⟩
    isplitr
    · imodintro
      iintro %i %key %c ⟨%Hkey, %Hc⟩ HP
      iNamed HP
      obtain ⟨Hi0, HRm, Hdone⟩ := Hi
      obtain ⟨hcx, hdR, hrdR, htxR⟩ := child_pre dep txl x bs R B key c hB hdep hready htx HRm Hc
      obtain ⟨-, hdep0, -, -⟩ := child_pre dep txl x bs (GMap.delete x bs) B key c hB hdep hready htx
        hRm0 Hc
      try wp_auto
      wp_apply ih c R st2 (by omega) hdR hrdR htxR $$ [HR Hst Hpv] as ⟨%R', %st3, %HR', HR, Hst, Hpv⟩
      · iframe
      try wp_auto
      obtain ⟨hM', hF', hprev⟩ := child_post dep (GMap.delete x bs) R R' c hdep0 HRm HR'.1 HR'.2
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists R', st3, c
      iframe
      ipureintro
      refine ⟨by omega, hM', fun k name c' hk hkn hc' => ?_⟩
      by_cases e : k = i.toNat
      · subst e; rw [Hkey] at hkn; cases hkn; rw [Hc] at hc'; cases hc'; exact hF'
      · exact hprev c' (Hdone k name c' (by omega) hkn hc')
    iintro HP Hbm
    iNamed HP
    obtain ⟨Hi0, HRm, Hdone⟩ := Hi
    have hall : ∀ name c, B.bm !! name = some c → derefFrom (GMap.delete x bs) R c := by
      intro name c hc
      have hmem : name ∈ keys := (Hkset name).2 (by rw [hc]; rfl)
      obtain ⟨k, hk, hkn⟩ := List.getElem_of_mem hmem
      exact Hdone k name c (by omega) (by rw [List.getElem?_eq_getElem hk, hkn]) hc
    obtain ⟨hM, hF⟩ := final dep x bs R B B1 hB hdep HB1 HRm hall
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
    · ipureintro; exact ⟨hM, hF⟩
    iframe
    iapply (BigSepM.bigSepM_insert (M := GMap Loc) (Φ := fun bl B => bktOwn (GF := GF) W bl B)
      (show Std.get? R x = none from hRx)).2
    iframe
    unfold bktOwn
    obtain ⟨e1, e2, e3, e4, -⟩ := HB1
    rw [e1, e2, e3, e4]
    iframe

theorem Bucket.dereference.wp_proof (hroot : node.root.spec (GF := GF) (hG := hG))
    (hnd : node.dereference.wspec (GF := GF) (hG := hG)) :
    Bucket.dereference.spec (GF := GF) (hG := hG) := by
  intro W txl T hready hc htx
  obtain ⟨dep, hdep, hrd⟩ := top_pre T _ hready
  iintro %Φ Hpre HΦ
  iapply (deref_rec hroot hnd W hc txl dep (dep (structFieldRef Tx go!"root" txl) + 1) _ T.bs
    T.t.stats' (Nat.lt_succ_self _) hdep hrd htx) $$ Hpre
  inext
  iintro ⟨%bs', %st', %H, Hbs, Hst, Hpv⟩
  iapply HΦ
  iexists { T with bs := bs', t := { T.t with stats' := st' } }
  iframe
  ipureintro; exact top_post T _ bs' st' hready H.1 H.2

end proof

end bbolt
end EtcdGrove
end Perennial
