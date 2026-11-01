/-
`n.children = nil` in `node.spill` (after its children loop): the cut. The node's children (all
spilled parts) leave the bucket's nodes (`cutNs`), but for those on the root node's parent chain
(a split root's old parts, kept as they are with the view's bytes forgotten: `staleRec`, so that
a remap, which does not reach them, keeps them).
-/
module

public import Proof.go_etcd_io.bbolt.SpillNodeLoop

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

/-- `c` is on the root node's parent chain. -/
def onRootPath (B : BRec) (c : Loc) : Bool :=
  @decide (∃ p t, upPath B.ns B.bv.rootNode' p t ∧ c ∈ p) (Classical.propDecidable _)

/-- The nodes `ns` without the nodes `cs`, but those to `keep` (without the view's bytes). -/
def cutNs (ns : GMap Loc NRec) (keep : Loc → Bool) : List Loc → GMap Loc NRec
  | [] => ns
  | c :: cs =>
    let m := cutNs ns keep cs
    if keep c then
      match m !! c with
      | some r => <[c := staleRec r]> m
      | none => m
    else GMap.delete c m

theorem cutNs_lookup (ns : GMap Loc NRec) (keep : Loc → Bool) :
    ∀ (cs : List Loc), cs.Nodup → ∀ l, cutNs ns keep cs !! l =
      if l ∈ cs then (if keep l then (ns !! l).map staleRec else none) else ns !! l
  | [], _, l => by simp [cutNs]
  | c :: cs, hnd, l => by
    obtain ⟨hc, hnd'⟩ := List.nodup_cons.1 hnd
    have ih := cutNs_lookup ns keep cs hnd'
    have hmc : cutNs ns keep cs !! c = ns !! c := by rw [ih c, if_neg hc]
    simp only [cutNs]
    by_cases hk : keep c = true
    · rw [if_pos hk]
      cases hm : cutNs ns keep cs !! c with
      | none =>
        simp only
        rw [ih l]
        by_cases e : l = c
        · subst e; rw [if_neg hc, if_pos List.mem_cons_self, if_pos hk, ← hmc, hm]; rfl
        · simp [e]
      | some r =>
        simp only
        by_cases e : l = c
        · subst e; rw [GMap.lookup_insert, if_pos List.mem_cons_self, if_pos hk, ← hmc, hm]; rfl
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm e), ih l]; simp [e]
    · rw [if_neg hk]
      by_cases e : l = c
      · subst e; rw [GMap.lookup_delete, if_pos List.mem_cons_self, if_neg hk]
      · rw [GMap.lookup_delete_ne _ (Ne.symm e), ih l]; simp [e]

end pure

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- A node dropped from a map. -/
theorem bigSepM_drop {V : Type} (Φ : Loc → V → IProp GF) (m : GMap Loc V) (c : Loc) :
    ([∗map] l ↦ v ∈ m, Φ l v) ⊢ [∗map] l ↦ v ∈ GMap.delete c m, Φ l v := by
  cases h : m !! c with
  | none =>
    have e : GMap.delete c m = m := by
      apply GMap.ext; intro l
      by_cases e : l = c
      · subst e; rw [GMap.lookup_delete, h]
      · rw [GMap.lookup_delete_ne _ (Ne.symm e)]
    rw [e]
  | some v =>
    iintro H
    icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := Φ) (show Std.get? m c = some v from h)).1 $$ H
      with ⟨-, H⟩
    iexact H

/-- The cut, of a map of nodes. -/
theorem bigSepM_cut (Φ : Loc → NRec → IProp GF)
    (hst : ∀ l r, Φ l r ⊢ Φ l (staleRec r)) (ns : GMap Loc NRec) (keep : Loc → Bool) :
    ∀ cs : List Loc, ([∗map] l ↦ v ∈ ns, Φ l v) ⊢ [∗map] l ↦ v ∈ cutNs ns keep cs, Φ l v
  | [] => .rfl
  | c :: cs => by
    refine (bigSepM_cut Φ hst ns keep cs).trans ?_
    simp only [cutNs]
    split
    · split
      · rename_i r hr
        iintro H
        icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := Φ)
          (show Std.get? (cutNs ns keep cs) c = some r from hr)).1 $$ H with ⟨Hc, H⟩
        iapply (BigSepM.bigSepM_insert_delete (M := GMap Loc) (Φ := Φ)).2
        iframe H
        iapply hst; iexact Hc
      · exact .rfl
    · exact bigSepM_drop Φ _ c

/-- The cut, of the spill state. -/
theorem spillR_cut (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (txl : Loc)
    (txid : w64) (T : WTx) (ρ : DBState) (F : GMap Nat (List w8)) (K : Loc → Bool) (bl : Loc)
    (B : BRec) (keep : Loc → Bool) (cs : List Loc) (hB : T.bs !! bl = some B) (hnd : cs.Nodup) :
    spillR I γd γ W txl txid T ρ F K ⊢
      spillR I γd γ W txl txid (setB T bl { B with ns := cutNs B.ns keep cs }) ρ F K := by
  iintro HR
  icases spillR_bkt I γd γ W txl txid T ρ F K bl B hB $$ HR with ⟨Hb, Hc, Hback⟩
  ihave Hb' : bktOwnX W bl { B with ns := cutNs B.ns keep cs } $$ [Hb]
  · isimp only [bktOwnX] at Hb
    icases Hb with ⟨Hbv, Hib, Hnm, Hbm, Hpo, Hns⟩
    unfold bktOwnX
    rw [show pageOwn W { B with ns := cutNs B.ns keep cs } = pageOwn W B from rfl]
    iframe Hbv Hib Hnm Hbm Hpo
    iapply bigSepM_cut (fun l r => nodeOwnX (GF := GF) W l r) (nodeOwnX_stale W) B.ns keep cs
    iexact Hns
  ihave Hc' : capsKN K ({ B with ns := cutNs B.ns keep cs } : BRec).ns $$ [Hc]
  · unfold capsKN
    iapply bigSepM_cut (fun l r => if K l then iprop(emp) else capOwn (GF := GF) r)
      (fun l r => by unfold capOwn staleRec; exact .rfl) B.ns keep cs
    iexact Hc
  iapply Hback $$ %({ B with ns := cutNs B.ns keep cs }) %K %(fun l h => absurd rfl h) Hb' Hc'

end own

end bbolt
end EtcdGrove
end Perennial
