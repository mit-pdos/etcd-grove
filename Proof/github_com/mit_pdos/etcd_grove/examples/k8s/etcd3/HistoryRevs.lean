/- Lean-first (no Rocq counterpart).

`HistoryRevs`' proof (notes/k8s-dist-k9.md §2.7, step 4).

- `OpReq x y u`: `u` is a revision `OpAnchors` asks of the operation `(x, y)`; `opAnchors_of`: an
  anchor list holding every such `u` satisfies `OpAnchors`.
- The ops loop keeps `∀ p ∈ xs.take j, ∀ u, OpReq p.1 p.2 u → u = 0 ∨ (A !! u).isSome` for the
  map `all` (`A`), whose keys are nonzero; `num(v)` and `obj(k, v)` both add `v` to it (`obj` also
  to `byKey`, whose contents the spec does not constrain).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.HistoryRevs
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.rvOfMsg
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.parseRV
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.decodeWEvents
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.decodeItemRVs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj Revs)

section pure
variable [GooseExts]

/-- `u` is a revision `OpAnchors` asks of `(x, y)` (see the file header). -/
def OpReq (x : Input) (y : Output) (u : w64) : Prop :=
  parseRVD x.MinRV' = some u ∨ (x.HasPreRV' = true ∧ parseRVD x.PreRV' = some u) ∨
  (x.Kind' = W64 5 ∧ y.WFailed' = false ∧ ∃ evs, decWEventsL y.WEvents' = some evs ∧
    ∃ e ∈ evs, e.t < 4 ∧ e.o.ResourceVersion' = u) ∨
  (x.Kind' ≠ W64 5 ∧ (u = y.ErrRV' ∨ u = y.ListRV' ∨ (y.Err' = W64 0 ∧ u = y.RV') ∨
    (x.Kind' = W64 4 ∧ y.Err' = W64 0 ∧ ∃ os : List Obj, y.Items' = encItemsL os ∧
      ∃ o ∈ os, o.ResourceVersion' = u) ∨
    (∃ o : Obj, y.ErrMsg' = preMsgL x o ∧ (x.HasPreUID' && !decide (x.PreUID' = o.UID')) = false ∧
      o.ResourceVersion' = u)))

theorem opAnchors_of (A : List Nat) (x : Input) (y : Output)
    (h : ∀ u, OpReq x y u → uint.nat u ∈ A) : k8s_dist.OpAnchors A x y := by
  unfold k8s_dist.OpAnchors
  refine ⟨fun r hr => h r (Or.inl hr), fun r h1 h2 => h r (Or.inr (Or.inl ⟨h1, h2⟩)),
    fun hk hw evs hevs e he ht => h _ (Or.inr (Or.inr (Or.inl ⟨hk, hw, evs, hevs, e, he, ht, rfl⟩))),
    fun hk => ⟨h _ (Or.inr (Or.inr (Or.inr ⟨hk, Or.inl rfl⟩))),
      h _ (Or.inr (Or.inr (Or.inr ⟨hk, Or.inr (Or.inl rfl)⟩))),
      fun he => h _ (Or.inr (Or.inr (Or.inr ⟨hk, Or.inr (Or.inr (Or.inl ⟨he, rfl⟩))⟩))),
      fun h4 he os hos o ho =>
        h _ (Or.inr (Or.inr (Or.inr ⟨hk, Or.inr (Or.inr (Or.inr (Or.inl ⟨h4, he, os, hos, o, ho, rfl⟩)))⟩))),
      fun o hm hb =>
        h _ (Or.inr (Or.inr (Or.inr ⟨hk, Or.inr (Or.inr (Or.inr (Or.inr ⟨o, hm, hb, rfl⟩)))⟩)))⟩⟩

/-- **The anchors from `all`'s keys** (the loop's invariant at its end, and the keys collected in
`anchors`) give `AnchorsOk`. -/
theorem anchorsOk_of (A : GMap w64 Bool) (l : List w64) (xs : List (Input × Output))
    (hl : ∀ k, k ∈ l ↔ (A !! k).isSome)
    (h : ∀ p ∈ xs, ∀ u, OpReq p.1 p.2 u → u = 0 ∨ (A !! u).isSome) :
    k8s_dist.AnchorsOk (0 :: l.map uint.nat) xs := by
  refine ⟨List.mem_cons_self .., fun p hp => opAnchors_of _ _ _ fun u hu => ?_⟩
  rcases h p hp u hu with rfl | hs
  · exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ (List.mem_map_of_mem ((hl u).2 hs))

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem HistoryRevs.wp_proof (wp_parseRV : parseRV.spec (GF := GF) (hG := hG))
    (wp_rvOfMsg : rvOfMsg.spec (GF := GF) (hG := hG))
    (wp_decodeWEvents : decodeWEvents.spec (GF := GF) (hG := hG))
    (wp_decodeItemRVs : decodeItemRVs.spec (GF := GF) (hG := hG)) :
    HistoryRevs.spec (GF := GF) (hG := hG) := by
  intro sl ops xs dq Hops Hok
  wp_start as Hs
  wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := Bool)) as %am Ham
  (try wp_auto)
  wp_apply (wp_map_make1 (K := GoString) (V := GoMap)) as %bm Hbm
  (try wp_auto)
  wp_apply (wp_map_make1 (K := w64) (V := Bool)) as %wm Hwm
  (try wp_auto)
  ipersist all
  ipersist byKey
  generalize hfn : (func.mk BAnon (BNamed "rv") _ : GoFunc) = fn at *
  generalize hfo : (func.mk BAnon (BNamed "key") _ : GoFunc) = fo at *
  ihave #Hnum : iprop(∀ (v : w64) (A : GMap w64 Bool),
      {{ am ↦$ A }} (App (Val #fn) (Val #v))
      {{ RET #(); am ↦$ (if v = W64 0 then A else <[v := true]> A) }}) $$ []
  · iintro %v %A !> %Φ' HA HΦ'
    rw [← hfn, ← recv_eq_func_mk]
    wp_auto
    wp_if_destruct
    · iapply HΦ'
      iframe
    · wp_apply (wp_mapInsert go.uint64 am A v true) $$ HA as HA
      (try wp_auto)
      iapply HΦ'
      rw [if_neg Hif]
      iframe
  ihave #Hobj : iprop(∀ (key : GoString) (v : w64) (A : GMap w64 Bool) (B : GMap GoString GoMap),
      {{ am ↦$ A ∗ bm ↦$ B ∗ [∗map] _k ↦ l ∈ B, ∃ m : GMap w64 Bool, l ↦$ m }}
        (App (App (Val #fo) (Val #key)) (Val #v))
      {{ RET #(); am ↦$ (if v = W64 0 then A else <[v := true]> A) ∗
          ∃ B' : GMap GoString GoMap, bm ↦$ B' ∗ [∗map] _k ↦ l ∈ B', ∃ m : GMap w64 Bool, l ↦$ m }}) $$ []
  · iintro %key %v %A %B !> %Φ' ⟨HA, HB, HBs⟩ HΦ'
    rw [← hfo, ← recv_eq_func_mk]
    wp_auto
    wp_if_destruct
    · (try wp_auto)
      iapply HΦ'
      iframe
    wp_apply (wp_mapInsert go.uint64 am A v true) $$ HA as HA
    (try wp_auto)
    wp_apply (wp_map_lookup1 go.string (go.uint64.MapType go.bool) bm B key) $$ HB as HB
    (try wp_auto)
    rcases hBk : B !! key with _ | l0
    · rw [show ((none : Option GoMap).getD (zero_val GoMap)) = map.nil from rfl,
        decide_eq_true rfl]
      (try wp_auto)
      wp_apply (wp_map_make1 (K := w64) (V := Bool)) as %l1 Hl1
      (try wp_auto)
      wp_apply (wp_mapInsert go.string bm B key l1) $$ HB as HB
      (try wp_auto)
      wp_apply (wp_map_lookup1 go.string (go.uint64.MapType go.bool) bm _ key) $$ HB as HB
      (try rw [GMap.lookup_insert])
      (try wp_auto)
      wp_apply (wp_mapInsert go.uint64 l1 _ v true) $$ Hl1 as Hl1
      (try wp_auto)
      iapply HΦ'
      rw [if_neg Hif]
      iframe
      iapply (BigSepM.bigSepM_insert (Φ := fun (_ : GoString) (l : GoMap) =>
        iprop(∃ m : GMap w64 Bool, ownMap (GF := GF) l (DFrac.own 1) m)) hBk).2
      iframe
    · ihave ⟨⟨%m0, Hl0⟩, HBs⟩ := (BigSepM.bigSepM_lookup_acc hBk).1 $$ HBs
      ihave %Hl0nn := ownMap_not_nil $$ Hl0
      rw [show ((some l0).getD (zero_val GoMap)) = l0 from rfl, decide_eq_false Hl0nn]
      (try wp_auto)
      wp_apply (wp_map_lookup1 go.string (go.uint64.MapType go.bool) bm B key) $$ HB as HB
      rw [hBk, Option.getD_some]
      (try wp_auto)
      wp_apply (wp_mapInsert go.uint64 l0 m0 v true) $$ Hl0 as Hl0
      (try wp_auto)
      iapply HΦ'
      rw [if_neg Hif]
      iframe
      iapply HBs
      iexists _
      iframe
  sorry

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
