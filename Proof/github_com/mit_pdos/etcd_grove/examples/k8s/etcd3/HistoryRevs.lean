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

theorem hr_forall₂_getElem {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 →
      ∀ i (h1 : i < l1.length) (h2 : i < l2.length), R l1[i] l2[i]
  | _, _, .cons h _, 0, _, _ => h
  | _, _, .cons _ t, i + 1, h1, h2 =>
    hr_forall₂_getElem t i (by simpa using h1) (by simpa using h2)

/-- `A`'s keys are nonzero and it holds every nonzero `u` with `P u`. -/
def Good (P : w64 → Prop) (A : GMap w64 Bool) : Prop :=
  (∀ k, (A !! k).isSome → k ≠ 0) ∧ ∀ u, P u → u = 0 ∨ (A !! u).isSome

theorem good_mono {P Q : w64 → Prop} {A : GMap w64 Bool} (h : Good P A) (hq : ∀ u, Q u → P u) :
    Good Q A :=
  ⟨h.1, fun u hu => h.2 u (hq u hu)⟩

theorem good_ite {P : w64 → Prop} {A : GMap w64 Bool} (v : w64) (h : Good P A) :
    Good (fun u => P u ∨ u = v) (if v = W64 0 then A else <[v := true]> A) := by
  obtain ⟨hnz, hc⟩ := h
  by_cases hv : v = W64 0
  · rw [if_pos hv]
    refine ⟨hnz, fun u hu => hu.elim (hc u) (fun h => Or.inl ?_)⟩
    rw [h, hv]; rfl
  · rw [if_neg hv]
    refine ⟨fun k hk => ?_, fun u hu => ?_⟩
    · rcases (GMap.lookup_insert_is_Some A v k true).1 hk with rfl | ⟨_, hk⟩
      · exact hv
      · exact hnz k hk
    · rcases hu with hu | rfl
      · rcases hc u hu with h0 | hs
        · exact Or.inl h0
        · right
          exact (GMap.lookup_insert_is_Some A v u true).2 (by by_cases h : v = u <;> simp_all)
      · right; rw [GMap.lookup_insert]; rfl

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- The maps `all` (`am`) and `byKey` (`bm`), `all` holding every nonzero `u` with `P u`. -/
def allSt (am bm : GoMap) (P : w64 → Prop) : IProp GF :=
  iprop(∃ (A : GMap w64 Bool) (B : GMap GoString GoMap), am ↦$ A ∗ bm ↦$ B ∗
    ([∗map] _k ↦ l ∈ B, ∃ m : GMap w64 Bool, l ↦$ m) ∗ ⌜Good P A⌝)

theorem allSt_mono (am bm : GoMap) {P Q : w64 → Prop} (hq : ∀ u, Q u → P u) :
    allSt (GF := GF) am bm P ⊢ allSt am bm Q := by
  unfold allSt
  iintro ⟨%A, %B, HA, HB, HBs, %HG⟩
  iexists A, B
  iframe
  ipureintro
  exact good_mono HG hq

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
  ihave #Hnum' : iprop(∀ (v : w64) (P : w64 → Prop),
      {{ allSt am bm P }} (App (Val #fn) (Val #v)) {{ RET #(); allSt am bm (fun u => P u ∨ u = v) }}) $$ []
  · iintro %v %P !> %Φ' Hst HΦ'
    unfold allSt
    icases Hst with ⟨%A, %B, HA, HB, HBs, %HG⟩
    wp_apply Hnum $$ HA as HA
    iapply HΦ'
    iexists _, B
    iframe
    ipureintro
    exact good_ite v HG
  ihave #Hobj' : iprop(∀ (key : GoString) (v : w64) (P : w64 → Prop),
      {{ allSt am bm P }} (App (App (Val #fo) (Val #key)) (Val #v))
      {{ RET #(); allSt am bm (fun u => P u ∨ u = v) }}) $$ []
  · iintro %key %v %P !> %Φ' Hst HΦ'
    unfold allSt
    icases Hst with ⟨%A, %B, HA, HB, HBs, %HG⟩
    wp_apply Hobj $$ [$HA $HB $HBs] as ⟨HA, %B', HB, HBs⟩
    iapply HΦ'
    iexists _, B'
    iframe
    ipureintro
    exact good_ite v HG
  iclear Hnum Hobj
  clear hfn hfo
  ipersist obj
  ipersist num
  ipersist written
  ihave %Hlen := ownSlice_len $$ Hs
  ihave HI : (∃ (j : w64) (opv : github_com.anishathalye.porcupine.Operation) (W : GMap w64 Bool),
      "i" ∷ i_ptr ↦ j ∗ "op" ∷ op_ptr ↦ opv ∗ "Hwm" ∷ wm ↦$ W ∗
      "Hst" ∷ allSt am bm (fun u => ∃ p ∈ xs.take (sint.nat j), OpReq p.1 p.2 u) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len⌝ : IProp GF) $$ [i op Hwm Ham Hbm]
  · iexists W64 0, _, _
    iframe
    isplitl
    · unfold allSt
      iexists ∅, ∅
      iframe
      isplitl
      · iapply BigSepM.bigSepM_empty.2
        itrivial
      ipureintro
      refine ⟨fun k hk => by simp at hk, fun u hu => ?_⟩
      obtain ⟨p, hp, _⟩ := hu
      rw [show sint.nat (W64 0) = 0 by word] at hp
      simp at hp
    ipureintro
    constructor <;> word
  wp_for HI
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len :=
      ⟨Hj.1, by first | exact Hif | exact dec_true Hif⟩
    have h1 : sint.nat j < ops.length := by rw [Hlen.1]; word
    have h2 : sint.nat j < xs.length := Hops.length_eq ▸ h1
    have hR := hr_forall₂_getElem Hops (sint.nat j) h1 h2
    have hjx : xs.take (sint.nat (j + W64 1)) = xs.take (sint.nat j) ++ [xs[sint.nat j]] := by
      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one,
        List.getElem?_eq_getElem h2]
      rfl
    have hok := Hok _ (List.getElem_mem h2)
    generalize xs[sint.nat j] = pj at hR hjx hok
    obtain ⟨x, y⟩ := pj
    simp only [Hb', _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z j) ops dq (ops[sint.nat j]) Hj.1 $$ [Hs] as Hs
    · isplit
      · iexact Hs
      · ipureintro; exact List.getElem?_eq_getElem h1
    (try wp_auto)
    rw [hR.1]
    (try wp_auto)
    rw [hR.2]
    (try wp_auto)
    generalize hPj : (fun u => ∃ p ∈ xs.take (sint.nat j), OpReq p.1 p.2 u) = Pj
    wp_join iprop(in_ptr ↦ x ∗ out_ptr ↦ y ∗ allSt am bm (fun u => Pj u ∨
        parseRVD x.MinRV' = some u)) at next with [Hst «in» out] as ⟨«in», out, Hst⟩
    · wp_apply wp_parseRV as %n %err Hp
      rcases hd : parseRVD x.MinRV' with _ | m <;> isimp only [hd] at Hp
      · icases Hp with ⟨%hne, -, %h0⟩
        obtain ⟨ei, rfl⟩ : ∃ ei, err = GoInterface.ok ei := by cases err <;> simp_all
        (try wp_auto)
        wp_join_done
        (try iframe)
        iapply (allSt_mono am bm (P := Pj)
          (fun u hu => by simpa using hu))
        iexact Hst
      · icases Hp with %h
        obtain ⟨rfl, rfl⟩ := h
        (try wp_auto)
        wp_apply Hnum' $$ Hst as Hst
        (try wp_auto)
        wp_join_done
        (try iframe)
        iapply (allSt_mono am bm (P := fun u => Pj u ∨ u = n)
          (fun u hu => by simpa [eq_comm] using hu))
        iexact Hst
    wp_join iprop(in_ptr ↦ x ∗ out_ptr ↦ y ∗ allSt am bm (fun u => (Pj u ∨
        parseRVD x.MinRV' = some u) ∨ (x.HasPreRV' = true ∧ parseRVD x.PreRV' = some u)))
        at next with [Hst «in» out] as ⟨«in», out, Hst⟩
    · (try wp_auto)
      wp_apply wp_parseRV as %n %err Hp
      rcases hd : parseRVD x.PreRV' with _ | m <;> isimp only [hd] at Hp
      · icases Hp with ⟨%hne, -, %h0⟩
        obtain ⟨ei, rfl⟩ : ∃ ei, err = GoInterface.ok ei := by cases err <;> simp_all
        (try wp_auto)
        cases hb : x.HasPreRV' <;> (try wp_auto) <;> wp_join_done <;>
          (try iframe) <;>
          iapply (allSt_mono am bm (P := fun u => Pj u ∨
            parseRVD x.MinRV' = some u) (fun u hu => by simpa using hu)) <;> iexact Hst
      · icases Hp with %h
        obtain ⟨rfl, rfl⟩ := h
        (try wp_auto)
        cases hb : x.HasPreRV'
        · (try wp_auto)
          wp_join_done
          (try iframe)
          iapply (allSt_mono am bm (P := fun u => Pj u ∨
            parseRVD x.MinRV' = some u) (fun u hu => by simpa using hu))
          iexact Hst
        · (try wp_auto)
          wp_apply Hnum' $$ Hst as Hst
          (try wp_auto)
          wp_join_done
          (try iframe)
          iapply (allSt_mono am bm (P := fun u => (Pj u ∨
            parseRVD x.MinRV' = some u) ∨ u = n) (fun u hu => by simpa [eq_comm] using hu))
          iexact Hst
    generalize hP2 : (fun u => (Pj u ∨ parseRVD x.MinRV' = some u) ∨
      (x.HasPreRV' = true ∧ parseRVD x.PreRV' = some u)) = P2
    wp_join iprop(in_ptr ↦ x ∗ out_ptr ↦ y ∗ allSt am bm P2)
        at next with [Hst «in» out] as ⟨«in», out, Hst⟩
    · (try wp_auto)
      cases hc : x.UseCached'
      · (try wp_auto)
        wp_join_done
      · (try wp_auto)
        wp_apply Hobj' $$ Hst as Hst
        (try wp_auto)
        wp_join_done
        (try iframe)
        iapply (allSt_mono am bm (P := fun u => P2 u ∨ u = x.Cached'.ResourceVersion')
          (fun u hu => Or.inl hu))
        iexact Hst
    sorry
  · sorry

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
