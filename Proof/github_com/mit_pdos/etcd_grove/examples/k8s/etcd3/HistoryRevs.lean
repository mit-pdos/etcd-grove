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
public import Perennial.Spec.slices.Sort

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

theorem hr_mem_take_succ {α : Type} {L : List α} {k : Nat} {a : α} (h : L[k]? = some a) {e : α}
    (he : e ∈ L.take (k + 1)) : e ∈ L.take k ∨ e = a := by
  rw [List.take_add_one, h] at he
  simpa using he

theorem take_succ_req {xs : List (Input × Output)} {j j' : Nat} {x : Input} {y : Output}
    {Pj Q : w64 → Prop} (hPj : (fun u => ∃ p ∈ xs.take j, OpReq p.1 p.2 u) = Pj)
    (hjx : xs.take j' = xs.take j ++ [(x, y)]) (hQ : ∀ u, Pj u → Q u)
    (hO : ∀ u, OpReq x y u → Q u) : ∀ u, (∃ p ∈ xs.take j', OpReq p.1 p.2 u) → Q u := by
  rintro u ⟨p, hp, hr⟩
  rw [hjx, List.mem_append, List.mem_singleton] at hp
  rcases hp with hp | rfl
  · exact hQ u (hPj ▸ ⟨p, hp, hr⟩)
  · exact hO u hr

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

theorem allSt_mono0 (am bm : GoMap) {P Q : w64 → Prop} (hq : ∀ u, Q u → P u ∨ u = 0) :
    allSt (GF := GF) am bm P ⊢ allSt am bm Q := by
  unfold allSt
  iintro ⟨%A, %B, HA, HB, HBs, %HG⟩
  iexists A, B
  iframe
  ipureintro
  refine ⟨HG.1, fun u hu => ?_⟩
  rcases hq u hu with h | h
  · exact HG.2 u h
  · exact Or.inl h

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
    wp_if_destruct
    · have hK := Hif
      wp_join iprop(in_ptr ↦ x ∗ out_ptr ↦ y ∗ allSt am bm (fun u => P2 u ∨ (y.WFailed' = false ∧
          ∃ evs, decWEventsL y.WEvents' = some evs ∧ ∃ e ∈ evs, e.t < 4 ∧ e.o.ResourceVersion' = u)))
          at next with [Hst «in» out] as ⟨«in», out, Hst⟩
      · (try wp_auto)
        wp_apply wp_decodeWEvents as %esl %ok Hd
        rcases hd : decWEventsL y.WEvents' with _ | evs <;> isimp only [hd] at Hd
        · icases Hd with %hok
          subst hok
          (try wp_auto)
          wp_join_done
          (try iframe)
          iapply (allSt_mono am bm (P := P2) (fun u hu => by simpa using hu))
          iexact Hst
        icases Hd with ⟨%hok, Hd⟩
        iunfold wevsOwnM at Hd
        icases Hd with ⟨%ws, Hws, %hws⟩
        subst hok hws
        (try wp_auto)
        cases hw : y.WFailed'
        rotate_left
        · (try wp_auto)
          wp_join_done
          (try iframe)
          iapply (allSt_mono am bm (P := P2) (fun u hu => by simpa using hu))
          iexact Hst
        (try wp_auto)
        ihave %Hwl := ownSlice_len $$ Hws
        irename «in» => Hin
        ihave Hst := allSt_mono am bm (Q := fun u => P2 u ∨
          ∃ e ∈ (ws.map wevOf).take (sint.nat (W64 0)), e.t < 4 ∧ e.o.ResourceVersion' = u)
          (fun u hu => hu.elim id (fun ⟨e, he, _⟩ => by
            rw [show sint.nat (W64 0) = 0 by word] at he; simp at he)) $$ Hst
        ihave HJ : (∃ (k : w64) (evv : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.WEvent),
            "i" ∷ i_ptr ↦ k ∗ "ev" ∷ ev_ptr ↦ evv ∗ "Hws" ∷ esl ↦* ws ∗
            "Hst" ∷ allSt am bm (fun u => P2 u ∨
              ∃ e ∈ (ws.map wevOf).take (sint.nat k), e.t < 4 ∧ e.o.ResourceVersion' = u) ∗
            "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z esl.len⌝ : IProp GF) $$ [i ev Hws Hst]
        · iexists W64 0, _
          iframe
          ipureintro
          constructor <;> word
        wp_for HJ
        wp_if_destruct
        · have Hb' : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z esl.len :=
            ⟨Hk.1, by first | exact Hif | exact dec_true Hif⟩
          list_elem ws (sint.nat k) as w
          simp only [Hb', _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index esl (sint.Z k) ws _ w Hk.1 $$ [Hws] as Hws
          · isplit
            · iexact Hws
            · ipureintro; exact Hw_lookup
          have hl : (ws.map wevOf)[sint.nat k]? = some (wevOf w) := by simp [Hw_lookup]
          have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
          have hstep : ∀ u, (P2 u ∨ ∃ e ∈ (ws.map wevOf).take (sint.nat (k + W64 1)),
                e.t < 4 ∧ e.o.ResourceVersion' = u) →
              (P2 u ∨ ∃ e ∈ (ws.map wevOf).take (sint.nat k), e.t < 4 ∧ e.o.ResourceVersion' = u) ∨
                (uint.nat w.Type' < 4 ∧ u = w.Obj'.ResourceVersion') := by
            intro u hu
            rcases hu with h | ⟨e, he, ht, hrv⟩
            · exact Or.inl (Or.inl h)
            rw [hk1] at he
            rcases hr_mem_take_succ hl he with he' | rfl
            · exact Or.inl (Or.inr ⟨e, he', ht, hrv⟩)
            · exact Or.inr ⟨ht, hrv.symm⟩
          (try wp_auto)
          wp_if_destruct
          · wp_apply Hnum' $$ Hst as Hst
            ihave Hst := allSt_mono am bm (fun u hu => (hstep u hu).imp id (fun h => h.2)) $$ Hst
            wp_for_post
            iframe
            iexists k + W64 1, w
            iframe
            ipureintro
            constructor <;> word
          (try wp_auto)
          wp_if_destruct
          · wp_apply Hobj' $$ Hst as Hst
            ihave Hst := allSt_mono am bm (fun u hu => (hstep u hu).imp id (fun h => h.2)) $$ Hst
            wp_for_post
            iframe
            iexists k + W64 1, w
            iframe
            ipureintro
            constructor <;> word
          · ihave Hst := allSt_mono am bm (fun u hu => (hstep u hu).elim id
              (fun h => absurd h.1 (by word))) $$ Hst
            wp_for_post
            iframe
            iexists k + W64 1, w
            iframe
            ipureintro
            constructor <;> word
        · have hge : ¬ sint.Z k < sint.Z esl.len := by first | exact Hif | exact dec_false Hif
          (try rw [decide_eq_false hge, if_pos (decide_eq_true rfl)])
          (try wp_auto)
          have hfull : (ws.map wevOf).take (sint.nat k) = ws.map wevOf :=
            List.take_of_length_le (by simp; word)
          wp_join_done
          (try iframe)
          iapply (allSt_mono am bm (P := fun u => P2 u ∨
            ∃ e ∈ (ws.map wevOf).take (sint.nat k), e.t < 4 ∧ e.o.ResourceVersion' = u)
            (fun u hu => hu.imp id (fun ⟨_, evs, he, h⟩ => by
            simp only [Option.some.injEq] at he; subst he; rw [hfull]; exact h)))
          iexact Hst
      wp_for_post
      iframe
      iexists j + W64 1, _, W
      iframe
      isplitl
      · have hfin : ∀ u, (∃ p ∈ xs.take (sint.nat (j + W64 1)), OpReq p.1 p.2 u) →
            P2 u ∨ (y.WFailed' = false ∧ ∃ evs, decWEventsL y.WEvents' = some evs ∧
              ∃ e ∈ evs, e.t < 4 ∧ e.o.ResourceVersion' = u) := by
          refine take_succ_req hPj hjx (fun u h => by rw [← hP2]; exact Or.inl (Or.inl (Or.inl h)))
            (fun u hu => ?_)
          rw [← hP2]
          rcases hu with h | h | h | ⟨hk5, _⟩
          · exact Or.inl (Or.inl (Or.inr h))
          · exact Or.inl (Or.inr h)
          · obtain ⟨_, hw, evs, he, e, hm, ht⟩ := h
            exact Or.inr ⟨hw, evs, he, e, hm, ht.1, ht.2⟩
          · exact absurd hK hk5
        iapply (allSt_mono am bm hfin)
        iexact Hst
      ipureintro
      constructor <;> word
    · have hK := Hif
      wp_apply Hnum' $$ Hst as Hst
      (try wp_auto)
      wp_apply Hnum' $$ Hst as Hst
      (try wp_auto)
      wp_apply wp_rvOfMsg
      (try wp_auto)
      ipersist r
      wp_join iprop(in_ptr ↦ x ∗ out_ptr ↦ y ∗ allSt am bm (fun u => ((P2 u ∨ u = y.ErrRV') ∨
          u = y.ListRV') ∨ u = rvOfMsgL y.ErrMsg')) at next with [Hst «in» out] as ⟨«in», out, Hst⟩
      · (try wp_auto)
        wp_if_destruct
        · (try wp_auto)
          wp_join_done
          (try iframe)
          iapply (allSt_mono0 am bm (P := fun u => (P2 u ∨ u = y.ErrRV') ∨ u = y.ListRV')
            (fun u hu => hu.imp id (fun h => h.trans Hif)))
          iexact Hst
        · (try wp_auto)
          wp_apply Hobj' $$ Hst as Hst
          (try wp_auto)
          wp_join_done
      generalize hP3 : (fun u => ((P2 u ∨ u = y.ErrRV') ∨ u = y.ListRV') ∨ u = rvOfMsgL y.ErrMsg') = P3
      wp_join iprop(in_ptr ↦ x ∗ out_ptr ↦ y ∗ (∃ W' : GMap w64 Bool, wm ↦$ W') ∗
          allSt am bm (fun u => P3 u ∨ (y.Err' = W64 0 ∧ u = y.RV')))
          at next with [Hst «in» out Hwm] as ⟨«in», out, ⟨%W1, Hwm⟩, Hst⟩
      · (try wp_auto)
        wp_if_destruct
        · (try wp_auto)
          wp_apply Hobj' $$ Hst as Hst
          (try wp_auto)
          ihave Hst := allSt_mono am bm (P := fun u => P3 u ∨ u = y.RV')
            (Q := fun u => P3 u ∨ (y.Err' = W64 0 ∧ u = y.RV')) (fun u hu => hu.imp id (fun h => h.2)) $$ Hst
          repeat' (wp_if_destruct <;> (try wp_auto))
          all_goals (try (cases hn : x.NoOp' <;> simp only [Bool.not_true, Bool.not_false] <;>
            (try wp_auto)))
          all_goals first
            | (wp_join_done; done)
            | (wp_apply (wp_mapInsert go.uint64 wm W y.RV' true) $$ Hwm as Hwm
               (try wp_auto)
               wp_join_done)
        · (try wp_auto)
          wp_join_done
          (try iframe)
          iapply (allSt_mono am bm (P := P3) (fun u hu => hu.elim id (fun h => absurd h.1 Hif)))
          iexact Hst
      generalize hP4 : (fun u => P3 u ∨ (y.Err' = W64 0 ∧ u = y.RV')) = P4
      have hfin : ∀ u, (∃ p ∈ xs.take (sint.nat (j + W64 1)), OpReq p.1 p.2 u) →
          P4 u ∨ (x.Kind' = W64 4 ∧ y.Err' = W64 0 ∧
            ∃ ds, decItemRVsL y.Items' = some ds ∧ ∃ d ∈ ds, d.ResourceVersion' = u) := by
        refine take_succ_req hPj hjx (fun u h => ?_) (fun u hu => ?_)
        · subst hP4 hP3 hP2
          exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))))
        subst hP4 hP3 hP2
        rcases hu with h | h | h | ⟨_, h | h | ⟨he, h⟩ | ⟨h4, he, os, hos, o, ho, hrv⟩ | ⟨o, hm, hb, hrv⟩⟩
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
        · exact absurd h.1 hK
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))
        · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
        · exact Or.inl (Or.inr ⟨he, h⟩)
        · obtain ⟨hs, hl⟩ := hok.2 h4 he
          rw [hos] at hs hl
          obtain ⟨ds, hds, hmap⟩ := decItemRVsL_encItemsL os hl hs
          have hm : u ∈ ds.map (·.ResourceVersion') := by
            rw [hmap]; exact List.mem_map.2 ⟨o, ho, hrv⟩
          obtain ⟨d, hd, hdu⟩ := List.mem_map.1 hm
          exact Or.inr ⟨h4, he, ds, hos ▸ hds, d, hd, hdu⟩
        · refine Or.inl (Or.inl (Or.inr ?_))
          rw [hm, rvOfMsgL_preMsgL x o hok.1 hb]
          exact hrv.symm
      (try wp_auto)
      wp_if_destruct
      rotate_left
      · (try wp_auto)
        wp_for_post
        iframe
        iexists j + W64 1, _, W1
        iframe
        isplitl
        · iapply (allSt_mono am bm (P := P4) (fun u hu => (fun u hu => hu.elim id (fun h => absurd h.1 Hif)) u (hfin u hu)))
          iexact Hst
        ipureintro
        constructor <;> word
      have hK4 := Hif
      (try wp_auto)
      wp_if_destruct
      rotate_left
      · (try wp_auto)
        wp_for_post
        iframe
        iexists j + W64 1, _, W1
        iframe
        isplitl
        · iapply (allSt_mono am bm (P := P4) (fun u hu => (fun u hu => hu.elim id (fun h => absurd h.2.1 Hif)) u (hfin u hu)))
          iexact Hst
        ipureintro
        constructor <;> word
      have hE0 := Hif
      (try wp_auto)
      wp_apply wp_decodeItemRVs as %isl %ok Hd
      rcases hd : decItemRVsL y.Items' with _ | ds <;> isimp only [hd] at Hd
      · icases Hd with %hok
        subst hok
        (try wp_auto)
        wp_for_post
        iframe
        iexists j + W64 1, _, W1
        iframe
        isplitl
        · iapply (allSt_mono am bm (P := P4) (fun u hu => (fun u hu => by simpa [hd] using hu) u (hfin u hu)))
          iexact Hst
        ipureintro
        constructor <;> word
      icases Hd with ⟨%hok, Hws⟩
      subst hok
      (try wp_auto)
      ihave %Hwl := ownSlice_len $$ Hws
      ihave Hst := allSt_mono am bm (Q := fun u => P4 u ∨
        ∃ e ∈ ds.take (sint.nat (W64 0)), e.ResourceVersion' = u)
        (fun u hu => hu.elim id (fun ⟨e, he, _⟩ => by
          rw [show sint.nat (W64 0) = 0 by word] at he; simp at he)) $$ Hst
      ihave HJ : (∃ (k : w64) (itv : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.item),
          "i" ∷ i_ptr ↦ k ∗ "it" ∷ it_ptr ↦ itv ∗
          "Hws" ∷ isl ↦* ds.map (fun o => github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.item.mk (objKeyL o) o false) ∗
          "Hst" ∷ allSt am bm (fun u => P4 u ∨
            ∃ e ∈ ds.take (sint.nat k), e.ResourceVersion' = u) ∗
          "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z isl.len⌝ : IProp GF) $$ [i it Hws Hst]
      · iexists W64 0, _
        iframe
        ipureintro
        constructor <;> word
      wp_for HJ
      wp_if_destruct
      · have Hb' : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z isl.len :=
          ⟨Hk.1, by first | exact Hif | exact dec_true Hif⟩
        have hkl : sint.nat k < ds.length := by simp at Hwl; word
        have hl : ds[sint.nat k]? = some ds[sint.nat k] := List.getElem?_eq_getElem hkl
        generalize ds[sint.nat k] = d at hl
        simp only [Hb', _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index isl (sint.Z k) _ _ (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.item.mk (objKeyL d) d false) Hk.1 $$ [Hws]
          as Hws
        · isplit
          · iexact Hws
          · ipureintro; simp [hl]
        have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
        have hstep : ∀ u, (P4 u ∨ ∃ e ∈ ds.take (sint.nat (k + W64 1)), e.ResourceVersion' = u) →
            (P4 u ∨ ∃ e ∈ ds.take (sint.nat k), e.ResourceVersion' = u) ∨ u = d.ResourceVersion' := by
          intro u hu
          rcases hu with h | ⟨e, he, hrv⟩
          · exact Or.inl (Or.inl h)
          rw [hk1] at he
          rcases hr_mem_take_succ hl he with he' | rfl
          · exact Or.inl (Or.inr ⟨e, he', hrv⟩)
          · exact Or.inr hrv.symm
        (try wp_auto)
        wp_apply Hobj' $$ Hst as Hst
        ihave Hst := allSt_mono am bm hstep $$ Hst
        wp_for_post
        iframe
        iexists k + W64 1, _
        iframe
        ipureintro
        constructor <;> word
      · have hge : ¬ sint.Z k < sint.Z isl.len := by first | exact Hif | exact dec_false Hif
        (try rw [decide_eq_false hge, if_pos (decide_eq_true rfl)])
        (try wp_auto)
        have hfull : ds.take (sint.nat k) = ds := List.take_of_length_le (by simp at Hwl; word)
        wp_for_post
        iframe
        iexists j + W64 1, _, W1
        iframe
        isplitl
        · iapply (allSt_mono am bm (P := fun u => P4 u ∨
          ∃ e ∈ ds.take (sint.nat k), e.ResourceVersion' = u) (fun u hu => (fun u hu => hu.imp id (fun ⟨_, _, ds', he, h⟩ => by
            rw [hd] at he; simp only [Option.some.injEq] at he; subst he; rw [hfull]; exact h)) u (hfin u hu)))
          iexact Hst
        ipureintro
        constructor <;> word
  · have hge : ¬ sint.Z j < sint.Z sl.len := by first | exact Hif | exact dec_false Hif
    have hfull : xs.take (sint.nat j) = xs := List.take_of_length_le (by rw [← Hops.length_eq, Hlen.1]; word)
    unfold allSt
    icases Hst with ⟨%A, %B, HA, HB, HBs, %HG⟩
    rw [hfull] at HG
    iStructNamed r
    -- WIP (K9-16): the tail (collect `A`'s keys, `slices.Sort`, the `byKey` loops). Blocked on a size
    -- bound `slices.Sort` needs (`notes/specs-only/ledger.md`, 2026-11-28, `HistoryRevs.spec`).
    sorry

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
