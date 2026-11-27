/-
Helpers of `Model()` (kit.go) for its proof against the key-value store's porcupine model spec `kvS`
(notes/dsv-craq.md, P2, P4): the state's helpers over read-only maps and slices of `pend`, `step`
(`wp_step`: `goStep` of the decoded answer), `kvDec` on boxed values (`kvDec_box`), `Model.spec`;
and the store's decoding facts remote's `Check` needs (`kvS_pendDec`, `kvR_encOut_inj`; finding F4).

Proved: `pushPend`, `copyMap`, `set`, `findPend`, `erasePend`, `step`. `ModelProof.lean` proves
`Model.wp_proof`.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.Kit

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace github_com.despreston.go_craq.examples.craqnet

open EtcdGrove EtcdGrove.linkv github_com.mit_pdos.etcd_grove.examples.lib.remote

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.despreston.go_craq.examples.craqnet.Assumptions]
variable [bvi : go.BasicIntoValInj]

local notation "kpkg" => pkg_id.github_com.despreston.go_craq.examples.craqnet

set_option goose.wp.extras true

/-- `pushPend(p, k, v)`: a new slice, `p`'s puts with `(k, v)` appended. -/
theorem wp_pushPend (p : GoSlice) (P : List pend) (k v : GoString) (hP : P.length < 2 ^ 60) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ p ↦*□ P }}
      (App (App (App (Val (@! github_com.despreston.go_craq.examples.craqnet.pushPend)) (Val #p))
        (Val #k)) (Val #v))
    {{ (q : GoSlice), RET #q; q ↦* (P ++ [pend.mk k v]) }} := by
  wp_start as #Hp
  ihave %Hl := ownSlice_len _ _ _ $$ Hp
  wp_auto
  wp_apply wp_slice_make2 (V := pend) $$ [] as %q ⟨Hq, -⟩
  · ipureintro; word
  wp_apply wp_slice_copy $$ [$Hq $Hp] as %n ⟨-, Hq, -⟩
  have hn : sint.nat (p.len + W64 1) = P.length + 1 := by rw [Hl.1]; word
  rw [hn, List.take_of_length_le (by simp), List.drop_replicate,
    show P.length + 1 - P.length = 1 by omega, List.replicate_one]
  ihave %Hql := ownSlice_len _ _ _ $$ Hq
  have hb : 0 ≤ sint.Z p.len ∧ sint.Z p.len < sint.Z q.len := by
    have := Hql.1; simp only [List.length_append, List.length_singleton] at this; word
  rw [ite_eq_left hb]
  wp_apply wp_store_slice_index q (sint.Z p.len) _ (pend.mk k v) $$ [Hq] as Hq
  · iframe Hq; ipureintro; simp only [List.length_append, List.length_singleton]; word
  rw [show (sint.Z p.len).toNat = P.length by rw [Hl.1],
    List.set_append_right _ _ (by omega), Nat.sub_self, List.set_cons_zero]
  wp_auto
  iapply HΦ
  iexact Hq

/-- `copyMap(m)`: a fresh map with `m`'s contents. -/
theorem wp_copyMap (mp : Loc) (m : GMap GoString GoString) (dq : DFrac) :
    {{ (mp ↦${dq} m : IProp GF) }}
      (App (Val (@! github_com.despreston.go_craq.examples.craqnet.copyMap)) (Val #mp))
    {{ (c : Loc), RET #c; c ↦$ m ∗ mp ↦${dq} m }} := by
  wp_start as Hm
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := GoString) go.string go.string) as %c Hc
  (try wp_auto)
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (wp_map_for_range (K := GoString) (V := GoString) (fun keys (i : Int) => iprop(
      ⌜0 ≤ i⌝ ∗ ∃ (cm : GMap GoString GoString) (kx vx : GoString),
        c_ptr ↦ c ∗ k_ptr ↦ kx ∗ v_ptr ↦ vx ∗ c ↦$ cm ∗
        ⌜∀ x, cm !! x = if x ∈ keys.take i.toNat then m !! x else none⌝))) $$ Hm
  iintro %keys %hkeys
  isplitl [c k v Hc]
  · isplitr
    · ipureintro; omega
    iexists ∅, _, _
    iframe
    ipureintro
    intro x
    simp
  isplitl []
  · imodintro
    iintro %i %key %val ⟨%hk1, %hk2⟩ ⟨%hi, %cm, %kx, %vx, Hcp, Hk, Hv, Hc, %Hcm⟩
    wp_auto
    wp_apply (wp_mapInsert go.string c cm key val) $$ [$Hc] as Hc
    (try wp_auto)
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; omega
    iexists _, key, val
    iframe
    ipureintro
    intro x
    rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, hk1]
    by_cases hx : x = key
    · subst hx
      simp [hk2]
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hx), Hcm x]
      simp [hx]
  · iintro ⟨%h0, %cm, %kx, %vx, Hcp, Hk, Hv, Hc, %Hcm⟩ Hm
    wp_auto
    iapply HΦ
    have hcm : cm = m := by
      apply GMap.map_eq
      intro x
      rw [Hcm x, ← hkeys.2.1, List.take_of_length_le (by omega)]
      by_cases hx : x ∈ keys
      · simp [hx]
      · rw [ite_eq_right_iff.2 (fun h => absurd h hx)]
        have h1 : ¬ (m !! x).isSome = true := fun h => hx ((hkeys.1 x).2 h)
        cases h : m !! x <;> simp_all
    rw [hcm]
    iframe
/-- `set(m, k, v)`: a fresh map, `m` with `k` mapped to `v`. -/
theorem wp_set (mp : Loc) (m : GMap GoString GoString) (dq : DFrac) (k v : GoString) :
    {{ (mp ↦${dq} m : IProp GF) }}
      (App (App (App (Val (@! github_com.despreston.go_craq.examples.craqnet.set)) (Val #mp))
        (Val #k)) (Val #v))
    {{ (c : Loc), RET #c; c ↦$ (<[k := v]> m) ∗ mp ↦${dq} m }} := by
  wp_start as Hm
  wp_auto
  wp_apply wp_copyMap mp m dq $$ [$Hm] as %c ⟨Hc, Hm⟩
  (try wp_auto)
  wp_apply (wp_mapInsert go.string c m k v) $$ [$Hc] as Hc
  (try wp_auto)
  iapply HΦ
  iframe

/-- `findPend(p, k, v)`: the first index of a put of `v` at `k` in `p`, if any. -/
theorem wp_findPend (p : GoSlice) (P : List pend) (k v : GoString) :
    {{ (p ↦*□ P : IProp GF) }}
      (App (App (App (Val (@! github_com.despreston.go_craq.examples.craqnet.findPend)) (Val #p))
        (Val #k)) (Val #v))
    {{ (i : w64) (ok : Bool), RET (PairV #i #ok);
        ⌜(∀ j < (if ok then sint.nat i else P.length), ∀ e, P[j]? = some e → ¬ (e.K' = k ∧ e.V' = v)) ∧
          (ok = true → 0 ≤ sint.Z i ∧ P[sint.nat i]? = some (pend.mk k v))⌝ }} := by
  wp_start as #Hp
  ihave %Hl := ownSlice_len _ _ _ $$ Hp
  wp_auto
  ihave HI : (∃ (i : w64), "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z p.len ∧
        ∀ j < sint.nat i, ∀ e, P[j]? = some e → ¬ (e.K' = k ∧ e.V' = v)⌝ : IProp GF) $$ [i]
  · iexists W64 0
    iframe
    ipureintro
    exact ⟨by decide, Hl.2, fun j hj => by rw [show sint.nat (W64 0) = 0 from rfl] at hj; omega⟩
  wp_for HI
  wp_if_destruct
  · have hi : sint.Z i < sint.Z p.len := by
      first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
    list_elem P (sint.nat i) as e
    icases ownSlice_elem_acc (sint.Z i) e p DFrac.discard P Hi.1 He_lookup $$ Hp with ⟨#He, -⟩
    rcases e with ⟨ek, ev⟩
    iStructNamed He
    simp only [show (0 ≤ sint.Z i ∧ sint.Z i < sint.Z p.len) = True from eq_true ⟨Hi.1, hi⟩,
      ite_true]
    wp_auto
    by_cases hk : ek = k
    · rw [decide_eq_true hk]
      wp_auto
      simp only [show (0 ≤ sint.Z i ∧ sint.Z i < sint.Z p.len) = True from eq_true ⟨Hi.1, hi⟩,
        ite_true]
      wp_auto
      by_cases hv : ev = v
      · rw [decide_eq_true hv]
        wp_auto
        rw [forPostcondition_unseal]; unfold forPostconditionDef
        iright; iright; iright; ileft
        iexists #()
        isplitr
        · ipureintro; rfl
        dsimp only
        wp_auto
        iapply HΦ
        ipureintro
        subst hk hv
        exact ⟨fun j hj => Hi.2.2 j (by simpa using hj), fun _ => ⟨Hi.1, He_lookup⟩⟩
      · rw [decide_eq_false hv]
        wp_auto
        wp_for_post
        iframe
        iexists i + W64 1
        iframe
        ipureintro
        refine ⟨by word, by word, fun j hj e he => ?_⟩
        rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word] at hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact Hi.2.2 j hj e he
        · rw [He_lookup] at he; cases he; intro h; first | exact hk h.1 | exact hv h.2
    · rw [decide_eq_false hk]
      wp_auto
      wp_for_post
      iframe
      iexists i + W64 1
      iframe
      ipureintro
      refine ⟨by word, by word, fun j hj e he => ?_⟩
      rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact Hi.2.2 j hj e he
      · rw [He_lookup] at he; cases he; intro h; first | exact hk h.1 | exact hv h.2
  · have hn : sint.nat i = P.length := by
      have : ¬ sint.Z i < sint.Z p.len := by
        first | exact Hif | exact fun h => Hif (by rw [decide_eq_true h])
      rw [Hl.1]; word
    (try wp_auto)
    iapply HΦ
    ipureintro
    exact ⟨fun j hj => Hi.2.2 j (by simpa [hn] using hj), fun h => by cases h⟩
theorem eraseIdx_take_succ {α : Type} (P : List α) (i j : Nat) (x : α) (hx : P[j]? = some x)
    (hij : j ≠ i) : (P.take (j + 1)).eraseIdx i = (P.take j).eraseIdx i ++ [x] := by
  rw [List.take_add_one, hx, Option.toList_some]
  have hj : j < P.length := (List.getElem?_eq_some_iff.1 hx).1
  have hl : (P.take j).length = j := by simp; omega
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · rw [List.eraseIdx_of_length_le (by simp; omega), List.eraseIdx_of_length_le (by omega)]
  · rw [List.eraseIdx_append_of_lt_length (by omega)]

theorem eraseIdx_take_self {α : Type} (P : List α) (i : Nat) :
    (P.take (i + 1)).eraseIdx i = (P.take i).eraseIdx i := by
  rw [List.eraseIdx_of_length_le (l := P.take i) (by simp [Nat.min_le_left])]
  rcases Nat.lt_or_ge i P.length with h | h
  · rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some,
      List.eraseIdx_append_of_length_le (by simp; omega)]
    simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt h), Nat.sub_self,
      List.eraseIdx_cons_zero, List.append_nil]
  · rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega),
      List.eraseIdx_of_length_le (by omega)]

/-- `erasePend(p, i)`: a fresh slice, `p` without its element `i`. -/
theorem wp_erasePend (p : GoSlice) (P : List pend) (i : w64) (hi : 0 ≤ sint.Z i) :
    {{ (p ↦*□ P : IProp GF) }}
      (App (App (Val (@! github_com.despreston.go_craq.examples.craqnet.erasePend)) (Val #p))
        (Val #i))
    {{ (q : GoSlice), RET #q; q ↦* P.eraseIdx (sint.nat i) }} := by
  wp_start as #Hp
  ihave %Hl := ownSlice_len _ _ _ $$ Hp
  wp_auto
  wp_apply wp_slice_make3 (V := pend) (W64 0) p.len ⟨by decide, Hl.2⟩ as %q ⟨Hq, Hqc, -⟩
  (try wp_auto)
  ihave HI : (∃ (j : w64) (qq : GoSlice), "j" ∷ j_ptr ↦ j ∗ "q" ∷ q_ptr ↦ qq ∗
      "Hq" ∷ qq ↦* (P.take (sint.nat j)).eraseIdx (sint.nat i) ∗
      "Hqc" ∷ ownSliceCap pend qq (DFrac.own 1) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z p.len⌝ : IProp GF) $$ [j q Hq Hqc]
  · iexists W64 0, q
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.eraseIdx_nil,
      List.replicate_zero]
    iframe
    ipureintro; exact ⟨by decide, Hl.2⟩
  wp_for HI
  wp_if_destruct
  · have hj : sint.Z j < sint.Z p.len := by
      first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
    by_cases hji : j = i
    · subst hji
      simp only [decide_true, Bool.not_true]
      wp_auto
      wp_for_post
      iframe
      iexists j + W64 1, qq
      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, eraseIdx_take_self]
      iframe
      ipureintro; exact ⟨by word, by word⟩
    · rw [decide_eq_false hji]
      simp only [Bool.not_false]
      wp_auto
      list_elem P (sint.nat j) as e
      rw [ite_eq_left ⟨Hj.1, hj⟩]
      wp_apply wp_load_slice_index p (sint.Z j) P DFrac.discard e Hj.1 $$ [$Hp] with -
      · ipureintro; exact He_lookup
      (try wp_auto)
      wp_apply wp_slice_literal (V := pend) [e]
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Hsl1, -⟩
      wp_apply wp_slice_append $$ [$Hq $Hqc $Hsl1] as %qq' ⟨Hq, Hqc, -⟩
      wp_for_post
      iframe
      iexists j + W64 1, qq'
      have hne : sint.nat j ≠ sint.nat i := fun h => hji (by word)
      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word,
        eraseIdx_take_succ P _ _ e He_lookup hne]
      iframe
      ipureintro; exact ⟨by word, by word⟩
  · have hn : sint.nat j = P.length := by
      have : ¬ sint.Z j < sint.Z p.len := by
        first | exact Hif | exact fun h => Hif (by rw [decide_eq_true h])
      rw [Hl.1]; word
    (try wp_auto)
    iapply HΦ
    rw [hn, List.take_length]
    iframe
/-- The Go map `m` holds the store state `a`. -/
def mrep (m : GMap GoString GoString) (a : St) : Prop := ∀ x, m.lookup x = (a x).map Subtype.val

theorem map_eraseIdx' {α β : Type} (g : α → β) (l : List α) (j : Nat) :
    (l.eraseIdx j).map g = (l.map g).eraseIdx j := by
  induction l generalizing j with
  | nil => simp
  | cons x l ih => cases j <;> simp_all [List.eraseIdx]

theorem erase_first {α : Type} [DecidableEq α] (l : List α) (x : α) (j : Nat)
    (hj : l[j]? = some x) (hlt : ∀ i < j, l[i]? ≠ some x) : l.erase x = l.eraseIdx j := by
  induction l generalizing j with
  | nil => simp at hj
  | cons y l ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj; simp
    | succ j =>
      have hy : y ≠ x := fun h => hlt 0 (by omega) (by simp [h])
      rw [List.erase_cons_tail (by simpa using hy), List.eraseIdx_cons_succ,
        ih j (by simpa using hj) (fun i hi => by simpa using hlt (i + 1) (by omega))]

/-- A put's `pend` determines it. -/
theorem pendOf_put {y : KIn} (hy : isPut y = true) {k v : GoString} (h : pendOf y = pend.mk k v) :
    ∃ hk, y = ⟨.put k v, hk⟩ := by
  obtain ⟨_ | ⟨k', v'⟩, hk'⟩ := y
  · simp [isPut] at hy
  · simp only [pendOf, pend.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hk', rfl⟩

theorem lookup_mrep {m : GMap GoString GoString} {a : St} (hm : mrep m a) (k : GoString) :
    m !! k = (a k).map Subtype.val := hm k

theorem mrep_set {m : GMap GoString GoString} {a : St} (hm : mrep m a) (k : GoString) (w : Str8) :
    mrep (<[k := w.1]> m) (upd a k w) := by
  intro x
  by_cases hx : x = k
  · subst hx; rw [show (<[x := w.1]> m).lookup x = (<[x := w.1]> m) !! x from rfl,
      GMap.lookup_insert]; simp [upd]
  · rw [show (<[k := w.1]> m).lookup x = (<[k := w.1]> m) !! x from rfl,
      GMap.lookup_insert_ne _ _ (Ne.symm hx)]
    simp [upd, hx]; exact hm x

theorem find_some (P : List KIn) (hP : ∀ x ∈ P, isPut x = true) (k : GoString) (w : Str8)
    (hk : keyOk k) (idx : Nat)
    (h1 : ∀ j < idx, ∀ e, (P.map pendOf)[j]? = some e → ¬ (e.K' = k ∧ e.V' = w.1))
    (h2 : (P.map pendOf)[idx]? = some (pend.mk k w.1)) :
    (⟨.put k w.1, ⟨hk, w.2⟩⟩ : KIn) ∈ P ∧
      P.erase ⟨.put k w.1, ⟨hk, w.2⟩⟩ = P.eraseIdx idx := by
  rw [List.getElem?_map] at h2
  obtain ⟨y, hy, hpy⟩ := Option.map_eq_some_iff.1 h2
  have hyP : y ∈ P := List.mem_of_getElem? hy
  obtain ⟨_, rfl⟩ := pendOf_put (hP y hyP) hpy
  refine ⟨hyP, erase_first P _ idx hy (fun j hj he => ?_)⟩
  exact h1 j hj (pend.mk k w.1) (by rw [List.getElem?_map, he]; rfl) ⟨rfl, rfl⟩

theorem find_none (P : List KIn) (k : GoString) (w : Str8) (hk : keyOk k)
    (h1 : ∀ j < (P.map pendOf).length, ∀ e, (P.map pendOf)[j]? = some e → ¬ (e.K' = k ∧ e.V' = w.1)) :
    (⟨.put k w.1, ⟨hk, w.2⟩⟩ : KIn) ∉ P := by
  intro hm
  obtain ⟨j, hj, he⟩ := List.getElem_of_mem hm
  exact h1 j (by simpa using hj) (pend.mk k w.1)
    (by rw [List.getElem?_map, List.getElem?_eq_getElem hj, he]; rfl) ⟨rfl, rfl⟩

/-- kit.go's `In` of a store input. -/
def inOf : KIn → In
  | ⟨.get k, _⟩ => In.mk false k []
  | ⟨.put k x, _⟩ => In.mk true k x

/-- What `step` returns: the verdict of `goStep` on the decoded answer, and when it allows the
step, a state holding `goStep`'s next state. -/
def stepPost (a : St) (P : List KIn) (i : KIn) (u f : Bool) (w : Str8) (ok : Bool) (s' : State) :
    IProp GF :=
  iprop(⌜ok = (goStep a P i (decAns i u f w)).isSome⌝ ∗
    if ok then ∃ (mp' : Loc) (sl' : GoSlice) (m' : GMap GoString GoString) (a' : St) (P' : List KIn),
      ⌜s' = State.mk mp' sl' ∧ goStep a P i (decAns i u f w) = some (a', P') ∧ mrep m' a' ∧
        (∀ x ∈ P', isPut x = true) ∧ P'.length ≤ P.length + 1⌝ ∗
      ownMap mp' DFrac.discard m' ∗ sl' ↦*□ P'.map pendOf
    else True)

theorem wp_step (mp : Loc) (sl : GoSlice) (m : GMap GoString GoString) (a : St) (P : List KIn)
    (hm : mrep m a) (hP : ∀ x ∈ P, isPut x = true) (hlen : P.length < 2 ^ 60)
    (i : KIn) (u f : Bool) (w : Str8) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ ownMap mp DFrac.discard m ∗ sl ↦*□ P.map pendOf }}
      (App (App (App (Val (@! github_com.despreston.go_craq.examples.craqnet.step))
        (Val #(State.mk mp sl))) (Val #(inOf i))) (Val #(Out.mk u f w.1)))
    {{ (ok : Bool) (s' : State), RET (PairV #ok #s'); stepPost a P i u f w ok s' }} := by
  wp_start as ⟨#Hm, #Hsl⟩
  have hpm : (P.map pendOf).length < 2 ^ 60 := by simpa using hlen
  obtain ⟨k | ⟨k, x⟩, hi⟩ := i <;> cases u
  all_goals simp only [inOf]
  all_goals wp_auto
  · -- a get, its answer known
    have hlk := lookup_mrep hm k
    wp_apply (wp_map_lookup2 go.string go.string mp m k DFrac.discard) $$ [$Hm] as -
    cases hak : a k with
    | none =>
      have hmk : m !! k = none := by rw [hlk, hak]; rfl
      simp only [hmk, Option.isSome_none, Option.getD_none, _root_.decide_false]
      cases f
      · simp only [Bool.not_false]
        wp_auto
        by_cases hw : w.1 = []
        · simp only [hw, _root_.decide_true, Bool.not_true]
          wp_auto
          iapply HΦ
          unfold stepPost
          isplitr
          · ipureintro; simp_all [decAns, goStep]
          simp only [↓reduceIte]
          iexists mp, sl, m, a, P
          isplitr
          · ipureintro; refine ⟨rfl, by simp_all [decAns, goStep], hm, hP, by omega⟩
          isplit
          · iexact Hm
          · iexact Hsl
        · simp only [hw, _root_.decide_false, Bool.not_false]
          wp_auto
          iapply HΦ
          unfold stepPost
          isplitr
          · ipureintro; simp_all [decAns, goStep]
          simp only [Bool.false_eq_true, ↓reduceIte]
          itrivial
      · simp only [Bool.not_true]
        wp_auto
        wp_apply wp_findPend sl (P.map pendOf) k w.1 $$ [$Hsl] as %idx %ok %Hf
        cases ok
        · have hnm := find_none P k w hi (by simpa using Hf.1)
          wp_auto
          iapply HΦ
          unfold stepPost
          isplitr
          · ipureintro; simp_all [decAns, goStep]
          simp only [Bool.false_eq_true, ↓reduceIte]
          itrivial
        · obtain ⟨hidx0, hidx⟩ := Hf.2 rfl
          obtain ⟨hmem, herase⟩ := find_some P hP k w hi (sint.nat idx) (by simpa using Hf.1) hidx
          wp_auto
          wp_apply +noauto wp_set mp m DFrac.discard k w.1 $$ [$Hm] as %c ⟨Hc, -⟩
          iapply fupd_wp
          imod ownMap_persist c _ _ $$ Hc with #Hc
          imodintro
          wp_auto
          wp_apply +noauto wp_erasePend sl (P.map pendOf) idx hidx0 $$ [$Hsl] as %q Hq
          iapply fupd_wp
          imod ownSlice_persist _ _ _ $$ Hq with #Hq
          imodintro
          wp_auto
          iapply HΦ
          unfold stepPost
          have hg : goStep a P ⟨.get k, hi⟩ (decAns ⟨.get k, hi⟩ false true w) =
              some (upd a k w, P.erase ⟨.put k w.1, ⟨hi, w.2⟩⟩) := by
            simp [decAns, goStep, hmem, hak]
          rw [hg]
          isplitr
          · ipureintro; rfl
          simp only [Option.isSome_some, ↓reduceIte]
          iexists c, q, <[k := w.1]> m, upd a k w, P.erase ⟨.put k w.1, ⟨hi, w.2⟩⟩
          isplitr
          · ipureintro
            refine ⟨rfl, rfl, mrep_set hm k w, fun y hy => hP y (List.mem_of_mem_erase hy), ?_⟩
            have := List.length_erase_le (l := P) (a := ⟨.put k w.1, ⟨hi, w.2⟩⟩); omega
          rw [herase, map_eraseIdx']
          isplit
          · iexact Hc
          · iexact Hq
    | some y =>
      have hmk : m !! k = some y.1 := by rw [hlk, hak]; rfl
      simp only [hmk, Option.isSome_some, Option.getD_some, _root_.decide_true]
      cases f
      · simp only [Bool.not_false]
        wp_auto
        by_cases hw : w.1 = []
        · simp only [hw, _root_.decide_true, Bool.not_true]
          wp_auto
          iapply HΦ
          unfold stepPost
          isplitr
          · ipureintro; simp_all [decAns, goStep]
          simp only [Bool.false_eq_true, ↓reduceIte]
          itrivial
        · simp only [hw, _root_.decide_false, Bool.not_false]
          wp_auto
          iapply HΦ
          unfold stepPost
          isplitr
          · ipureintro; simp_all [decAns, goStep]
          simp only [Bool.false_eq_true, ↓reduceIte]
          itrivial
      · simp only [Bool.not_true]
        wp_auto
        by_cases hyw : y = w
        · subst hyw
          simp only [_root_.decide_true]
          wp_auto
          iapply HΦ
          unfold stepPost
          isplitr
          · ipureintro; simp_all [decAns, goStep]
          simp only [↓reduceIte]
          iexists mp, sl, m, a, P
          isplitr
          · ipureintro; refine ⟨rfl, by simp_all [decAns, goStep], hm, hP, by omega⟩
          isplit
          · iexact Hm
          · iexact Hsl
        · have hyw' : y.1 ≠ w.1 := fun h => hyw (Subtype.ext h)
          simp only [hyw', _root_.decide_false]
          wp_auto
          wp_apply wp_findPend sl (P.map pendOf) k w.1 $$ [$Hsl] as %idx %ok %Hf
          cases ok
          · have hnm := find_none P k w hi (by simpa using Hf.1)
            wp_auto
            iapply HΦ
            unfold stepPost
            isplitr
            · ipureintro; simp_all [decAns, goStep]
            simp only [Bool.false_eq_true, ↓reduceIte]
            itrivial
          · obtain ⟨hidx0, hidx⟩ := Hf.2 rfl
            obtain ⟨hmem, herase⟩ := find_some P hP k w hi (sint.nat idx) (by simpa using Hf.1) hidx
            wp_auto
            wp_apply +noauto wp_set mp m DFrac.discard k w.1 $$ [$Hm] as %c ⟨Hc, -⟩
            iapply fupd_wp
            imod ownMap_persist c _ _ $$ Hc with #Hc
            imodintro
            wp_auto
            wp_apply +noauto wp_erasePend sl (P.map pendOf) idx hidx0 $$ [$Hsl] as %q Hq
            iapply fupd_wp
            imod ownSlice_persist _ _ _ $$ Hq with #Hq
            imodintro
            wp_auto
            iapply HΦ
            unfold stepPost
            have hg : goStep a P ⟨.get k, hi⟩ (decAns ⟨.get k, hi⟩ false true w) =
                some (upd a k w, P.erase ⟨.put k w.1, ⟨hi, w.2⟩⟩) := by
              simp [decAns, goStep, hmem, hak, hyw]
            rw [hg]
            isplitr
            · ipureintro; rfl
            simp only [Option.isSome_some, ↓reduceIte]
            iexists c, q, <[k := w.1]> m, upd a k w, P.erase ⟨.put k w.1, ⟨hi, w.2⟩⟩
            isplitr
            · ipureintro
              refine ⟨rfl, rfl, mrep_set hm k w, fun y hy => hP y (List.mem_of_mem_erase hy), ?_⟩
              have := List.length_erase_le (l := P) (a := ⟨.put k w.1, ⟨hi, w.2⟩⟩); omega
            rw [herase, map_eraseIdx']
            isplit
            · iexact Hc
            · iexact Hq
  · -- a get, unknown
    iapply HΦ
    unfold stepPost
    simp only [decAns, goStep, isPut, ite_true, Option.isSome_some, Bool.false_eq_true, ↓reduceIte]
    isplitr
    · ipureintro; first | rfl | trivial
    iexists mp, sl, m, a, P
    isplitr
    · ipureintro; exact ⟨rfl, rfl, hm, hP, by omega⟩
    isplit
    · iexact Hm
    · iexact Hsl
  · -- a put, its answer known
    cases f
    · simp only
      wp_auto
      by_cases hw : w.1 = []
      · simp only [hw, decide_true, Bool.not_true]
        wp_auto
        wp_apply +noauto wp_set mp m DFrac.discard k x $$ [$Hm] as %c ⟨Hc, -⟩
        iapply fupd_wp
        imod ownMap_persist c _ _ $$ Hc with #Hc
        imodintro
        wp_auto
        iapply HΦ
        unfold stepPost
        simp only [decAns, goStep, Bool.not_false, Bool.true_and, hw, decide_true, ↓reduceIte,
          Option.isSome_some]
        isplitr
        · ipureintro; first | rfl | trivial
        iexists c, sl, <[k := x]> m, upd a k ⟨x, hi.2⟩, P
        isplitr
        · ipureintro; exact ⟨rfl, rfl, mrep_set hm k ⟨x, hi.2⟩, hP, by omega⟩
        isplit
        · iexact Hc
        · iexact Hsl
      · simp only [hw, decide_false, Bool.not_false]
        wp_auto
        iapply HΦ
        unfold stepPost
        simp only [decAns, goStep, Bool.not_true, Bool.not_false, Bool.false_and, Bool.true_and,
          Bool.false_eq_true, ↓reduceIte, Option.isSome_none, hw, decide_false, decide_true]
        isplitr
        · ipureintro; first | rfl | trivial | simp_all
        itrivial
    · simp only
      wp_auto
      have hw : True := trivial
      iapply HΦ
      unfold stepPost
      simp only [decAns, goStep, Bool.not_true, Bool.not_false, Bool.false_and, Bool.true_and,
        Bool.false_eq_true, ↓reduceIte, Option.isSome_none, hw, decide_false, decide_true]
      isplitr
      · ipureintro; first | rfl | trivial | simp_all
      itrivial
  · -- a put, unknown
    wp_apply +noauto wp_pushPend sl (P.map pendOf) k x hpm $$ [$Hsl] as %q Hq
    iapply fupd_wp
    imod ownSlice_persist _ _ _ $$ Hq with #Hq
    imodintro
    wp_auto
    iapply HΦ
    unfold stepPost
    simp only [decAns, goStep, isPut, ite_true, Option.isSome_some, ↓reduceIte]
    isplitr
    · ipureintro; first | rfl | trivial
    iexists mp, q, m, a, P ++ [⟨.put k x, hi⟩]
    simp only [List.map_append, List.map_cons, List.map_nil, pendOf]
    isplitr
    · ipureintro
      refine ⟨by simp, by simp, hm, fun y hy => ?_, by simp⟩
      rcases List.mem_append.1 hy with h | h
      · exact hP y h
      · simp only [List.mem_singleton] at h; subst h; rfl
    isplit
    · iexact Hm
    · iexact Hq
end proof

/-! ## `kvDec` on boxed values -/

section dec
variable [GooseExts] [go_gctx : GoGlobalContext] [lctx : GoLocalContext] [GoSemanticsFunctions]
variable [sem : go.Semantics] [bvi : go.BasicIntoValInj]
variable [package_sem : github_com.despreston.go_craq.examples.craqnet.Assumptions]

/-- `Out`'s values are injective (the fields are read off by deterministic steps). -/
theorem out_intoVal_inj {x y : Out} (h : (#x : val) = #y) : x = y := by
  have hV := (Out.TypeAssumptions.get_V x).isGoStep_det_internal.isGoStep_pure_det
  have hV' := (Out.TypeAssumptions.get_V y).isGoStep_det_internal.isGoStep_pure_det
  have hU := (Out.TypeAssumptions.get_Unknown x).isGoStep_det_internal.isGoStep_pure_det
  have hU' := (Out.TypeAssumptions.get_Unknown y).isGoStep_det_internal.isGoStep_pure_det
  have hF := (Out.TypeAssumptions.get_Found x).isGoStep_det_internal.isGoStep_pure_det
  have hF' := (Out.TypeAssumptions.get_Found y).isGoStep_det_internal.isGoStep_pure_det
  rw [h, hV'] at hV
  rw [h, hU'] at hU
  rw [h, hF'] at hF
  have eV : Val #x.V' = Val #y.V' := (congrFun hV (Val #y.V')) ▸ rfl
  have eU : Val #x.Unknown' = Val #y.Unknown' := (congrFun hU (Val #y.Unknown')) ▸ rfl
  have eF : Val #x.Found' = Val #y.Found' := (congrFun hF (Val #y.Found')) ▸ rfl
  injection eV with eV
  injection eU with eU
  injection eF with eF
  have eV' := go.intoVal_inj eV
  have eU' := GoGlobalContext.intoVal_inj_bool eU
  have eF' := GoGlobalContext.intoVal_inj_bool eF
  cases x; cases y
  simp only at eV' eU' eF'
  subst eV' eU' eF'
  rfl

/-- `In`'s values are injective. -/
theorem in_intoVal_inj {x y : In} (h : (#x : val) = #y) : x = y := by
  have hV := (In.TypeAssumptions.get_V x).isGoStep_det_internal.isGoStep_pure_det
  have hV' := (In.TypeAssumptions.get_V y).isGoStep_det_internal.isGoStep_pure_det
  have hK := (In.TypeAssumptions.get_K x).isGoStep_det_internal.isGoStep_pure_det
  have hK' := (In.TypeAssumptions.get_K y).isGoStep_det_internal.isGoStep_pure_det
  have hP := (In.TypeAssumptions.get_Put x).isGoStep_det_internal.isGoStep_pure_det
  have hP' := (In.TypeAssumptions.get_Put y).isGoStep_det_internal.isGoStep_pure_det
  rw [h, hV'] at hV
  rw [h, hK'] at hK
  rw [h, hP'] at hP
  have eV : Val #x.V' = Val #y.V' := (congrFun hV (Val #y.V')) ▸ rfl
  have eK : Val #x.K' = Val #y.K' := (congrFun hK (Val #y.K')) ▸ rfl
  have eP : Val #x.Put' = Val #y.Put' := (congrFun hP (Val #y.Put')) ▸ rfl
  injection eV with eV
  injection eK with eK
  injection eP with eP
  have eV' := go.intoVal_inj eV
  have eK' := go.intoVal_inj eK
  have eP' := GoGlobalContext.intoVal_inj_bool eP
  cases x; cases y
  simp only at eV' eK' eP'
  subst eV' eK' eP'
  rfl

theorem outV_inj {u f v u' f' v'} (h : outV u f v = outV u' f' v') : u = u' ∧ f = f' ∧ v = v' := by
  simp only [outV, interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq,
    _root_.true_and] at h
  have := out_intoVal_inj h
  simp only [Out.mk.injEq] at this
  exact this

theorem ivK_inj {x y : KIn} (h : ivK x = ivK y) : x = y := by
  obtain ⟨k | ⟨k, v⟩, hx⟩ := x <;> obtain ⟨k' | ⟨k', v'⟩, hy⟩ := y <;>
    simp only [ivK, inV, interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq,
      _root_.true_and] at h <;>
    have := in_intoVal_inj h <;> simp only [In.mk.injEq] at this
  · obtain ⟨-, rfl, -⟩ := this; rfl
  · exact absurd this.1 (by decide)
  · exact absurd this.1 (by decide)
  · obtain ⟨-, rfl, rfl⟩ := this; rfl

/-- `kvDec` on a boxed input and a boxed bounded `Out`. -/
theorem kvDec_box (x : KIn) (u f : Bool) (w : Str8) :
    kvDec (ivK x, outV u f w.1) = some (x, decAns x u f w) := by
  unfold kvDec
  split
  · next h =>
    have hs := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec h)))
    obtain ⟨h1, h2⟩ := Prod.mk.inj hs
    have e1 := ivK_inj h1
    obtain ⟨e2, e3, e4⟩ := outV_inj h2
    have e4' := Subtype.ext e4
    dsimp only
    rw [← e4', ← e3, ← e2, ← e1]
  · next hn => exact absurd ⟨x, u, f, w, rfl⟩ hn

/-- `Out{u, f, w}`'s bytes. -/
theorem encOutV_outV (u f : Bool) (w : Str8) : encOutV (outV u f w.1) = encOutB u f w.1 := by
  unfold encOutV
  split
  · rename_i h
    have hs := Classical.choose_spec h
    obtain ⟨h1, h2, h3⟩ := outV_inj hs
    rw [← h1, ← h2, ← h3]
  · rename_i h
    exact absurd ⟨(u, f, w), rfl⟩ h

/-- `ovK o`'s bytes. -/
theorem encOutV_ovK (o : KOut) : ∃ (f : Bool) (w : Str8), ovK o = outV false f w.1 ∧
    encOutV (ovK o) = encOutB false f w.1 := by
  rcases o with (_ | x) | _
  · exact ⟨false, ⟨[], by simp⟩, rfl, encOutV_outV false false ⟨[], by simp⟩⟩
  · exact ⟨true, x, rfl, encOutV_outV false true x⟩
  · exact ⟨false, ⟨[W8 0], by simp⟩, rfl, encOutV_outV false false ⟨[W8 0], by simp⟩⟩

/-- `decAns` inverts `ovK`. -/
theorem decAns_ovK (i : KIn) (o : KOut) (f : Bool) (w : Str8) (h : ovK o = outV false f w.1) :
    decAns i false f w = .ok o := by
  rcases o with (_ | x) | _ <;> simp only [ovK] at h <;> obtain ⟨-, rfl, hw⟩ := outV_inj h
  · simp [decAns, ← hw]
  · have : w = x := Subtype.ext hw.symm
    subst this; simp [decAns]
  · simp [decAns, ← hw]

end dec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.despreston.go_craq.examples.craqnet.Assumptions]
variable [bvi : go.BasicIntoValInj]

local notation "kpkg" => pkg_id.github_com.despreston.go_craq.examples.craqnet

set_option goose.wp.extras true

/-- `Model()`: porcupine's model of the store (`kvS`). -/
abbrev Model.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) kpkg }}
    (App (Val (@! github_com.despreston.go_craq.examples.craqnet.Model)) (Val #()))
  {{ (m : github_com.anishathalye.porcupine.Model), RET #m; isModel (kvS (GF := GF)) m }}

theorem ivK_inOf (x : KIn) : ivK x = interface.mkOk In.ty #(inOf x) := by
  obtain ⟨k | ⟨k, v⟩, hx⟩ := x <;> rfl


/-- **porcupine's model is the pending-writes model** of the far side's store `kvR γ` (remote's
`Check` premise; finding F4: a put's success and a get's not found are the one output `got none`,
so `ovK` decodes back to its output whatever the input). -/
theorem kvS_pendDec (γ : CraqNames) :
    PendDec (kvR (Gg := hG.goose_globalGS) γ) (kvS (GF := GF)) :=
  .ofTotal (fun _ => rfl) {
  init := rfl
  ok s i o := by
    obtain ⟨f, w, hv, -⟩ := encOutV_ovK o
    show (linkv.pM kvB kvDec).step s (ivK i, ovK o) = _
    rw [hv, linkv.pM_step kvB kvDec s _ i _ (kvDec_box i false f w), decAns_ovK i o f w hv]
    rfl
  err s i := by
    show (linkv.pM kvB kvDec).step s (ivK i, outV true false []) = _
    rw [linkv.pM_step kvB kvDec s _ i _ (kvDec_box i true false ⟨[], by simp⟩)]
    rfl
  ioOk_ok i o := by
    obtain ⟨f, w, hv, -⟩ := encOutV_ovK o
    exact BI.pure_intro ⟨⟨i, rfl⟩, false, f, w, hv⟩
  ioOk_err i := BI.pure_intro ⟨⟨i, rfl⟩, true, false, ⟨[], by simp⟩, rfl⟩
  noObs _ := rfl }

/-- **Distinct outputs have distinct bytes** (remote's `Check` premise; finding F4). -/
theorem kvR_encOut_inj (γ : CraqNames) (o o' : KOut)
    (h : (kvR (Gg := hG.goose_globalGS) γ).encOut ((kvR (Gg := hG.goose_globalGS) γ).ov o) =
      (kvR (Gg := hG.goose_globalGS) γ).encOut ((kvR (Gg := hG.goose_globalGS) γ).ov o')) :
    o = o' := by
  simp only [kvR] at h
  obtain ⟨f, w, hv, he⟩ := encOutV_ovK o
  obtain ⟨f', w', hv', he'⟩ := encOutV_ovK o'
  rw [he, he'] at h
  rcases o with (_ | x) | _ <;> rcases o' with (_ | x') | _ <;>
    simp only [ovK] at hv hv' <;> obtain ⟨-, rfl, hw⟩ := outV_inj hv <;>
    obtain ⟨-, rfl, hw'⟩ := outV_inj hv' <;>
    simp_all [encOutB, encS, flagB]
  exact Subtype.ext (hw.trans hw'.symm)

end proof

end github_com.despreston.go_craq.examples.craqnet
end Perennial
