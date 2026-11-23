/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/codec/Map.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
Go maps with `swift.CommandId` keys at the level of their entries (`rawMap`: the map's heap
value lists its entries in insertion order), as the codec's `MSync` ownership states them
(`Spec/swiftnet/Codec.lean`, `mapOwn`): `swift.CommandId` is a safe map key (Go's `==` on it is
equality, its `intoVal` is injective), an insert into a raw map, and the raw map as an `ownMap`
(for `len` and `range`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.codec.Base

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section map
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : examples.swiftnet.Assumptions]


instance cmdId_safeMapKey (k : swift.CommandId) :
    SafeMapKey (GF := GF) (keys := mapKeys_all swift.CommandId) swift.CommandId.ty k where
  key_ok := trivial
  wp_go_eq_map_key k' _ s E Φ := wp_eq_cmdid k k' s E Φ

/-- The Go map at `l` holds the entries `ps` (in this order). -/
def rawMap {V : Type} [ZeroVal V] (l : Loc) (dq : DFrac) (ps : List (swift.CommandId × V)) :
    IProp GF :=
  heapPointsto l dq (map.mapV #(zero_val V) (ps.map map.toE))

/-- `m[k] = v` on a raw map with distinct keys: the entries `insertL k v ps`. -/
theorem wp_rawMapInsert {V : Type} [ZeroVal V] (l : Loc) (ps : List (swift.CommandId × V))
    (k : swift.CommandId) (v : V) :
    {{ (rawMap l (DFrac.own 1) ps : IProp GF) }}
      (App (App (App (Val (map.insert swift.CommandId.ty)) (Val #l)) (Val #k)) (Val #v))
    {{ RET #(); rawMap l (DFrac.own 1) (map.insertL k v ps) }} := by
  haveI : go.IntoValInj swift.CommandId := ⟨cmdId_intoVal_inj (sem := sem) (package_sem := package_sem)⟩
  iintro %Φ Hown HΦ
  unfold rawMap
  wp_call
  wp_apply (_internal_wp_untyped_read _ _ _ (map.mapV_not_panic _ _)) $$ Hown with Hown
  wp_pures
  have hid : k ∉ ps.map Prod.fst → map.freshId #k (ps.map map.toE) = map.keyId k :=
    map.freshId_keyId k ps
  have Hins := wp_insertExpr (GF := GF) (s := Stuckness.NotStuck) (E := ⊤) swift.CommandId.ty k v
    #(zero_val V) _ [] ps hid (fun _ _ => trivial)
  simp only [List.map_nil, List.nil_append] at Hins
  wp_bind (map.insertExpr swift.CommandId.ty #k #v #(zero_val V) (map.freshId #k (ps.map map.toE)) []
    (ps.map map.toE))
  iapply Hins
  wp_apply (_internal_wp_untyped_store _ _ _ (map.mapV_not_panic _ _)) $$ Hown with Hown
  iapply HΦ $$ Hown

/-- `make(map[swift.CommandId]V)`: an empty raw map. -/
theorem wp_rawMap_make1 {V : Type} [ZeroVal V] (elem_type : go.GoType)
    [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V elem_type] :
    {{ (True : IProp GF) }}
      (App (Val #(functions go.make1 [go.MapType swift.CommandId.ty elem_type])) (Val #()))
    {{ (l : Loc), RET #l; rawMap l (DFrac.own 1) ([] : List (swift.CommandId × V)) }} := by
  haveI : go.IntoValInj swift.CommandId := ⟨cmdId_intoVal_inj (sem := sem) (package_sem := package_sem)⟩
  iintro %Φ - HΦ
  wp_apply (wp_map_make1 (K := swift.CommandId) (V := V) swift.CommandId.ty elem_type) as %l Hl
  rw [ownMap_unseal]; unfold ownMapDef
  iNamed Hl
  obtain ⟨rfl, -, -, Hagree⟩ := Hrepr
  have : ps = [] := by
    cases ps with
    | nil => rfl
    | cons p ps =>
      have := Hagree p.1
      simp [map.lookupL] at this
  subst this
  iapply HΦ; unfold rawMap; iexact Hown

omit [GooseSemantics] [GooseInterp] in
theorem perm_of_map_inj {α β : Type} [Inhabited α] {f : α → β} (hf : Function.Injective f)
    {l1 l2 : List α} (h : (l1.map f).Perm (l2.map f)) : l1.Perm l2 := by
  classical
  let g : β → α := fun b => if hb : ∃ a, f a = b then Classical.choose hb else default
  have hg : ∀ a, g (f a) = a := by
    intro a
    have hb : ∃ a', f a' = f a := ⟨a, rfl⟩
    simp only [g, dif_pos hb]
    exact hf (Classical.choose_spec hb)
  have := h.map g
  simp only [List.map_map, Function.comp_def, hg, List.map_id'] at this
  exact this

/-- `len(m)` of a raw map. -/
theorem wp_rawMap_len {V : Type} [ZeroVal V] {t elem_type : go.GoType}
    [t ↓u go.MapType swift.CommandId.ty elem_type] (mp : Loc) (dq : DFrac)
    (ps : List (swift.CommandId × V)) :
    {{ (rawMap mp dq ps : IProp GF) }}
      (App (Val #(functions go.len [t])) (Val #mp))
    {{ RET #(W64 ps.length); rawMap mp dq ps ∗ ⌜ps.length < 2 ^ 63⌝ }} := by
  wp_start as Hm
  unfold rawMap
  ihave %Hnn := heapPointsto_non_null _ _ _ $$ Hm
  rw [decide_eq_false (show mp ≠ map.nil from Hnn)]
  wp_pures
  wp_bind (App (Val Read) (Val #mp))
  wp_apply (_internal_wp_untyped_read _ _ _ (map.mapV_not_panic _ _)) $$ Hm as Hm
  rw [List.length_map]
  by_cases hb : ps.length < 2 ^ 63
  · rw [if_pos hb]
    wp_pures
    iapply HΦ
    iframe
    ipureintro; exact hb
  · rw [if_neg hb]
    iapply wp_assume
    iintro %h
    cases h

/-- `for k, v := range m { body }` over a raw map the loop only reads (any fraction), whose
body always runs to its end: the body is called on each key of the map once, in the order of
`keys` (a permutation of the entries' keys), with its value. -/
theorem wp_rawMap_for_range {V : Type} [ZeroVal V] (P : List swift.CommandId → Nat → IProp GF)
    (body : GoFunc) (elem_type : go.GoType) (mp : Loc) (dq : DFrac)
    (ps : List (swift.CommandId × V)) (Φ : val → IProp GF) :
    (rawMap mp dq ps : IProp GF) -∗
    (∀ keys : List swift.CommandId, ⌜keys.Perm (ps.map Prod.fst)⌝ -∗
      (P keys 0 ∗
       □ (∀ (i : Nat) (key : swift.CommandId) (v : V),
          ⌜keys[i]? = some key ∧ map.lookupL key ps = some v⌝ -∗ P keys i -∗
          WP (App (App (Val #body) (Val #key)) (Val #v))
            {{ bv, ⌜bv = executeVal⌝ ∗ P keys (i + 1) }}) ∗
       (P keys keys.length -∗ rawMap mp dq ps -∗ Φ executeVal))) -∗
    WP (App (App (Val (map.forRange swift.CommandId.ty elem_type)) (Val #mp)) (Val #body)) {{ Φ }} := by
  haveI : go.IntoValInj swift.CommandId := ⟨cmdId_intoVal_inj (sem := sem) (package_sem := package_sem)⟩
  iintro Hm HΦ
  unfold rawMap
  ihave %Hnn := heapPointsto_non_null _ _ _ $$ Hm
  wp_call
  rw [decide_eq_false (show mp ≠ map.nil from Hnn)]
  wp_pures
  wp_bind (App (Val Read) (Val #mp))
  wp_apply (_internal_wp_untyped_read _ _ _ (map.mapV_not_panic _ _)) $$ Hm as Hm
  wp_pures
  rw [show PairV #(zero_val V) (ArrayV ((ps.map map.toE).map map.entryV)) =
    map.mapV #(zero_val V) (ps.map map.toE) from rfl]
  wp_bind (App (Val (GoInstruction (InternalMapForRange swift.CommandId.ty elem_type))) _)
  iapply wp_InternalMapForRange
  iintro %e' %He'
  rw [go.internal_map_for_range_step] at He'
  obtain ⟨ids, hperm, rfl⟩ := He'
  have hids : (ps.map map.toE).map (·.id) = (ps.map Prod.fst).map map.keyId := by
    simp [List.map_map, Function.comp_def, map.toE]
  rw [hids] at hperm
  obtain ⟨keys, rfl⟩ := list_exists_map_of_forall map.keyId ids (fun x hx => by
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 (hperm.mem_iff.1 hx)
    exact ⟨k, rfl⟩)
  have hkp : keys.Perm (ps.map Prod.fst) :=
    haveI : Inhabited swift.CommandId := ⟨⟨0, 0⟩⟩
    perm_of_map_inj map.keyId_inj hperm
  icases HΦ $$ %keys %hkp with ⟨HP, #Hiter, HΦ⟩
  obtain ⟨i, hi⟩ : ∃ i : Nat, i = 0 := ⟨0, rfl⟩
  have hile : i ≤ keys.length := by omega
  rw [show List.map map.keyId keys = List.map map.keyId (keys.drop i) by rw [hi, List.drop_zero],
    show P keys 0 = P keys i by rw [hi]]
  clear hi
  iloeb as IH generalizing %i %hile
  by_cases hlt : i < keys.length
  · have hkey : keys[i]? = some keys[i] := List.getElem?_eq_getElem hlt
    rw [List.drop_eq_getElem_cons hlt, List.map_cons, List.foldr_cons]
    wp_auto
    wp_bind (App (Val Read) (Val #mp))
    wp_apply (_internal_wp_untyped_read _ _ _ (map.mapV_not_panic _ _)) $$ Hm as Hm
    wp_pures
    rw [show PairV #(keys[i]) (ArrayV (List.replicate 0 (LitV LitUnit))) = map.keyId keys[i]
      from rfl, map.lookupIdVal_keyId]
    have hin : keys[i] ∈ ps.map Prod.fst := hkp.mem_iff.1 (List.getElem_mem hlt)
    obtain ⟨v, hv⟩ : ∃ v, map.lookupL keys[i] ps = some v := by
      cases h : map.lookupL keys[i] ps with
      | none => exact absurd hin (by
          intro hm
          obtain ⟨⟨k, w⟩, hp, rfl⟩ := List.mem_map.1 hm
          have := (map.lookupL_eq_none_iff _ ps).1 h
          exact this (List.mem_map_of_mem hp))
      | some v => exact ⟨v, rfl⟩
    rw [hv]
    simp only
    wp_pures
    ihave Hb := Hiter $$ %i %(keys[i]) %v %(⟨hkey, hv⟩) HP
    wp_bind (App (App (Val #body) (Val #(keys[i]))) (Val #v))
    iapply wp_wand $$ Hb
    iintro %bv ⟨%hbv, HP⟩
    subst hbv
    rw [executeVal_unseal]; simp only [executeValDef]
    wp_auto
    iapply IH $$ %(i + 1) %(by omega) Hm HP HΦ
  · rw [List.drop_of_length_le (by omega)]
    simp only [List.map_nil, List.foldr_nil]
    wp_auto
    have hi : i = keys.length := by omega
    subst hi
    iapply HΦ $$ HP Hm

/-- The Go entries `gs` hold the decoded entries `xs`: the same keys in the same order, each Go
value holding its value (`own`). -/
def valsOwn {G A : Type} (own : G → A → IProp GF) :
    List (swift.CommandId × G) → List (swift.CommandId × A) → IProp GF
  | [], [] => iprop(True)
  | g :: gs, a :: xs => iprop(⌜g.1 = a.1⌝ ∗ own g.2 a.2 ∗ valsOwn own gs xs)
  | _, _ => iprop(False)

theorem valsOwn_keys {G A : Type} (own : G → A → IProp GF) (gs : List (swift.CommandId × G))
    (xs : List (swift.CommandId × A)) :
    valsOwn own gs xs ⊢ ⌜gs.map Prod.fst = xs.map Prod.fst⌝ := by
  induction gs generalizing xs with
  | nil =>
    cases xs with
    | nil => iintro _; ipureintro; rfl
    | cons a xs => simp only [valsOwn]; iintro H; iexfalso; iexact H
  | cons g gs ih =>
    cases xs with
    | nil => simp only [valsOwn]; iintro H; iexfalso; iexact H
    | cons a xs =>
      simp only [valsOwn]
      iintro ⟨%h, -, H⟩
      ihave %h' := ih xs $$ H
      ipureintro; simp [h, h']

theorem valsOwn_insert {G A : Type} (own : G → A → IProp GF) (k : swift.CommandId) (g : G) (a : A)
    (gs : List (swift.CommandId × G)) (xs : List (swift.CommandId × A)) :
    valsOwn own gs xs ∗ own g a ⊢ valsOwn own (map.insertL k g gs) (map.insertL k a xs) := by
  induction gs generalizing xs with
  | nil =>
    cases xs with
    | nil => simp only [valsOwn, map.insertL]; iintro ⟨-, H⟩; iframe H
    | cons a xs => simp only [valsOwn]; iintro ⟨H, -⟩; iexfalso; iexact H
  | cons g1 gs ih =>
    cases xs with
    | nil => simp only [valsOwn]; iintro ⟨H, -⟩; iexfalso; iexact H
    | cons a1 xs =>
      obtain ⟨k1, v1⟩ := g1
      obtain ⟨k1', a1'⟩ := a1
      simp only [valsOwn]
      iintro ⟨⟨%h, H1, H⟩, Ha⟩
      subst h
      by_cases hk : k = k1
      · subst hk
        simp only [map.insertL, ↓reduceIte, valsOwn]
        iframe Ha H
      · simp only [map.insertL, hk, ↓reduceIte, valsOwn]
        iframe H1
        iapply ih $$ [H Ha]
        iframe

/-- A decoded map: a fresh Go map whose entries (distinct keys) hold the decoded entries. -/
def ownMapOf {G A : Type} [ZeroVal G] (own : G → A → IProp GF) (mp : GoMap)
    (xs : List (swift.CommandId × A)) : IProp GF :=
  iprop(∃ gs : List (swift.CommandId × G), rawMap mp (DFrac.own 1) gs ∗
    ⌜(gs.map Prod.fst).Nodup⌝ ∗ valsOwn own gs xs)

end map

end Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet

namespace Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet
section entries
variable [GooseExts]

/-- The decoded entry listed at the position of the Go key `k` in the map's entries. -/
def entryAt {G A : Type} : List (swift.CommandId × G) → List (sp.CmdId × A) → swift.CommandId →
    Option (sp.CmdId × A)
  | p :: ps, e :: l, k => if p.1 = k then some e else entryAt ps l k
  | _, _, _ => none

theorem entryAt_getElem {G A : Type} (ps : List (swift.CommandId × G)) (l : List (sp.CmdId × A))
    (hnd : (ps.map Prod.fst).Nodup) (j : Nat) (p : swift.CommandId × G) (hp : ps[j]? = some p) :
    entryAt ps l p.1 = l[j]? := by
  induction ps generalizing l j with
  | nil => simp at hp
  | cons q ps ih =>
    cases l with
    | nil => cases j <;> simp [entryAt]
    | cons e l =>
      simp only [List.map_cons, List.nodup_cons] at hnd
      cases j with
      | zero =>
        simp at hp; subst hp; simp [entryAt]
      | succ j =>
        simp only [List.getElem?_cons_succ] at hp ⊢
        have hne : ¬ q.1 = p.1 := by
          intro h; apply hnd.1; rw [h]; exact List.mem_map_of_mem (List.mem_of_getElem? hp)
        simp only [entryAt, hne, ↓reduceIte]
        exact ih l hnd.2 j hp

theorem filterMap_entryAt {G A : Type} (ps : List (swift.CommandId × G)) (l : List (sp.CmdId × A))
    (hnd : (ps.map Prod.fst).Nodup) (hlen : ps.length = l.length) :
    (ps.map Prod.fst).filterMap (entryAt ps l) = l := by
  induction ps generalizing l with
  | nil => cases l <;> simp_all
  | cons q ps ih =>
    cases l with
    | nil => simp at hlen
    | cons e l =>
      simp only [List.map_cons, List.nodup_cons] at hnd
      simp only [List.map_cons, List.filterMap_cons, entryAt, ↓reduceIte, List.cons.injEq, true_and]
      conv => rhs; rw [← ih l hnd.2 (by simpa using hlen)]
      have key : ∀ (ks : List swift.CommandId), (∀ k ∈ ks, ¬ q.1 = k) →
          ks.filterMap (entryAt (q :: ps) (e :: l)) = ks.filterMap (entryAt ps l) := by
        intro ks hks
        induction ks with
        | nil => rfl
        | cons k ks ihk =>
          have h1 : ¬ q.1 = k := hks k (List.mem_cons_self ..)
          have e1 : entryAt (q :: ps) (e :: l) k = entryAt ps l k := by simp [entryAt, h1]
          rw [List.filterMap_cons, List.filterMap_cons, e1,
            ihk (fun k' hk' => hks k' (List.mem_cons_of_mem _ hk'))]
      exact key _ (fun k hk h => hnd.1 (h ▸ hk))

theorem perm_filterMap_entryAt {G A : Type} (ps : List (swift.CommandId × G))
    (l : List (sp.CmdId × A)) (hnd : (ps.map Prod.fst).Nodup) (hlen : ps.length = l.length)
    (keys : List swift.CommandId) (hk : keys.Perm (ps.map Prod.fst)) :
    (keys.filterMap (entryAt ps l)).Perm l := by
  have := hk.filterMap (entryAt ps l)
  rw [filterMap_entryAt ps l hnd hlen] at this
  exact this

end entries
end Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet

namespace Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet
section entries2
variable [GooseExts]

theorem lookupL_getElem {G : Type} (ps : List (swift.CommandId × G)) (k : swift.CommandId) (v : G)
    (h : map.lookupL k ps = some v) : ∃ j : Nat, ps[j]? = some (k, v) := by
  induction ps with
  | nil => simp [map.lookupL] at h
  | cons p ps ih =>
    simp only [map.lookupL] at h
    by_cases hk : k = p.1
    · simp only [hk, ↓reduceIte, Option.some.injEq] at h
      exact ⟨0, by subst h; simp [hk]⟩
    · simp only [hk, ↓reduceIte] at h
      obtain ⟨j, hj⟩ := ih h
      exact ⟨j + 1, by simpa using hj⟩

/-- The encoder's output for the keys seen so far, extended by one key. -/
theorem filterMap_take_succ {G A : Type} (ps : List (swift.CommandId × G)) (l : List (sp.CmdId × A))
    (keys : List swift.CommandId) (i : Nat) (k : swift.CommandId) (e : sp.CmdId × A)
    (hk : keys[i]? = some k) (he : entryAt ps l k = some e) :
    (keys.take (i + 1)).filterMap (entryAt ps l) = (keys.take i).filterMap (entryAt ps l) ++ [e] := by
  rw [List.take_add_one, hk]
  simp [List.filterMap_append, he]

end entries2
end Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet
