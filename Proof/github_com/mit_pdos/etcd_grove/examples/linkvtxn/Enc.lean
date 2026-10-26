/-
Lean-first (no Rocq counterpart).

# linkvtxn: the model's answers as `call` builds them (linkv-txn stage F)

`call` (`examples/linkvtxn/linkvtxn.go`) turns a reply into an `Output`; `outOf o` is the `Output`
it builds for the model's answer `o` (`encVR`, `encRes`: a get's key-value, a transaction
operation's result, as `call`'s `vrOf` and `TRes{...}`), `errOut` the one of a failed call.

- **`decOut_outOf`**: the model decodes `outOf` of its own answer back (`decOut`), for a decodable
  input at a state whose next revision fits a word (the header revision `call` copies);
  `decOut_errOut` the failed call's.
- `GoodKV σ`: etcd's state sorted by key, its keys the workload's (`linkv.KeysIn wks`): what the
  model's steps against etcd's (`linkv.absSt_kvOpStep`, `linkv.mStep_list_out`) need, kept by
  every step of a workload input (`goodKV_step`); `opIn i` the server's operation of the model
  input `i` (`linkv.opOf` at the list's range `[listFrom, listTo)`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Steps
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.TxnModelKV

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open github_com.mit_pdos.etcd_grove.examples.linkvtxn
open Classical

section enc
variable [GooseExts]

/-! ## The encoding -/

/-- A model key-value's value as `vrOf` builds it. -/
def encVR (r : linkv.VR GoString) : VR := ⟨r.val, r.mod, r.ver⟩

/-- A transaction operation's model result as `call` builds it. -/
def encRes : linkv.MRes GoString → TRes
  | .get none => getRes (zVR, false)
  | .get (some r) => getRes (encVR r, true)
  | .put => putRes
  | .del n => delRes (W64 (n : Int))

/-- **The `Output` `call` builds for the model's answer `o`** (see the file header). -/
def outOf : MO → Output
  | .get rev none => { zOut with Rev' := W64 (rev : Int) }
  | .get rev (some r) => { zOut with Rev' := W64 (rev : Int), Found' := true, R' := encVR r }
  | .list rev rs =>
    withKVsL { zOut with Rev' := W64 (rev : Int) } (rs.map fun p => (⟨p.1, encVR p.2⟩ : KV))
  | .put rev => { zOut with Rev' := W64 (rev : Int) }
  | .del rev n => { zOut with Rev' := W64 (rev : Int), N' := W64 (n : Int) }
  | .txn rev ok rs => withResL { zOut with Rev' := W64 (rev : Int), Ok' := ok } (rs.map encRes)

/-- A failed call's `Output` (`Output{Err: true}`). -/
def errOut : Output := { zOut with Err' := true }

theorem uint_nat_W64 (n : Nat) (h : n < 2 ^ 64) : uint.nat (W64 (n : Int)) = n := by
  unfold uint.nat; word

/-- A result the model's operations give: a get's, a put's, a delete's of at most one key. -/
def MRes.Small : linkv.MRes GoString → Prop
  | .del n => n < 2
  | _ => True

theorem decRes_encRes (r : linkv.MRes GoString) (h : MRes.Small r) : decRes (encRes r) = r := by
  cases r with
  | get v => cases v <;> rfl
  | put => exact decRes_putRes
  | del n =>
    simp only [MRes.Small] at h
    simp only [encRes]
    rw [decRes_delRes, uint_nat_W64 n (by omega)]

theorem runOps_small (r : Nat) :
    ∀ (m : linkv.MStore GoString GoString) (ops : List (linkv.MOp GoString GoString)),
      (linkv.runOps r m ops).2.1.length = ops.length ∧
        ∀ x ∈ (linkv.runOps r m ops).2.1, MRes.Small x
  | m, [] => by simp [linkv.runOps]
  | m, op :: ops => by
    have ih := runOps_small r (op.run r m).1 ops
    simp only [linkv.runOps, List.length_cons, List.mem_cons, forall_eq_or_imp]
    refine ⟨by rw [ih.1], ?_, ih.2⟩
    cases op with
    | get k => trivial
    | put k v => trivial
    | del k =>
      simp only [linkv.MOp.run]
      cases m k <;> simp [MRes.Small]

theorem decAll_length {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (l' : List β), decAll f l = some l' → l'.length = l.length
  | [], l', h => by simp only [decAll, Option.some.injEq] at h; subst h; rfl
  | a :: l, l', h => by
    simp only [decAll] at h
    cases hf : f a with
    | none => rw [hf] at h; cases h
    | some b =>
      rw [hf] at h
      cases hr : decAll f l with
      | none => rw [hr] at h; cases h
      | some r =>
        rw [hr] at h
        simp only [Option.bind_some, Option.map_some, Option.some.injEq] at h
        subst h
        simp [decAll_length f l r hr]

/-- Decoding every element: the elements' decodings, index by index. -/
theorem decAll_getElem {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (l' : List β), decAll f l = some l' →
      ∀ (k : Nat) (a : α), l[k]? = some a → ∃ b, f a = some b ∧ l'[k]? = some b
  | [], l', _, k, a, h => by simp at h
  | x :: l, l', h, k, a, hk => by
    simp only [decAll] at h
    cases hf : f x with
    | none => rw [hf] at h; cases h
    | some b =>
      rw [hf] at h
      cases hr : decAll f l with
      | none => rw [hr] at h; cases h
      | some r =>
        rw [hr] at h
        simp only [Option.bind_some, Option.map_some, Option.some.injEq] at h
        subst h
        cases k with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
          subst hk
          exact ⟨b, hf, rfl⟩
        | succ k =>
          simp only [List.getElem?_cons_succ] at hk ⊢
          exact decAll_getElem f l r hr k a hk

theorem filterMap_length_le {α β : Type} (f : α → Option β) :
    ∀ l : List α, (l.filterMap f).length ≤ l.length
  | [] => by simp
  | a :: l => by
    have := filterMap_length_le f l
    simp only [List.filterMap_cons]
    split <;> simp <;> omega

theorem w64_3_ne_0 : (W64 3 : w64) ≠ W64 0 := by decide
theorem w64_3_ne_1 : (W64 3 : w64) ≠ W64 1 := by decide
theorem w64_3_ne_2 : (W64 3 : w64) ≠ W64 2 := by decide
theorem w64_4_ne_0 : (W64 4 : w64) ≠ W64 0 := by decide
theorem w64_4_ne_1 : (W64 4 : w64) ≠ W64 1 := by decide
theorem w64_4_ne_2 : (W64 4 : w64) ≠ W64 2 := by decide
theorem w64_4_ne_3 : (W64 4 : w64) ≠ W64 3 := by decide

/-- **The model decodes `outOf` of its own answer** (see the file header). -/
theorem decOut_outOf (x : Input) (i : MI) (hx : decIn x = some i) (s : MS)
    (hr : (linkv.mStep wks i s).2.rev < 2 ^ 64) :
    decOut x.Kind' (outOf (linkv.mStep wks i s).2) = .ok (linkv.mStep wks i s).2 := by
  have n10 := w64_1_ne_0
  have n20 := w64_2_ne_0
  have n21 := w64_2_ne_1
  have n30 := w64_3_ne_0
  have n31 := w64_3_ne_1
  have n32 := w64_3_ne_2
  have n40 := w64_4_ne_0
  have n41 := w64_4_ne_1
  have n42 := w64_4_ne_2
  have n43 := w64_4_ne_3
  rcases decIn_cases x i hx with ⟨hk, rfl⟩ | ⟨hk, rfl⟩ | ⟨hk, rfl⟩ | ⟨hk, rfl⟩ |
    ⟨hk, cs, t, e, rfl, hcs, ht, he⟩
  · -- get
    have hr0 : uint.nat (W64 (s.rev : Int)) = s.rev := uint_nat_W64 _ hr
    simp only [linkv.mStep]
    cases hv : s.kv x.Key' with
    | none =>
      simp only [outOf, decOut, zOut, hk, ↓reduceIte, hr0, decVR]
      rfl
    | some r =>
      simp only [outOf, decOut, zOut, hk, ↓reduceIte, hr0, decVR]
      rfl
  · -- list
    have hr0 : uint.nat (W64 (s.rev : Int)) = s.rev := uint_nat_W64 _ hr
    simp only [linkv.mStep, outOf]
    have hlen : ((wks.filterMap fun k => (s.kv k).map fun v => (k, v)).map
        fun p => (⟨p.1, encVR p.2⟩ : KV)).length ≤ 3 := by
      rw [List.length_map]
      exact filterMap_length_le _ wks
    obtain ⟨h1, h2⟩ := kvsOfL_withKVsL { zOut with Rev' := W64 (s.rev : Int) } _ hlen
    unfold decOut
    simp only [withKVsL, zOut] at h1 h2 ⊢
    simp only [Bool.false_eq_true, ↓reduceIte, hk, n10, h2, h1, List.map_map, hr0]
    congr 2
    conv => rhs; rw [← List.map_id (wks.filterMap _)]
    apply List.map_congr_left
    intro p _
    rfl
  · -- put
    have hr1 : uint.nat (W64 ((s.rev + 1 : Nat) : Int)) = s.rev + 1 := uint_nat_W64 _ hr
    simp only [linkv.mStep, outOf, decOut, zOut, Bool.false_eq_true, ↓reduceIte, hk, n20, n21,
      hr1]
  · -- delete
    simp only [linkv.mStep] at hr ⊢
    cases hv : s.kv x.Key' with
    | none =>
      rw [hv] at hr
      have hr0 : uint.nat (W64 (s.rev : Int)) = s.rev := uint_nat_W64 _ hr
      simp only [outOf, decOut, zOut, Bool.false_eq_true, ↓reduceIte, hk, n30, n31, n32, hr0]
      rw [uint_nat_W64 0 (by omega)]
    | some _ =>
      rw [hv] at hr
      have hr1 : uint.nat (W64 ((s.rev + 1 : Nat) : Int)) = s.rev + 1 := uint_nat_W64 _ hr
      simp only [outOf, decOut, zOut, Bool.false_eq_true, ↓reduceIte, hk, n30, n31, n32, hr1]
      rw [uint_nat_W64 1 (by omega)]
  · -- transaction
    have hlt : t.length ≤ 3 := by rw [decAll_length _ _ _ ht]; exact thenOfL_length x
    have hle : e.length ≤ 3 := by rw [decAll_length _ _ _ he]; exact elseOfL_length x
    simp only [linkv.mStep, linkv.MOut.rev] at hr ⊢
    generalize hok : cs.all (linkv.MCmp.holds s.kv) = ok at hr ⊢
    generalize hq : linkv.runOps (s.rev + 1) s.kv (if ok = true then t else e) = q at hr ⊢
    have hsm := runOps_small (s.rev + 1) s.kv (if ok = true then t else e)
    rw [hq] at hsm
    have hql : (q.2.1.map encRes).length ≤ 3 := by
      rw [List.length_map, hsm.1]; split <;> assumption
    generalize hrv0 : (if q.2.2 = true then s.rev + 1 else s.rev) = rv at hr ⊢
    have hrv : uint.nat (W64 (rv : Int)) = rv := uint_nat_W64 _ hr
    obtain ⟨h1, h2⟩ := resOfL_withResL { zOut with Rev' := W64 (rv : Int), Ok' := ok } _ hql
    simp only [outOf]
    unfold decOut
    simp only [withResL, zOut] at h1 h2 ⊢
    simp only [Bool.false_eq_true, ↓reduceIte, hk, n40, n41, n42, n43, h2, h1, List.map_map,
      hrv]
    congr 2
    conv => rhs; rw [← List.map_id q.2.1]
    apply List.map_congr_left
    intro r hr
    exact decRes_encRes r (hsm.2 r hr)

/-- `outOf`'s header revision is the answer's. -/
theorem outOf_rev (o : MO) : (outOf o).Rev' = W64 (o.rev : Int) := by
  cases o with
  | get r v => cases v <;> rfl
  | _ => rfl

/-- A failed call's output decodes to the error. -/
theorem decOut_errOut (k : w64) : decOut k errOut = .err := rfl

/-! ## etcd's state -/

/-- A list's range: every workload key (`listFrom`, `listTo` in `linkvtxn.go`). -/
abbrev listFrom : GoString := go!"k"
abbrev listTo : GoString := go!"l"

/-- **The server's operation of the model input `i`.** -/
abbrev opIn (i : MI) : KVOp := linkv.opOf listFrom listTo i

/-- **A good state** (see the file header). -/
def GoodKV (σ : KVState) : Prop := σ.kvs.Pairwise etcdKvLess ∧ linkv.KeysIn wks σ

theorem inKeys_keysIn (i : MI) (h : inKeys i) : i.KeysIn wks := by
  cases i with
  | txn cs t e =>
    intro op hop
    have := h op hop
    cases op <;> exact this
  | _ => exact h

/-- Every step of a workload input keeps the state good. -/
theorem goodKV_step (σ : KVState) (h : GoodKV σ) (i : MI) (hi : i.KeysIn wks) :
    GoodKV (kvOpStep (opIn i) σ) :=
  ⟨linkv.kvOpStep_sorted _ σ, linkv.kvOpStep_keysIn wks listFrom listTo σ i hi h.2⟩

/-- An empty state is good. -/
theorem goodKV_empty (σ : KVState) (h : σ.kvs = []) : GoodKV σ :=
  ⟨KVState.kvs_sorted σ, fun _ he => by rw [h] at he; cases he⟩

/-- The list's range holds every workload key. -/
theorem wks_inRange : ∀ k ∈ wks, inRange listFrom listTo k = true := by
  decide

/-- **A step's state follows the model's**, on a good state. -/
theorem absSt_step (σ : KVState) (h : GoodKV σ) (i : MI) :
    linkv.absSt (kvOpStep (opIn i) σ) = (linkv.mStep wks i (linkv.absSt σ)).1 :=
  linkv.absSt_kvOpStep wks listFrom listTo σ h.1 i

/-- A step's revision: the same state, or the next revision. -/
theorem kvOpStep_cases (op : KVOp) (σ : KVState) :
    kvOpStep op σ = σ ∨ (kvOpStep op σ).rev = σ.rev + 1 := by
  have hc : ∀ cs, σ.commit cs = σ ∨ (σ.commit cs).rev = σ.rev + 1 := by
    intro cs
    by_cases h : cs = []
    · subst h; exact Or.inl (KVState.commit_nil σ)
    · exact Or.inr (KVState.commit_rev σ cs h)
  cases op with
  | put o =>
    simp only [kvOpStep]
    split
    · exact Or.inl rfl
    · exact hc _
  | range o => exact Or.inl rfl
  | deleteRange o => exact hc _
  | txn t =>
    simp only [kvOpStep]
    split
    · exact hc _
    · exact Or.inl rfl

end enc

end linkvtxn
end EtcdGrove
end Perennial
