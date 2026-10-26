/-
Lean-first (no Rocq counterpart).

# linkvtxn: the generator's inputs (linkv-txn stage G)

What `Gen` returns is an input `Apply` may take (`GenIn`): `genFrom`'s cases, by the decoder.

- `TxnShape r cs ts es`: a transaction whose comparisons and operations are `cs`, `ts`, `es`
  (`cmpsOfL`, `thenOfL`, `elseOfL`), its counts in the decoder's bounds; `decIn_txnShape`: it
  decodes as their decodings.
- `genIn_txn`: such a transaction of decodable comparisons and operations on the workload's keys,
  not empty, is one `Apply` may take; `genIn_key`: a get, a list, a put or a delete of a workload
  key.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Calls

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open github_com.mit_pdos.etcd_grove.examples.linkvtxn

section gen
variable [GooseExts]

/-- **A transaction input's shape** (see the file header). -/
def TxnShape (r : Input) (cs : List Cmp) (ts es : List TOp) : Prop :=
  r.Kind' = W64 4 ∧ 0 ≤ sint.Z r.NCmps' ∧ sint.Z r.NCmps' ≤ 1 ∧ 0 ≤ sint.Z r.NThen' ∧
    sint.Z r.NThen' ≤ 3 ∧ 0 ≤ sint.Z r.NElse' ∧ sint.Z r.NElse' ≤ 1 ∧
    cmpsOfL r = cs ∧ thenOfL r = ts ∧ elseOfL r = es

theorem decIn_txnShape (r : Input) (cs : List Cmp) (ts es : List TOp) (h : TxnShape r cs ts es) :
    decIn r = (decAll decCmp cs).bind fun c => (decAll decTOp ts).bind fun t =>
      (decAll decTOp es).map fun e => .txn c t e := by
  obtain ⟨hk, h1, h2, h3, h4, h5, h6, hc, ht, he⟩ := h
  unfold decIn
  rw [hk, if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_pos ⟨rfl, h1, h2, h3, h4, h5, h6⟩, hc, ht, he]

theorem decTOp_key (o : TOp) (m : linkv.MOp GoString GoString) (h : decTOp o = some m) :
    mopKey m = o.Key' := by
  unfold decTOp at h
  split at h
  · cases h; rfl
  split at h
  · cases h; rfl
  split at h
  · cases h; rfl
  · cases h

theorem decAll_keys (os : List TOp) (ms : List (linkv.MOp GoString GoString))
    (h : decAll decTOp os = some ms) (hk : ∀ o ∈ os, o.Key' ∈ wks) : ∀ m ∈ ms, mopKey m ∈ wks := by
  intro m hm
  obtain ⟨k, hk'⟩ := List.getElem_of_mem hm
  obtain ⟨hlt, rfl⟩ := hk'
  have hlen := decAll_length _ _ _ h
  obtain ⟨o, ho⟩ : ∃ o, os[k]? = some o := ⟨os[k], List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨b, hb, hb'⟩ := decAll_getElem decTOp os ms h k o ho
  rw [List.getElem?_eq_getElem hlt] at hb'
  cases hb'
  rw [decTOp_key o _ hb]
  exact hk o (List.mem_of_getElem? ho)

/-- **A transaction `Gen` makes is one `Apply` takes** (see the file header). -/
theorem genIn_txn (r : Input) (cs : List Cmp) (ts es : List TOp) (h : TxnShape r cs ts es)
    (c : List (linkv.MCmp GoString GoString)) (t e : List (linkv.MOp GoString GoString))
    (hc : decAll decCmp cs = some c) (ht : decAll decTOp ts = some t)
    (he : decAll decTOp es = some e) (hk : ∀ o ∈ ts ++ es, o.Key' ∈ wks) (hne : ts ++ es ≠ []) :
    GenIn r := by
  have hd := decIn_txnShape r cs ts es h
  rw [hc, ht, he] at hd
  simp only [Option.bind_some, Option.map_some] at hd
  refine ⟨⟨_, hd, ?_⟩, fun c' t' e' h' => ?_⟩
  · intro op hop
    rcases List.mem_append.1 hop with hop | hop
    · exact decAll_keys ts t ht (fun o ho => hk o (List.mem_append_left _ ho)) op hop
    · exact decAll_keys es e he (fun o ho => hk o (List.mem_append_right _ ho)) op hop
  · rw [hd] at h'
    cases h'
    intro hnil
    apply hne
    have h1 := decAll_length _ _ _ ht
    have h2 := decAll_length _ _ _ he
    rw [List.append_eq_nil_iff] at hnil ⊢
    exact ⟨List.eq_nil_of_length_eq_zero (by rw [← h1, hnil.1]; rfl),
      List.eq_nil_of_length_eq_zero (by rw [← h2, hnil.2]; rfl)⟩

/-- A get, a list, a put or a delete of a workload key is an input `Apply` takes. -/
theorem genIn_key (r : Input) (hk : r.Kind' ≠ W64 1 → r.Key' ∈ wks)
    (hkind : r.Kind' = W64 0 ∨ r.Kind' = W64 1 ∨ r.Kind' = W64 2 ∨ r.Kind' = W64 3) :
    GenIn r := by
  have hnt : ∀ cs t e, decIn r ≠ some (.txn cs t e) := by
    intro cs t e h
    unfold decIn at h
    rcases hkind with h' | h' | h' | h' <;> simp [h'] at h
  refine ⟨?_, fun cs t e h => absurd h (hnt cs t e)⟩
  rcases hkind with h' | h' | h' | h'
  · exact ⟨.get r.Key', by unfold decIn; simp [h'], hk (by rw [h']; decide)⟩
  · exact ⟨.list, by unfold decIn; simp [h'], trivial⟩
  · exact ⟨.put r.Key' r.Val', by unfold decIn; simp [h'], hk (by rw [h']; decide)⟩
  · exact ⟨.del r.Key', by unfold decIn; simp [h'], hk (by rw [h']; decide)⟩

/-- A word below `3`. -/
theorem w64_lt3 (k : w64) (h : uint.Z k < 3) : k = W64 0 ∨ k = W64 1 ∨ k = W64 2 := by
  have h0 : 0 ≤ uint.Z k := by word
  rcases (by omega : uint.Z k = 0 ∨ uint.Z k = 1 ∨ uint.Z k = 2) with h' | h' | h'
  · left; word
  · right; left; word
  · right; right; word

theorem decTOp_some (o : TOp) (h : uint.Z o.Kind' < 3) : ∃ m, decTOp o = some m := by
  unfold decTOp
  rcases w64_lt3 _ h with h' | h' | h' <;> simp [h']

theorem decCmp_some (c : Cmp) (h : uint.Z c.Kind' < 3) : ∃ m, decCmp c = some m := by
  unfold decCmp
  rcases w64_lt3 _ h with h' | h' | h' <;> simp [h']

theorem decAll_some {α β : Type} (f : α → Option β) :
    ∀ l : List α, (∀ a ∈ l, ∃ b, f a = some b) → ∃ l', decAll f l = some l'
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a List.mem_cons_self
    obtain ⟨l', hl'⟩ := decAll_some f l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    exact ⟨b :: l', by simp [decAll, hb, hl']⟩

/-- **A transaction input of decodable comparisons and operations on the workload's keys, not
empty, is one `Apply` takes** (`genIn_txn` at its own lists). -/
theorem genIn_txn' (r : Input) (hk : r.Kind' = W64 4) (h1 : 0 ≤ sint.Z r.NCmps')
    (h2 : sint.Z r.NCmps' ≤ 1) (h3 : 0 ≤ sint.Z r.NThen') (h4 : sint.Z r.NThen' ≤ 3)
    (h5 : 0 ≤ sint.Z r.NElse') (h6 : sint.Z r.NElse' ≤ 1)
    (hc : ∀ c ∈ cmpsOfL r, uint.Z c.Kind' < 3)
    (ho : ∀ o ∈ thenOfL r ++ elseOfL r, uint.Z o.Kind' < 3 ∧ o.Key' ∈ wks)
    (hne : thenOfL r ++ elseOfL r ≠ []) : GenIn r := by
  obtain ⟨c, hc'⟩ := decAll_some decCmp _ (fun a ha => decCmp_some a (hc a ha))
  obtain ⟨t, ht'⟩ := decAll_some decTOp (thenOfL r)
    (fun a ha => decTOp_some a (ho a (List.mem_append_left _ ha)).1)
  obtain ⟨e, he'⟩ := decAll_some decTOp (elseOfL r)
    (fun a ha => decTOp_some a (ho a (List.mem_append_right _ ha)).1)
  exact genIn_txn r _ _ _ ⟨hk, h1, h2, h3, h4, h5, h6, rfl, rfl, rfl⟩ c t e hc' ht' he'
    (fun o h => (ho o h).2) hne

theorem thenOfL_subset (x : Input) : ∀ o ∈ thenOfL x, o = x.Then0' ∨ o = x.Then1' ∨ o = x.Then2' := by
  intro o ho
  unfold thenOfL at ho
  simp only [List.mem_append] at ho
  rcases ho with (ho | ho) | ho <;> split at ho <;> simp_all

end gen

end linkvtxn
end EtcdGrove
end Perennial
