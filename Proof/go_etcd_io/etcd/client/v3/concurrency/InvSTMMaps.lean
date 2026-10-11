/-
Lemmas for the proofs of `stm.go`'s Go-map methods (`readSet.*`, `writeSet.*`, `stm.Put`,
`stm.Del`, `stm.reset`, `stmSerializable.gets`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvSTM

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

theorem stm_deleteOp_txnOpOf (key : GoString) :
    txnOpOf (opDeleteModel key []) = some (.delete (opDeleteModel key [])) := by
  simp [opDeleteModel, opFold, OpFull.deleteInit, OpFull.newOp, OpModel.zero, txnOpOf]

/-! ## Map sizes -/

theorem GMap_size_eq_of_dom {V1 V2 : Type} (m1 : GMap GoString V1) (m2 : GMap GoString V2)
    (h : ∀ k, (m1 !! k).isSome = (m2 !! k).isSome) : GMap.size m1 = GMap.size m2 := by
  rw [GMap.size_eq_length m1 m2.domList (GMap.nodup_dom_list m2)
    (fun k => by rw [GMap.mem_dom_list, h]), GMap.size_eq_dom_list_length]

/-! ## `readSet.first` -/

/-- `first()`'s loop invariant: `r` is the least of `2^63 - 2` and the header revisions of the
reads of the first `n` keys of `keys`. -/
def FirstUpTo (reads : GMap GoString ReadM) (keys : List GoString) (n : Nat) (r : w64) : Prop :=
  sint.Z r ≤ 2 ^ 63 - 2 ∧
    (∀ j k e, j < n → keys[j]? = some k → reads !! k = some e → sint.Z r ≤ sint.Z e.hdr) ∧
    (r = W64 (2 ^ 63 - 2) ∨ ∃ k e, reads !! k = some e ∧ r = e.hdr)

theorem FirstUpTo_init (reads : GMap GoString ReadM) (keys : List GoString) :
    FirstUpTo reads keys 0 (W64 (2 ^ 63 - 2)) :=
  ⟨by decide, fun _ _ _ h => absurd h (Nat.not_lt_zero _), .inl rfl⟩

theorem FirstUpTo_step {reads : GMap GoString ReadM} {keys : List GoString} {n : Nat} {r : w64}
    {k : GoString} {e : ReadM} (h : FirstUpTo reads keys n r) (hk : keys[n]? = some k)
    (he : reads !! k = some e) :
    FirstUpTo reads keys (n + 1) (if sint.Z e.hdr < sint.Z r then e.hdr else r) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hj : ∀ j k' e', j < n + 1 → keys[j]? = some k' → reads !! k' = some e' →
      (j < n ∨ (k' = k ∧ e' = e)) := by
    intro j k' e' hj hk' he'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · exact .inl hj
    · subst hj; rw [hk] at hk'; cases hk'; rw [he] at he'; cases he'; exact .inr ⟨rfl, rfl⟩
  split
  · rename_i hlt
    refine ⟨by omega, ?_, .inr ⟨k, e, he, rfl⟩⟩
    intro j k' e' hjn hk' he'
    rcases hj j k' e' hjn hk' he' with hj | ⟨rfl, rfl⟩
    · have := h2 j k' e' hj hk' he'; omega
    · exact Int.le_refl _
  · rename_i hlt
    refine ⟨h1, ?_, h3⟩
    intro j k' e' hjn hk' he'
    rcases hj j k' e' hjn hk' he' with hj | ⟨rfl, rfl⟩
    · exact h2 j k' e' hj hk' he'
    · omega

theorem FirstUpTo_final {reads : GMap GoString ReadM} {rsMap : GMap GoString Loc}
    {keys : List GoString} {r : w64} (h : FirstUpTo reads keys keys.length r)
    (hdom : ∀ k, (rsMap !! k).isSome = (reads !! k).isSome)
    (hkeys : ∀ k, k ∈ keys ↔ (rsMap !! k).isSome) : FirstOk reads r := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, ?_⟩
  · intro k e he
    have hk : k ∈ keys := (hkeys k).2 (by rw [hdom, he]; rfl)
    obtain ⟨j, hj, hjk⟩ := List.getElem_of_mem hk
    exact h2 j k e hj (by rw [List.getElem?_eq_getElem hj, hjk]) he
  · rcases h3 with h3 | h3
    · exact .inl (by rw [h3])
    · exact .inr h3

/-! ## Lists built by appending in a map's order -/

theorem filterMap_take_succ {A B : Type} (f : A → Option B) (l : List A) (n : Nat) (a : A) (b : B)
    (ha : l[n]? = some a) (hb : f a = some b) :
    (l.take (n + 1)).filterMap f = (l.take n).filterMap f ++ [b] := by
  rw [List.take_add_one, ha]
  simp [List.filterMap_append, hb]

theorem map_take_succ {A B : Type} (f : A → B) (l : List A) (n : Nat) (a : A)
    (ha : l[n]? = some a) :
    (l.take (n + 1)).map f = (l.take n).map f ++ [f a] := by
  rw [List.take_add_one, ha]
  simp

/-! ## `readSet.add` -/

theorem readsAdd_take_succ (reads : GMap GoString ReadM) (ks : List GoString) (es : List ReadM)
    (n : Nat) (k : GoString) (e : ReadM) (hk : ks[n]? = some k) (he : es[n]? = some e) :
    readsAdd reads ((ks.zip es).take (n + 1)) =
      GMap.insert k e (readsAdd reads ((ks.zip es).take n)) := by
  have hz : (ks.zip es)[n]? = some (k, e) := by
    rw [List.getElem?_zip_eq_some]; exact ⟨hk, he⟩
  rw [List.take_add_one, hz]
  simp [readsAdd, List.foldl_append]

theorem readsAdd_take_all (reads : GMap GoString ReadM) (ks : List GoString) (es : List ReadM)
    (h : es.length ≤ ks.length) :
    readsAdd reads ((ks.zip es).take es.length) = readsAdd reads (ks.zip es) := by
  rw [List.take_of_length_le]
  simp [List.length_zip]; omega

section iprop
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- A write added to the write set. -/
theorem writesAt_insert (pfx k : GoString) (wsMap : GMap GoString stmPut)
    (writes : GMap GoString WriteM) (sp : stmPut) (w : WriteM) :
    writesAt (GF := GF) pfx wsMap writes ∗ writeAt pfx k sp w ⊢
      writesAt pfx (GMap.insert k sp wsMap) (GMap.insert k w writes) := by
  unfold writesAt
  iintro ⟨⟨%Hdom, #Hall⟩, #Hw⟩
  isplitr
  · ipureintro
    intro k'
    by_cases h : k' = k
    · subst h; simp
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm h), GMap.lookup_insert_ne _ _ (Ne.symm h)]
      exact Hdom k'
  imodintro
  iintro %k' %sp' %w' %Hsp %Hw'
  by_cases h : k' = k
  · subst h
    rw [GMap.lookup_insert] at Hsp Hw'
    cases Hsp; cases Hw'
    iexact Hw
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm h)] at Hsp Hw'
    iapply Hall $$ %k' %sp' %w' %Hsp %Hw'

/-- A read added to the read set. -/
theorem readsAt_insert (pfx k : GoString) (rsMap : GMap GoString Loc)
    (reads : GMap GoString ReadM) (p : Loc) (e : ReadM) :
    readsAt (GF := GF) pfx rsMap reads ∗ readRespAt pfx k p e ⊢
      readsAt pfx (GMap.insert k p rsMap) (GMap.insert k e reads) := by
  unfold readsAt
  iintro ⟨⟨%Hdom, #Hall⟩, #Hr⟩
  isplitr
  · ipureintro
    intro k'
    by_cases h : k' = k
    · subst h; simp
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm h), GMap.lookup_insert_ne _ _ (Ne.symm h)]
      exact Hdom k'
  imodintro
  iintro %k' %p' %e' %Hp %He
  by_cases h : k' = k
  · subst h
    rw [GMap.lookup_insert] at Hp He
    cases Hp; cases He
    iexact Hr
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm h)] at Hp He
    iapply Hall $$ %k' %p' %e' %Hp %He

/-- Two lists related pointwise by a persistent predicate, extended by a related pair. -/
theorem pointwise_snoc {A B : Type} (P : A → B → IProp GF) [∀ a b, Persistent (P a b)]
    (xs : List A) (ys : List B) (a : A) (b : B) (hlen : xs.length = ys.length) :
    (□ ∀ (i : Nat) (x : A) (y : B), ⌜xs[i]? = some x⌝ -∗ ⌜ys[i]? = some y⌝ -∗ P x y) ∗ P a b ⊢
      □ ∀ (i : Nat) (x : A) (y : B), ⌜(xs ++ [a])[i]? = some x⌝ -∗ ⌜(ys ++ [b])[i]? = some y⌝ -∗
        P x y := by
  iintro ⟨#H, #Hp⟩
  imodintro
  iintro %i %x %y %hx %hy
  rcases Nat.lt_or_ge i xs.length with h | h
  · rw [List.getElem?_append_left h] at hx
    rw [List.getElem?_append_left (by omega)] at hy
    iapply H $$ %i %x %y %hx %hy
  · rw [List.getElem?_append_right h] at hx
    rw [List.getElem?_append_right (by omega)] at hy
    rcases Nat.lt_or_ge (i - xs.length) 1 with h' | h'
    · rw [show i - xs.length = 0 by omega] at hx
      rw [show i - ys.length = 0 by omega] at hy
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hy
      subst hx; subst hy
      iexact Hp
    · rw [List.getElem?_eq_none (by simp; omega)] at hx
      cases hx

/-- The empty pointwise relation. -/
theorem pointwise_nil {A B : Type} (P : A → B → IProp GF) :
    ⊢ (□ ∀ (i : Nat) (x : A) (y : B), ⌜([] : List A)[i]? = some x⌝ -∗
        ⌜([] : List B)[i]? = some y⌝ -∗ P x y : IProp GF) := by
  imodintro
  iintro %i %x %y %hx %hy
  simp at hx

end iprop

end concurrency
end EtcdGrove
end Perennial
