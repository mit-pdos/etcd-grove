/-
**The link's pure lemmas** (wal-link L0, 2026-11-17; `notes/wal-link-scope.md` §3.1). Proved; no trusted
text. Layer 2's records are the eager model (`walSave`, `walSaveSnap`), layer 1's state a history `H`
(`WalHist`) read back by `walRead`. Here:

- the eager fold of a history appended by the server's `Save`s and `SaveSnap`s is `walSave`/`walSaveSnap`
  (`walFoldChkFrom_save_cons`, `walFoldChkFrom_snoc_save`, `walFoldChkFrom_snoc_snap`: the reader's
  `readEnt` fold is `appendEnts` for consecutive entries above the base, `WalSaveOk`'s case);
- **the read bridge** (`walRead_of_fold`): when the eager fold of `H` is `σ` with `σ.b ≤ σ.commit`, a
  restart reads `σ` (the reader drops only the snapshot records above the final commit, which the fold
  ignored: the base only grows, and a record above the final commit would have raised it above);
  Go evidence C1 (`examples/wallink/link_test.go`, `TestEagerModelReadsBack`: the guard is needed);
- the read's side conditions `walCommitLe`/`walIdxLe` from facts kept along the appends.

`WalSaveOk` (`WalRecs.lean`) is stated here unfolded (`WalSaveOkC`), so that layer 2's sealed module
can import this one.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.WalHistLemmas
public import Proof.go_etcd_io.raft.v3.Protocol.RaftState

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

section link
variable [GooseExts]

/-! ## The base only grows along a fold -/

theorem walFoldChkFrom_b_ge {τ σ : StorContents} {H : WalHist} (h : walFoldChkFrom τ H = some σ) :
    τ.b ≤ σ.b := by
  induction H generalizing τ with
  | nil => simp only [walFoldChkFrom, Option.some.injEq] at h; subst h; exact Nat.le_refl _
  | cons o H ih =>
    cases o with
    | snap m al =>
      simp only [walFoldChkFrom] at h
      exact Nat.le_trans (walSaveSnap_base_ge τ m).1 (ih h)
    | save hs es =>
      simp only [walFoldChkFrom, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨ents, -, h⟩ := h
      exact ih (τ := { τ with hs := phsNext τ.hs hs, ents := ents }) h

/-- A prefix of a successful fold succeeds. -/
theorem walFoldChkFrom_prefix {τ σ : StorContents} {H : WalHist} (n : Nat)
    (h : walFoldChkFrom τ H = some σ) : ∃ τ', walFoldChkFrom τ (H.take n) = some τ' ∧
      walFoldChkFrom τ' (H.drop n) = some σ := by
  have h' := h
  rw [← List.take_append_drop n H, walFoldChkFrom_append] at h'
  cases hA : walFoldChkFrom τ (H.take n) with
  | none => rw [hA] at h'; cases h'
  | some τ' => rw [hA] at h'; exact ⟨τ', rfl, h'⟩

/-! ## The read bridge -/

/-- Dropping the snapshot records above `c` changes nothing when the fold ends with its base at or
below `c`. -/
theorem walFoldChkFrom_filter_keep {c : Nat} {τ σ : StorContents} {H : WalHist}
    (h : walFoldChkFrom τ H = some σ) (hc : σ.b ≤ c) :
    walFoldChkFrom τ (H.filter (walKeep c)) = some σ := by
  induction H generalizing τ with
  | nil => exact h
  | cons o H ih =>
    cases o with
    | snap m al =>
      simp only [walFoldChkFrom] at h
      by_cases hm : uint.nat m.Index' ≤ c
      · simp only [List.filter_cons, walKeep, hm, decide_true, ite_true, walFoldChkFrom]
        exact ih h
      · simp only [List.filter_cons, walKeep, hm, decide_false, Bool.false_eq_true, ite_false]
        have hge := walFoldChkFrom_b_ge h
        rcases walSaveSnap_cases τ m with he | ⟨-, hb⟩
        · rw [he] at h; exact ih h
        · exfalso
          simp only [StorContents.b, hb] at hge
          simp only [StorContents.b] at hc
          omega
    | save hs es =>
      simp only [List.filter_cons, walKeep, ite_true, walFoldChkFrom, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at h ⊢
      obtain ⟨ents, he, h⟩ := h
      exact ⟨ents, he, ih h⟩

/-- A fold from the fresh records ends with the history's last saved hard state. -/
theorem walFoldChkFrom_fresh_hs {σ : StorContents} {H : WalHist}
    (h : walFoldChkFrom walFresh H = some σ) : σ.hs = walLastHS H := by
  rw [walFoldChkFrom_hs h, walLastHS_eq]; rfl

/-- **The read bridge** (Scope §3.1): when the eager fold of the history is `σ` and its base is at or
below its commit, a restart reads `σ`. -/
theorem walRead_of_fold {σ : StorContents} {H : WalHist}
    (h : walFoldChkFrom walFresh H = some σ) (hb : σ.b ≤ σ.commit) : walRead H = some σ := by
  unfold walRead
  rw [← walFoldChkFrom_fresh_hs h]
  exact walFoldChkFrom_filter_keep h hb

/-! ## The eager steps -/

/-- `WalSaveOk σ es` (`WalRecs.lean`), unfolded: consecutive entries above the base, the first at most
one past the last. -/
def WalSaveOkC (σ : StorContents) (es : List EntryM) : Prop :=
  ∀ e0, es.head? = some e0 → σ.b < uint.nat e0.Index' ∧ uint.nat e0.Index' ≤ σ.last + 1 ∧
    ∀ (j : Nat) (e : EntryM), es[j]? = some e → uint.nat e.Index' = uint.nat e0.Index' + j

/-- The reader's fold over consecutive entries from index `i > b`, the stored entries ending just below
`i`: the batch appended. -/
theorem readEnts_consec_full {b : Nat} : ∀ {es : List EntryM} {i : Nat} {ents : List EntryM},
    b < i → ents.length = i - b - 1 →
    (∀ (j : Nat) (e : EntryM), es[j]? = some e → uint.nat e.Index' = i + j) →
    es.foldlM (fun ents e => readEnt b ents e) ents = some (ents ++ es) := by
  intro es
  induction es with
  | nil => intro i ents _ _ _; simp
  | cons e es ih =>
    intro i ents hb hl hc
    have he : uint.nat e.Index' = i := by have := hc 0 e (by simp); omega
    have hr : readEnt b ents e = some (ents ++ [e]) := by
      unfold readEnt
      rw [ite_eq_right_of_eq_false _ _ (by simp only [eq_iff_iff, iff_false]; omega),
        ite_eq_left_of_eq_true _ _ (by simp only [eq_iff_iff, iff_true]; omega), he,
        List.take_of_length_le (by omega)]
    simp only [List.foldlM_cons, Option.bind_eq_bind, hr, Option.bind_some]
    rw [ih (i := i + 1) (by omega) (by simp; omega)
      (fun j x hx => by have := hc (j + 1) x (by simpa using hx); omega)]
    simp

/-- The reader's fold over a nonempty batch of consecutive entries from index `i > b`: the stored
entries cut below `i`, then the batch. -/
theorem readEnts_consec {b : Nat} {e : EntryM} {es : List EntryM} {i : Nat} {ents : List EntryM}
    (hb : b < i) (hl : i - b - 1 ≤ ents.length)
    (hc : ∀ (j : Nat) (x : EntryM), (e :: es)[j]? = some x → uint.nat x.Index' = i + j) :
    (e :: es).foldlM (fun ents e => readEnt b ents e) ents =
      some (ents.take (i - b - 1) ++ (e :: es)) := by
  have he : uint.nat e.Index' = i := by have := hc 0 e (by simp); omega
  have hr : readEnt b ents e = some (ents.take (i - b - 1) ++ [e]) := by
    unfold readEnt
    rw [ite_eq_right_of_eq_false _ _ (by simp only [eq_iff_iff, iff_false]; omega),
      ite_eq_left_of_eq_true _ _ (by simp only [eq_iff_iff, iff_true]; omega), he]
  simp only [List.foldlM_cons, Option.bind_eq_bind, hr, Option.bind_some]
  rw [readEnts_consec_full (i := i + 1) (by omega) (by simp; omega)
    (fun j x hx => by have := hc (j + 1) x (by simpa using hx); omega)]
  simp

/-- `appendEnts` in `WalSaveOk`'s case: the stored entries cut below the batch's first, then the
batch. -/
theorem appendEnts_consec {σ : StorContents} {es : List EntryM} {e0 : EntryM} (he0 : es.head? = some e0)
    (hb : σ.b < uint.nat e0.Index') :
    appendEnts σ.base σ.ents es = σ.ents.take (uint.nat e0.Index' - σ.b - 1) ++ es := by
  cases es with
  | nil => cases he0
  | cons x es =>
    simp only [List.head?_cons, Option.some.injEq] at he0; subst he0
    unfold appendEnts plogTruncateAppend
    simp only [StorContents.b] at hb
    have h0 : (uint.Z σ.base.index' + 1 - uint.Z x.Index').toNat = 0 := by
      word
    dsimp only
    rw [h0, List.drop_zero]
    dsimp only
    simp only [StorContents.b]
    congr 2
    word

/-- **The eager `Save` step**: in `WalSaveOk`'s case the fold of a `save` record is `walSave`'s update
(`{σ with hs := phsNext σ.hs h, ents := appendEnts σ.base σ.ents es}`). -/
theorem walFoldChkFrom_save_cons {τ : StorContents} {h : HardStateM} {es : List EntryM} {H : WalHist}
    (hok : WalSaveOkC τ es) :
    walFoldChkFrom τ (.save h es :: H) =
      walFoldChkFrom { τ with hs := phsNext τ.hs h, ents := appendEnts τ.base τ.ents es } H := by
  simp only [walFoldChkFrom, Option.bind_eq_bind]
  cases hes : es.head? with
  | none =>
    have : es = [] := List.head?_eq_none_iff.mp hes
    subst this
    simp only [List.foldlM_nil, Option.pure_def, Option.bind_some, appendEnts]
  | some e0 =>
    obtain ⟨hb, hl, hc⟩ := hok e0 hes
    obtain ⟨x, es', rfl⟩ : ∃ x es', es = x :: es' := by
      cases es with | nil => cases hes | cons x es' => exact ⟨x, es', rfl⟩
    rw [readEnts_consec (i := uint.nat e0.Index') hb
      (by simp only [StorContents.last] at hl; omega) hc, appendEnts_consec hes hb]
    rfl

theorem walFoldChkFrom_snoc_save {τ σ : StorContents} {H : WalHist} {h : HardStateM}
    {es : List EntryM} (hH : walFoldChkFrom τ H = some σ) (hok : WalSaveOkC σ es) :
    walFoldChkFrom τ (H ++ [.save h es]) =
      some { σ with hs := phsNext σ.hs h, ents := appendEnts σ.base σ.ents es } := by
  rw [walFoldChkFrom_append, hH, Option.bind_some, walFoldChkFrom_save_cons hok]; rfl

theorem walFoldChkFrom_snoc_snap {τ σ : StorContents} {H : WalHist} {m : SnapshotMetadataM} {al : Bool}
    (hH : walFoldChkFrom τ H = some σ) :
    walFoldChkFrom τ (H ++ [.snap m al]) = some (walSaveSnap σ m) := by
  rw [walFoldChkFrom_append, hH, Option.bind_some]; rfl

/-! ## The read's side conditions -/

/-- `walCommitLeFrom` along an append: the new whole fold has its commit within its last index. -/
theorem walCommitLeFrom_snoc {τ σ : StorContents} {H : WalHist} {o : WalOp}
    (hc : walCommitLeFrom τ H) (h : walFoldChkFrom τ (H ++ [o]) = some σ) (hσ : σ.commit ≤ σ.last) :
    walCommitLeFrom τ (H ++ [o]) := by
  intro n τ' hn
  rcases Nat.lt_or_ge n (H.length + 1) with hlt | hge
  · rcases Nat.lt_or_ge n (H.length) with hlt' | hge'
    · rw [List.take_append_of_le_length (by omega)] at hn; exact hc n τ' hn
    · have : n = H.length := by omega
      subst this
      rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length] at hn
      exact hc H.length τ' (by rw [List.take_length]; exact hn)
  · rw [List.take_of_length_le (by simp; omega)] at hn
    rw [h] at hn; cases hn; exact hσ

/-- (walcommitle, 2026-11-28) **`walCommitLeFrom` along a snapshot record**: `SaveSnapshot` keeps the
whole fold's commit within its last index (as `WalEnc.walSaveSnap_commitLe`, which `WalReadAllPost` proves
above this module). -/
theorem walCommitLeFrom_snoc_snap {τ σ : StorContents} {H : WalHist} {m : SnapshotMetadataM} {al : Bool}
    (hc : walCommitLeFrom τ H) (hH : walFoldChkFrom τ H = some σ) :
    walCommitLeFrom τ (H ++ [.snap m al]) := by
  have h : σ.commit ≤ σ.last := hc H.length σ (by rw [List.take_length]; exact hH)
  refine walCommitLeFrom_snoc hc (walFoldChkFrom_snoc_snap hH) ?_
  unfold walSaveSnap
  split
  · exact h
  · next hlt =>
    by_cases hcm : uint.nat m.Index' ≤ σ.commit
    · rw [if_pos hcm]
      simp only [StorContents.commit, StorContents.last, StorContents.b, List.length_drop] at h hlt hcm ⊢
      omega
    · rw [if_neg hcm]
      simp only [StorContents.commit, StorContents.last, StorContents.b, List.length_nil] at h hlt hcm ⊢
      omega

theorem walCommitLeFrom_nil (τ : StorContents) (hτ : τ.commit ≤ τ.last) : walCommitLeFrom τ [] := by
  intro n τ' hn
  simp only [List.take_nil, walFoldChkFrom, Option.some.injEq] at hn; subst hn; exact hτ

/-- Every prefix of the filtered history is the filter of a prefix of the history. -/
theorem filter_take_exists {α : Type} (p : α → Bool) : ∀ (H : List α) (n : Nat),
    ∃ m, (H.filter p).take n = (H.take m).filter p := by
  intro H
  induction H with
  | nil => intro n; exact ⟨0, by simp⟩
  | cons a H ih =>
    intro n
    cases n with
    | zero => exact ⟨0, by simp⟩
    | succ n =>
      by_cases ha : p a = true
      · obtain ⟨m, hm⟩ := ih n
        exact ⟨m + 1, by simp [ha, hm]⟩
      · obtain ⟨m, hm⟩ := ih (n + 1)
        exact ⟨m + 1, by simp [ha, hm]⟩

/-- **The read's `walCommitLe` from the fold's**: when the eager fold of `H` is `σ` with `σ.b ≤ σ.commit`
and every prefix of the (unfiltered) fold has its commit within its last index, so has every prefix
of the reader's (filtered) fold. -/
theorem walCommitLe_of_fold {σ : StorContents} {H : WalHist}
    (h : walFoldChkFrom walFresh H = some σ) (hb : σ.b ≤ σ.commit) (hc : walCommitLeFrom walFresh H) :
    walCommitLe H := by
  unfold walCommitLe
  rw [← walFoldChkFrom_fresh_hs h]
  intro n τ' hn
  obtain ⟨m, hm⟩ := filter_take_exists (walKeep (uint.nat σ.hs.Commit')) H n
  rw [hm] at hn
  obtain ⟨τm, hτm, hrest⟩ := walFoldChkFrom_prefix m h
  have hle : τm.b ≤ uint.nat σ.hs.Commit' := Nat.le_trans (walFoldChkFrom_b_ge hrest) hb
  rw [walFoldChkFrom_filter_keep hτm hle] at hn
  simp only [Option.some.injEq] at hn; subst hn
  exact hc m _ hτm

theorem walIdxLe_nil (B : Nat) : walIdxLe B [] :=
  ⟨fun _ _ _ h _ => (by cases h), fun _ _ h => (by cases h)⟩

theorem walIdxLe_append {B : Nat} {A C : WalHist} (hA : walIdxLe B A) (hC : walIdxLe B C) :
    walIdxLe B (A ++ C) := by
  refine ⟨fun hs es e ho he => ?_, fun m al ho => ?_⟩
  · rcases List.mem_append.mp ho with ho | ho
    · exact hA.1 hs es e ho he
    · exact hC.1 hs es e ho he
  · rcases List.mem_append.mp ho with ho | ho
    · exact hA.2 m al ho
    · exact hC.2 m al ho

theorem walIdxLe_save {B : Nat} {h : HardStateM} {es : List EntryM}
    (hes : ∀ e ∈ es, uint.nat e.Index' ≤ B) : walIdxLe B [.save h es] := by
  refine ⟨fun hs es' e ho he => ?_, fun m al ho => ?_⟩
  · simp only [List.mem_singleton, WalOpG.save.injEq] at ho
    obtain ⟨-, rfl⟩ := ho; exact hes e he
  · simp at ho

theorem walIdxLe_snap {B : Nat} {m : SnapshotMetadataM} {al : Bool} (hm : uint.nat m.Index' ≤ B) :
    walIdxLe B [.snap m al] := by
  refine ⟨fun hs es' e ho he => ?_, fun m' al' ho => ?_⟩
  · simp at ho
  · simp only [List.mem_singleton, WalOpG.snap.injEq] at ho; obtain ⟨rfl, -⟩ := ho; exact hm

/-! ## The fold commutes with a map of the entries keeping their indices (wal-link L1b)

The server's WAL history holds wrapped entry models (`RaftModel/Srv.lean`, `walEntW`); the server reads
them through `walEntUnwrap`, which keeps the index: the checked fold and the read of the mapped history
are the mapped ones. -/

/-- An operation with its entries mapped. -/
def walOpMapE (f : EntryM → EntryM) : WalOp → WalOp
  | .save h es => .save h (es.map f)
  | .snap m al => .snap m al

/-- A record state with its entries mapped. -/
def storMapE (f : EntryM → EntryM) (σ : StorContents) : StorContents := { σ with ents := σ.ents.map f }

theorem storMapE_b (f : EntryM → EntryM) (σ : StorContents) : (storMapE f σ).b = σ.b := rfl

theorem readEnt_map (f : EntryM → EntryM) (hf : ∀ e, (f e).Index' = e.Index') (b : Nat)
    (ents : List EntryM) (e : EntryM) :
    readEnt b (ents.map f) (f e) = (readEnt b ents e).map (List.map f) := by
  unfold readEnt
  rw [hf e]
  by_cases h1 : uint.nat e.Index' ≤ b
  · simp [h1]
  · by_cases h2 : uint.nat e.Index' - b - 1 ≤ ents.length
    · simp [h1, h2, List.map_take]
    · simp [h1, h2]

theorem foldlM_readEnt_map (f : EntryM → EntryM) (hf : ∀ e, (f e).Index' = e.Index') (b : Nat)
    (es ents : List EntryM) :
    (es.map f).foldlM (fun ents e => readEnt b ents e) (ents.map f) =
      (es.foldlM (fun ents e => readEnt b ents e) ents).map (List.map f) := by
  induction es generalizing ents with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons, List.foldlM_cons, readEnt_map f hf]
    cases readEnt b ents e with
    | none => rfl
    | some x => exact ih x

theorem walSaveSnap_map (f : EntryM → EntryM) (σ : StorContents) (m : SnapshotMetadataM) :
    walSaveSnap (storMapE f σ) m = storMapE f (walSaveSnap σ m) := by
  unfold walSaveSnap storMapE
  simp only [StorContents.b, StorContents.commit]
  by_cases h1 : uint.nat m.Index' < uint.nat σ.base.index' <;>
    by_cases h2 : uint.nat m.Index' ≤ uint.nat σ.hs.Commit' <;> simp [h1, h2, List.map_drop]

/-- **The checked fold of a mapped history is the mapped fold.** -/
theorem walFoldChkFrom_map (f : EntryM → EntryM) (hf : ∀ e, (f e).Index' = e.Index') :
    ∀ (σ : StorContents) (H : WalHist),
      walFoldChkFrom (storMapE f σ) (H.map (walOpMapE f)) = (walFoldChkFrom σ H).map (storMapE f)
  | σ, [] => rfl
  | σ, .snap m _ :: H => by
    simp only [List.map_cons, walOpMapE, walFoldChkFrom]
    rw [walSaveSnap_map, walFoldChkFrom_map f hf _ H]
  | σ, .save h es :: H => by
    simp only [List.map_cons, walOpMapE, walFoldChkFrom]
    rw [show (storMapE f σ).ents = σ.ents.map f from rfl, storMapE_b,
      foldlM_readEnt_map f hf]
    cases es.foldlM (fun ents e => readEnt σ.b ents e) σ.ents with
    | none => rfl
    | some x =>
      simp only [Option.map_some, Option.bind_some]
      exact walFoldChkFrom_map f hf { σ with hs := phsNext σ.hs h, ents := x } H

theorem walLastHS_map (f : EntryM → EntryM) (H : WalHist) :
    walLastHS (H.map (walOpMapE f)) = walLastHS H := by
  unfold walLastHS
  rw [List.foldl_map]
  congr 1
  funext p o
  cases o <;> rfl

/-- **The read of a mapped history is the mapped read.** -/
theorem walRead_map (f : EntryM → EntryM) (hf : ∀ e, (f e).Index' = e.Index') (H : WalHist) :
    walRead (H.map (walOpMapE f)) = (walRead H).map (storMapE f) := by
  unfold walRead
  rw [walLastHS_map]
  have hk : (walKeep (uint.nat (walLastHS H).Commit') ∘ walOpMapE f) =
      walKeep (uint.nat (walLastHS H).Commit') := by
    funext o; cases o <;> rfl
  rw [List.filter_map, hk]
  exact walFoldChkFrom_map f hf walFresh _

end link

end EtcdGrove
end Perennial
