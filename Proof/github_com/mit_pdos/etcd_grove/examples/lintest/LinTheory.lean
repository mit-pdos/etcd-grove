/-
Lean-first (no Rocq counterpart).

# lintest: a traced history is linearizable (2026-10-14)

The pure argument behind `Run`: `n` clients each ran `m` operations; client `c`'s trace is
`hs[c]`, and the whole history is their concatenation `hs.flatten` (what `Run` passes to
porcupine), so client `c`'s `j`-th operation is operation `c * m + j` of the history.

The proof's ghost log `L` lists the operations in the order in which they took effect
(their linearization points), each with its client `c`, its index `j` in the client's trace,
its input and output `io`, and the clock's value `τ` at its linearization point
(`LinRec`). What the program logic gives (`LogOk`):

- the log's operations of client `c` are, in order, the client's records `Lcs[c]`
  (`clientRecs`): its `j`-th record is its `j`-th operation, with the trace's input and
  output, and the trace's call and return times around `τ` (the call timestamp was read
  before the linearization point, the return timestamp after, from a monotone clock);
- `τ` never decreases along the log (the clock is monotone);
- the model runs the log's operations from its initial state.

Then the log, as indices of the history (`c * m + j`), is a linearization in porcupine's
sense (`Theory.Linearizable`): every operation once, allowed by the model, and an operation
that returned before another was called comes first (if `b` follows `a` in the log, then
`a.call ≤ τa ≤ τb ≤ b.ret`, so `b` did not return before `a` was called).
-/
module

public import Proof.github_com.anishathalye.porcupine.Theory

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace lintest

open github_com.anishathalye.porcupine.Theory

variable {σ α : Type}

/-- An entry of the ghost log: client `c`'s `j`-th operation, which did `io`, linearized
when the clock read `τ`. -/
structure LinRec (α : Type) where
  c : Nat
  j : Nat
  io : α
  τ : Int

/-- Client `c`'s records (its operations' `io` and `τ`, in order) as log entries. -/
def clientRecs (c : Nat) (Lc : List (α × Int)) : List (LinRec α) :=
  Lc.mapIdx fun j p => ⟨c, j, p.1, p.2⟩

/-- The `j`-th operation of the trace `o` is described by the record `p`: same input and
output, and the record's `τ` is between its call and its return. -/
def RecOk (o : Op α) (p : α × Int) : Prop :=
  o.val = p.1 ∧ o.call ≤ p.2 ∧ p.2 ≤ o.ret

/-- What the program logic establishes about the clients' traces `hs`, their records `Lcs`
and the log `L` (see the file header). -/
structure LogOk (M : SeqModel σ α) (m : Nat) (hs : List (List (Op α)))
    (Lcs : List (List (α × Int))) (L : List (LinRec α)) : Prop where
  len : Lcs.length = hs.length
  hlen : ∀ h ∈ hs, h.length = m
  lclen : ∀ Lc ∈ Lcs, Lc.length = m
  recs : ∀ (c : Nat) (h : List (Op α)) (Lc : List (α × Int)), hs[c]? = some h →
    Lcs[c]? = some Lc → ∀ (j : Nat) (o : Op α) (p : α × Int), h[j]? = some o →
      Lc[j]? = some p → RecOk o p
  filt : ∀ c, L.filter (fun e => e.c == c) = clientRecs c (Lcs.getD c [])
  sorted : L.Pairwise fun a b => a.τ ≤ b.τ
  runs : (run M M.init (L.map LinRec.io)).isSome

theorem clientRecs_getElem? (c : Nat) (Lc : List (α × Int)) (j : Nat) :
    (clientRecs c Lc)[j]? = Lc[j]?.map fun p => ⟨c, j, p.1, p.2⟩ := by
  simp [clientRecs, List.getElem?_mapIdx]

theorem mem_clientRecs {c : Nat} {Lc : List (α × Int)} {e : LinRec α}
    (he : e ∈ clientRecs c Lc) : ∃ p, Lc[e.j]? = some p ∧ e = ⟨c, e.j, p.1, p.2⟩ := by
  obtain ⟨j, hj⟩ := List.getElem?_of_mem he
  rw [clientRecs_getElem?] at hj
  cases hp : Lc[j]? with
  | none => rw [hp] at hj; cases hj
  | some p =>
    rw [hp] at hj
    simp only [Option.map_some, Option.some.injEq] at hj
    subst hj
    exact ⟨p, hp, rfl⟩

theorem clientRecs_pairwise (c : Nat) (Lc : List (α × Int)) :
    (clientRecs c Lc).Pairwise (fun a b => a.j < b.j) := by
  rw [List.pairwise_iff_getElem]
  intro i k hi hk hik
  simp only [clientRecs, List.getElem_mapIdx]
  exact hik

theorem flatten_length {β : Type} (hs : List (List β)) (m : Nat)
    (hl : ∀ h ∈ hs, h.length = m) : hs.flatten.length = hs.length * m := by
  induction hs with
  | nil => simp
  | cons h t ih =>
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    rw [hl h (List.mem_cons_self), ih (fun h' hh' => hl h' (List.mem_cons_of_mem _ hh'))]
    rw [Nat.succ_mul, Nat.add_comm]

theorem flatten_getElem? {β : Type} (hs : List (List β)) (m : Nat)
    (hl : ∀ h ∈ hs, h.length = m) (c j : Nat) (hj : j < m) :
    hs.flatten[c * m + j]? = hs[c]?.bind (·[j]?) := by
  induction hs generalizing c with
  | nil => simp
  | cons h t ih =>
    have hh : h.length = m := hl h (List.mem_cons_self)
    have ht : ∀ h' ∈ t, h'.length = m := fun h' hh' => hl h' (List.mem_cons_of_mem _ hh')
    simp only [List.flatten_cons]
    cases c with
    | zero =>
      rw [Nat.zero_mul, Nat.zero_add, List.getElem?_append_left (by omega)]
      simp
    | succ c =>
      rw [List.getElem?_append_right (by rw [hh, Nat.succ_mul]; omega)]
      rw [show (c + 1) * m + j - h.length = c * m + j by rw [hh, Nat.succ_mul]; omega]
      rw [ih ht c]
      simp

/-- The history index of a log entry. -/
def gidx (m : Nat) (e : LinRec α) : Nat := e.c * m + e.j

section
variable {M : SeqModel σ α} {m : Nat} {hs : List (List (Op α))}
  {Lcs : List (List (α × Int))} {L : List (LinRec α)}

/-- Every log entry is one of the history's operations, described by the entry. -/
theorem LogOk.entry (H : LogOk M m hs Lcs L) {e : LinRec α} (he : e ∈ L) :
    e.c < hs.length ∧ e.j < m ∧ ∃ o, hs.flatten[gidx m e]? = some o ∧ RecOk o (e.io, e.τ) := by
  have hf : e ∈ L.filter (fun x => x.c == e.c) := by
    simp only [List.mem_filter, beq_self_eq_true, and_true]; exact he
  rw [H.filt e.c] at hf
  obtain ⟨p, hp, hep⟩ := mem_clientRecs hf
  have hc : e.c < Lcs.length := by
    rcases Nat.lt_or_ge e.c Lcs.length with hc | hc
    · exact hc
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hc] at hp
      simp at hp
  obtain ⟨Lc, hLc⟩ : ∃ Lc, Lcs[e.c]? = some Lc := ⟨_, List.getElem?_eq_getElem hc⟩
  rw [List.getD_eq_getElem?_getD, hLc, Option.getD_some] at hp
  have hcl : e.c < hs.length := by rw [← H.len]; exact hc
  obtain ⟨h, hh⟩ : ∃ h, hs[e.c]? = some h := ⟨_, List.getElem?_eq_getElem hcl⟩
  have hjm : e.j < m := by
    rw [← H.lclen Lc (List.mem_of_getElem? hLc)]
    exact (List.getElem?_eq_some_iff.1 hp).1
  have hjh : e.j < h.length := by rw [H.hlen h (List.mem_of_getElem? hh)]; exact hjm
  obtain ⟨o, ho⟩ : ∃ o, h[e.j]? = some o := ⟨_, List.getElem?_eq_getElem hjh⟩
  refine ⟨hcl, hjm, o, ?_, ?_⟩
  · unfold gidx
    rw [flatten_getElem? hs m H.hlen e.c e.j hjm, hh]
    simpa using ho
  · have hr := H.recs e.c h Lc hh hLc e.j o p ho hp
    have hio : e.io = p.1 := by rw [hep]
    have hτ : e.τ = p.2 := by rw [hep]
    rw [hio, hτ]
    exact hr

theorem LogOk.gidx_inj (H : LogOk M m hs Lcs L) {x y : LinRec α} (hx : x ∈ L) (hy : y ∈ L)
    (hxy : gidx m x = gidx m y) : x = y := by
  obtain ⟨-, hxj, -⟩ := H.entry hx
  obtain ⟨-, hyj, -⟩ := H.entry hy
  unfold gidx at hxy
  have hc : x.c = y.c := by
    have h1 : (x.c * m + x.j) / m = x.c := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hxj, Nat.zero_add]
    have h2 : (y.c * m + y.j) / m = y.c := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hyj, Nat.zero_add]
    rw [← h1, ← h2, hxy]
  have hj : x.j = y.j := by rw [hc] at hxy; omega
  have hfx : x ∈ L.filter (fun e => e.c == x.c) := by
    simp only [List.mem_filter, beq_self_eq_true, and_true]; exact hx
  have hfy : y ∈ L.filter (fun e => e.c == x.c) := by
    simp only [List.mem_filter, hc, beq_self_eq_true, and_true]; exact hy
  rw [H.filt] at hfx hfy
  obtain ⟨px, hpx, hex⟩ := mem_clientRecs hfx
  obtain ⟨py, hpy, hey⟩ := mem_clientRecs hfy
  rw [hj] at hpx
  rw [hpx] at hpy
  cases hpy
  rw [hex, hey, hj]

/-- A client's operations appear in the log in order. -/
theorem LogOk.pairwise_j (H : LogOk M m hs Lcs L) :
    L.Pairwise (fun a b => a.c = b.c → a.j < b.j) := by
  rw [List.pairwise_iff_getElem]
  intro i k hi hk hik hc
  have hf := clientRecs_pairwise L[i].c (Lcs.getD L[i].c [])
  rw [← H.filt, List.pairwise_filter, List.pairwise_iff_getElem] at hf
  exact hf i k hi hk hik (by simp) (by simp [hc])

theorem LogOk.nodup_map (H : LogOk M m hs Lcs L) : (L.map (gidx m)).Nodup := by
  unfold List.Nodup
  rw [List.pairwise_map]
  refine H.pairwise_j.imp_of_mem ?_
  intro a b ha hb hab heq
  have := H.gidx_inj ha hb heq
  subst this
  exact Nat.lt_irrefl _ (hab rfl)

theorem LogOk.mem_iff (H : LogOk M m hs Lcs L) (k : Nat) :
    k ∈ L.map (gidx m) ↔ k < hs.length * m := by
  constructor
  · intro hk
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hk
    obtain ⟨hc, hj, -⟩ := H.entry he
    unfold gidx
    have : (e.c + 1) * m ≤ hs.length * m := Nat.mul_le_mul_right _ hc
    rw [Nat.succ_mul] at this
    omega
  · intro hk
    have hm : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · rw [h0, Nat.mul_zero] at hk; omega
      · exact h0
    have hc : k / m < hs.length := (Nat.div_lt_iff_lt_mul hm).2 hk
    have hc' : k / m < Lcs.length := by rw [H.len]; exact hc
    obtain ⟨Lc, hLc⟩ : ∃ Lc, Lcs[k / m]? = some Lc := ⟨_, List.getElem?_eq_getElem hc'⟩
    have hj : k % m < Lc.length := by
      rw [H.lclen Lc (List.mem_of_getElem? hLc)]; exact Nat.mod_lt _ hm
    obtain ⟨p, hp⟩ : ∃ p, Lc[k % m]? = some p := ⟨_, List.getElem?_eq_getElem hj⟩
    have hmem : (⟨k / m, k % m, p.1, p.2⟩ : LinRec α) ∈ clientRecs (k / m) Lc := by
      apply List.mem_of_getElem? (i := k % m)
      rw [clientRecs_getElem?, hp]; rfl
    have hfL : (⟨k / m, k % m, p.1, p.2⟩ : LinRec α) ∈ L.filter (fun e => e.c == k / m) := by
      rw [H.filt, List.getD_eq_getElem?_getD, hLc, Option.getD_some]; exact hmem
    refine List.mem_map.2 ⟨_, (List.mem_filter.1 hfL).1, ?_⟩
    simp only [gidx]
    rw [Nat.mul_comm, Nat.div_add_mod]

theorem LogOk.vals (H : LogOk M m hs Lcs L) :
    vals hs.flatten (L.map (gidx m)) = L.map LinRec.io := by
  unfold github_com.anishathalye.porcupine.Theory.vals
  rw [List.filterMap_map]
  have : ∀ L' : List (LinRec α), (∀ e ∈ L', e ∈ L) →
      L'.filterMap (fun e => (hs.flatten[gidx m e]?).map Op.val) = L'.map LinRec.io := by
    intro L' hL'
    induction L' with
    | nil => rfl
    | cons e t ih =>
      obtain ⟨-, -, o, ho, hr⟩ := H.entry (hL' e (List.mem_cons_self))
      rw [List.filterMap_cons, List.map_cons]
      simp only [ho, Option.map_some]
      rw [hr.1]
      rw [ih (fun e' he' => hL' e' (List.mem_cons_of_mem _ he'))]
  exact this L (fun _ h => h)

/-- **The traced history is linearizable** (see the file header). -/
theorem LogOk.linearizable (H : LogOk M m hs Lcs L) : Linearizable M hs.flatten := by
  refine ⟨L.map (gidx m), ?_, ?_, ?_, ?_⟩
  · exact H.nodup_map
  · intro k
    rw [H.mem_iff k, flatten_length hs m H.hlen]
    simp
  · rw [H.vals]; exact H.runs
  · rw [List.pairwise_map]
    refine H.sorted.imp_of_mem ?_
    intro a b ha hb hab hprec
    obtain ⟨-, -, oa, hoa, hra⟩ := H.entry ha
    obtain ⟨-, -, ob, hob, hrb⟩ := H.entry hb
    obtain ⟨ob', oa', hob', hoa', hlt⟩ := hprec
    rw [hob] at hob'; cases hob'
    rw [hoa] at hoa'; cases hoa'
    have := hra.2.1
    have := hrb.2.2
    simp only at *
    omega

end

end lintest
end EtcdGrove
end Perennial
