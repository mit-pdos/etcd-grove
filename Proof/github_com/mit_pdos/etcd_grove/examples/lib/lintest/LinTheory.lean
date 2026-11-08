/-
Lean-first (no Rocq counterpart).

# lintest: a traced history is linearizable (2026-10-14)

The pure argument behind `Run`: `n` clients ran some operations each (as many as `RunLin2`'s
group says); client `c`'s trace is `hs[c]`, and the whole history is their concatenation
`hs.flatten` (what `Run` passes to porcupine), so client `c`'s `j`-th operation is operation
`off hs c + j` of the history, `off hs c` the lengths of the traces before it (2026-11-08, k8s 7f:
until `RunLin2` every client ran `m` operations and the index was `c * m + j`).

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

Then the log, as indices of the history (`off hs c + j`), is a linearization in porcupine's
sense (`Theory.Linearizable`): every operation once, allowed by the model, and an operation
that returned before another was called comes first (if `b` follows `a` in the log, then
`a.call ≤ τa ≤ τb ≤ b.ret`, so `b` did not return before `a` was called).
-/
module

public import Proof.github_com.anishathalye.porcupine.Theory
public import Perennial.Std.List

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
and the log `L` (see the file header). The clients' traces may have different lengths
(`RunLin2`'s two groups); client `c`'s records are as many as its trace's operations. -/
structure LogOk (M : SeqModel σ α) (hs : List (List (Op α)))
    (Lcs : List (List (α × Int))) (L : List (LinRec α)) : Prop where
  len : Lcs.length = hs.length
  lclen : ∀ (c : Nat) (h : List (Op α)) (Lc : List (α × Int)), hs[c]? = some h →
    Lcs[c]? = some Lc → Lc.length = h.length
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

/-! ### Where client `c`'s operations are in the concatenated history -/

section offsets
variable {β : Type}

/-- The index in `hs.flatten` of client `c`'s first operation: the lengths of the traces
before it. -/
def off (hs : List (List β)) (c : Nat) : Nat := ((hs.take c).map List.length).sum

theorem off_zero (hs : List (List β)) : off hs 0 = 0 := by simp [off]

theorem off_cons_succ (h : List β) (t : List (List β)) (c : Nat) :
    off (h :: t) (c + 1) = h.length + off t c := by
  simp [off, List.take_succ_cons]

theorem off_succ (hs : List (List β)) (c : Nat) (h : List β) (hc : hs[c]? = some h) :
    off hs (c + 1) = off hs c + h.length := by
  induction hs generalizing c with
  | nil => simp at hc
  | cons h0 t ih =>
    cases c with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc
      rw [off_cons_succ, off_zero, off_zero]; omega
    | succ c =>
      simp only [List.getElem?_cons_succ] at hc
      rw [off_cons_succ, off_cons_succ, ih c hc]; omega

theorem off_mono (hs : List (List β)) {c d : Nat} (hcd : c ≤ d) : off hs c ≤ off hs d := by
  unfold off
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hcd
  rw [List.take_add, List.map_append, List.sum_append]
  omega

theorem flatten_getElem?_off (hs : List (List β)) (c : Nat) (h : List β) (hc : hs[c]? = some h)
    (j : Nat) (hj : j < h.length) : hs.flatten[off hs c + j]? = h[j]? := by
  induction hs generalizing c with
  | nil => simp at hc
  | cons h0 t ih =>
    simp only [List.flatten_cons]
    cases c with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc
      rw [off_zero, Nat.zero_add, List.getElem?_append_left hj]
    | succ c =>
      simp only [List.getElem?_cons_succ] at hc
      rw [off_cons_succ, List.getElem?_append_right (by omega),
        show h0.length + off t c + j - h0.length = off t c + j by omega]
      exact ih c hc

theorem off_inj (hs : List (List β)) {c1 c2 j1 j2 : Nat} {h1 h2 : List β}
    (hc1 : hs[c1]? = some h1) (hj1 : j1 < h1.length)
    (hc2 : hs[c2]? = some h2) (hj2 : j2 < h2.length)
    (he : off hs c1 + j1 = off hs c2 + j2) : c1 = c2 ∧ j1 = j2 := by
  have key : ∀ {a b ja jb : Nat} {ha hb : List β}, hs[a]? = some ha → ja < ha.length →
      a < b → off hs a + ja < off hs b + jb := by
    intro a b ja jb ha hb hha hja hab
    have h1 := off_succ hs a ha hha
    have h2 := off_mono hs (show a + 1 ≤ b by omega)
    omega
  rcases Nat.lt_trichotomy c1 c2 with hlt | heq | hgt
  · exact absurd he (Nat.ne_of_lt (key (hb := h2) hc1 hj1 hlt))
  · subst heq; exact ⟨rfl, by omega⟩
  · exact absurd he.symm (Nat.ne_of_lt (key (hb := h1) hc2 hj2 hgt))

theorem lt_flatten_length (hs : List (List β)) (k : Nat) (hk : k < hs.flatten.length) :
    ∃ c h j, hs[c]? = some h ∧ j < h.length ∧ k = off hs c + j := by
  induction hs generalizing k with
  | nil => simp at hk
  | cons h0 t ih =>
    simp only [List.flatten_cons, List.length_append] at hk
    rcases Nat.lt_or_ge k h0.length with hlt | hge
    · exact ⟨0, h0, k, rfl, hlt, by rw [off_zero]; omega⟩
    · obtain ⟨c, h, j, hc, hj, hk'⟩ := ih (k - h0.length) (by omega)
      exact ⟨c + 1, h, j, by simpa using hc, hj, by rw [off_cons_succ]; omega⟩

theorem off_lt_flatten_length (hs : List (List β)) (c : Nat) (h : List β) (hc : hs[c]? = some h)
    (j : Nat) (hj : j < h.length) : off hs c + j < hs.flatten.length := by
  have := flatten_getElem?_off hs c h hc j hj
  rw [List.getElem?_eq_getElem hj] at this
  exact (List.getElem?_eq_some_iff.1 this).1

end offsets

/-- The history index of a log entry. -/
def gidx (hs : List (List (Op α))) (e : LinRec α) : Nat := off hs e.c + e.j

section
variable {M : SeqModel σ α} {hs : List (List (Op α))}
  {Lcs : List (List (α × Int))} {L : List (LinRec α)}

/-- Every log entry is one of the history's operations, described by the entry. -/
theorem LogOk.entry (H : LogOk M hs Lcs L) {e : LinRec α} (he : e ∈ L) :
    ∃ h, hs[e.c]? = some h ∧ e.j < h.length ∧
      ∃ o, hs.flatten[gidx hs e]? = some o ∧ RecOk o (e.io, e.τ) := by
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
  have hjh : e.j < h.length := by
    rw [← H.lclen e.c h Lc hh hLc]
    exact (List.getElem?_eq_some_iff.1 hp).1
  obtain ⟨o, ho⟩ : ∃ o, h[e.j]? = some o := ⟨_, List.getElem?_eq_getElem hjh⟩
  refine ⟨h, hh, hjh, o, ?_, ?_⟩
  · unfold gidx
    rw [flatten_getElem?_off hs e.c h hh e.j hjh, ho]
  · have hr := H.recs e.c h Lc hh hLc e.j o p ho hp
    have hio : e.io = p.1 := by rw [hep]
    have hτ : e.τ = p.2 := by rw [hep]
    rw [hio, hτ]
    exact hr

theorem LogOk.gidx_inj (H : LogOk M hs Lcs L) {x y : LinRec α} (hx : x ∈ L) (hy : y ∈ L)
    (hxy : gidx hs x = gidx hs y) : x = y := by
  obtain ⟨hx', hhx, hxj, -⟩ := H.entry hx
  obtain ⟨hy', hhy, hyj, -⟩ := H.entry hy
  obtain ⟨hc, hj⟩ := off_inj hs hhx hxj hhy hyj hxy
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
theorem LogOk.pairwise_j (H : LogOk M hs Lcs L) :
    L.Pairwise (fun a b => a.c = b.c → a.j < b.j) := by
  rw [List.pairwise_iff_getElem]
  intro i k hi hk hik hc
  have hf := clientRecs_pairwise L[i].c (Lcs.getD L[i].c [])
  rw [← H.filt, List.pairwise_filter, List.pairwise_iff_getElem] at hf
  exact hf i k hi hk hik (by simp) (by simp [hc])

theorem LogOk.nodup_map (H : LogOk M hs Lcs L) : (L.map (gidx hs)).Nodup := by
  unfold List.Nodup
  rw [List.pairwise_map]
  refine H.pairwise_j.imp_of_mem ?_
  intro a b ha hb hab heq
  have := H.gidx_inj ha hb heq
  subst this
  exact Nat.lt_irrefl _ (hab rfl)

theorem LogOk.mem_iff (H : LogOk M hs Lcs L) (k : Nat) :
    k ∈ L.map (gidx hs) ↔ k < hs.flatten.length := by
  constructor
  · intro hk
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hk
    obtain ⟨h, hh, hj, -⟩ := H.entry he
    exact off_lt_flatten_length hs e.c h hh e.j hj
  · intro hk
    obtain ⟨c, h, j, hh, hj, rfl⟩ := lt_flatten_length hs k hk
    have hcl : c < hs.length := (List.getElem?_eq_some_iff.1 hh).1
    have hc' : c < Lcs.length := by rw [H.len]; exact hcl
    obtain ⟨Lc, hLc⟩ : ∃ Lc, Lcs[c]? = some Lc := ⟨_, List.getElem?_eq_getElem hc'⟩
    have hjl : j < Lc.length := by rw [H.lclen c h Lc hh hLc]; exact hj
    obtain ⟨p, hp⟩ : ∃ p, Lc[j]? = some p := ⟨_, List.getElem?_eq_getElem hjl⟩
    have hmem : (⟨c, j, p.1, p.2⟩ : LinRec α) ∈ clientRecs c Lc := by
      apply List.mem_of_getElem? (i := j)
      rw [clientRecs_getElem?, hp]; rfl
    have hfL : (⟨c, j, p.1, p.2⟩ : LinRec α) ∈ L.filter (fun e => e.c == c) := by
      rw [H.filt, List.getD_eq_getElem?_getD, hLc, Option.getD_some]; exact hmem
    exact List.mem_map.2 ⟨_, (List.mem_filter.1 hfL).1, rfl⟩

theorem LogOk.vals (H : LogOk M hs Lcs L) :
    vals hs.flatten (L.map (gidx hs)) = L.map LinRec.io := by
  unfold github_com.anishathalye.porcupine.Theory.vals
  rw [List.filterMap_map]
  have : ∀ L' : List (LinRec α), (∀ e ∈ L', e ∈ L) →
      L'.filterMap (fun e => (hs.flatten[gidx hs e]?).map Op.val) = L'.map LinRec.io := by
    intro L' hL'
    induction L' with
    | nil => rfl
    | cons e t ih =>
      obtain ⟨-, -, -, o, ho, hr⟩ := H.entry (hL' e (List.mem_cons_self))
      rw [List.filterMap_cons, List.map_cons]
      simp only [ho, Option.map_some]
      rw [hr.1]
      rw [ih (fun e' he' => hL' e' (List.mem_cons_of_mem _ he'))]
  exact this L (fun _ h => h)

/-- **The traced history is linearizable** (see the file header). -/
theorem LogOk.linearizable (H : LogOk M hs Lcs L) : Linearizable M hs.flatten := by
  refine ⟨L.map (gidx hs), ?_, ?_, ?_, ?_⟩
  · exact H.nodup_map
  · intro k
    rw [H.mem_iff k]
    simp
  · rw [H.vals]; exact H.runs
  · rw [List.pairwise_map]
    refine H.sorted.imp_of_mem ?_
    intro a b ha hb hab hprec
    obtain ⟨-, -, -, oa, hoa, hra⟩ := H.entry ha
    obtain ⟨-, -, -, ob, hob, hrb⟩ := H.entry hb
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
