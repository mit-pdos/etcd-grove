/-
Lean-first (no Rocq counterpart).

# Laws for the checker's states and slices (#33 S3b-2, 2026-11-23)

What the proofs of `state.go`, `binding.go` and `check.go` share (`notes/antithesis-check-design.md`
§10, "How to prove an action"):
- **slices**: a read-only slice of persistent elements with one element replaced (the `set*`
  helpers), and the empty slice;
- **reading a state**: `stateRO`/`stateOwn` opened (`iNamed`: the struct `Hp`, each field
  `H<Field>`, the shape `HWf`), a server's position within every per-server list, an element of
  a per-server list read through its slice;
- **building a successor**: `stateFields` with one field replaced (`stateFields_with_<field>`, one
  law per field: the Lean's `{ s with f := x }`), and `stateOwn_persist` (a built successor frozen).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Rep

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-! ## A state's shape -/

theorem State.Wf.len_currentTerm {s : State} (h : s.Wf) : s.currentTerm.length = s.cfg.server.length := h.1
theorem State.Wf.len_voteTerm {s : State} (h : s.Wf) : s.voteTerm.length = s.cfg.server.length := h.2.1
theorem State.Wf.len_voteFor {s : State} (h : s.Wf) : s.voteFor.length = s.cfg.server.length := h.2.2.1
theorem State.Wf.len_log {s : State} (h : s.Wf) : s.log.length = s.cfg.server.length := h.2.2.2.1
theorem State.Wf.len_commitIndex {s : State} (h : s.Wf) : s.commitIndex.length = s.cfg.server.length := h.2.2.2.2.1
theorem State.Wf.len_role {s : State} (h : s.Wf) : s.role.length = s.cfg.server.length := h.2.2.2.2.2.1
theorem State.Wf.len_lastApplied {s : State} (h : s.Wf) : s.lastApplied.length = s.cfg.server.length := h.2.2.2.2.2.2.1
theorem State.Wf.len_config {s : State} (h : s.Wf) : s.config.length = s.cfg.server.length := h.2.2.2.2.2.2.2.1
theorem State.Wf.len_confAt {s : State} (h : s.Wf) : s.confAt.length = s.cfg.server.length := h.2.2.2.2.2.2.2.2.1
theorem State.Wf.len_confirmed {s : State} (h : s.Wf) : s.confirmed.length = s.cfg.server.length := h.2.2.2.2.2.2.2.2.2.1
theorem State.Wf.len_undo {s : State} (h : s.Wf) : s.undo.length = s.cfg.server.length := h.2.2.2.2.2.2.2.2.2.2.1
theorem State.Wf.len_pending {s : State} (h : s.Wf) : s.pending.length = s.cfg.server.length := h.2.2.2.2.2.2.2.2.2.2.2.1
theorem State.Wf.len_queue {s : State} (h : s.Wf) : s.queue.length = s.cfg.server.length := h.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem State.Wf.len_reads {s : State} (h : s.Wf) : s.reads.length = s.cfg.server.length := h.2.2.2.2.2.2.2.2.2.2.2.2.2

/-! ## The budget (`State.Within`) is monotone -/

theorem logWithin.mono {b b' E E' : Nat} (hb : b ≤ b') (hE : E ≤ E') {l : List Entry}
    (h : logWithin b E l) : logWithin b' E' l :=
  ⟨Nat.le_trans h.1 hb, fun e he => ⟨(h.2 e he).1, Nat.le_trans (h.2 e he).2 hE⟩⟩

theorem confWithin.mono {V b b' E E' : Nat} (hb : b ≤ b') (hE : E ≤ E') {c : Conf}
    (h : confWithin V b E c) : confWithin V b' E' c := by
  have hm : b * E ≤ b' * E' := Nat.mul_le_mul hb hE
  exact ⟨by have := h.1; omega, by have := h.2; omega⟩

theorem termIntsWithin.mono {b b' : Nat} (hb : b ≤ b') {f : TermFn Int}
    (h : termIntsWithin b f) : termIntsWithin b' f :=
  ⟨Nat.le_trans h.1 hb, h.2⟩

theorem Msg.Within.mono {b b' E E' : Nat} (hb : b ≤ b') (hE : E ≤ E') {m : Msg}
    (h : m.Within b E) : m.Within b' E' :=
  ⟨h.1, Nat.le_trans h.2.1 hb, fun l hl e he => Nat.le_trans (h.2.2 l hl e he) hE⟩

theorem Event.Within.mono {b b' E E' : Nat} (hb : b ≤ b') (hE : E ≤ E') {ev : Event}
    (h : ev.Within b E) : ev.Within b' E' :=
  ⟨h.1, Nat.le_trans h.2.1 hb, fun l hl e he => Nat.le_trans (h.2.2 l hl e he) hE⟩

theorem Pre.Within.mono {b b' E E' : Nat} (hb : b ≤ b') (hE : E ≤ E') {u : Pre}
    (h : u.Within b E) : u.Within b' E' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8.mono hb hE, by omega, by omega, h11, by omega, h13,
    by omega, h15⟩

/-- A state within a budget is within any larger one (`Ready` passes `OnDisk` the budget after the
report, `b + ev.weight`). -/
theorem State.Within.mono {b b' E E' : Nat} (hb : b ≤ b') (hE : E ≤ E') {s : State}
    (h : s.Within b E) : s.Within b' E' := by
  obtain ⟨hc, hi1, hi2, h1, h2, h3, h4, h5, h6, hlog, hch, hll1, hll2, hcf, hlc1, hlc2, hla, hel,
    htl, hm1, hm2, hv1, hv2, hl1, hl2, hu, hp, hq, hr, hvi⟩ := h
  refine ⟨hc, hi1, by omega, h1, h2, h3, h4, h5, h6, fun l hl => (hlog l hl).mono hb hE,
    hch.mono hb hE, by omega, fun p hp => ⟨(hll2 p hp).1, (hll2 p hp).2.mono hb hE⟩,
    fun c hc => (hcf c hc).mono hb hE, by omega,
    fun p hp => ⟨(hlc2 p hp).1, (hlc2 p hp).2.mono hb hE⟩, hla.mono hb, hel.mono hb, htl.mono hb,
    by omega, hm2, by omega, hv2, by omega, hl2, fun o ho u hou => (hu o ho u hou).mono hb hE,
    fun ms hms => ⟨by have := (hp ms hms).1; omega, fun m hm => ((hp ms hms).2 m hm).mono hb hE⟩,
    fun q hq' => ⟨by have := (hq q hq').1; omega, fun it hit =>
      ⟨((hq q hq').2 it hit).1.mono hb hE, by have := ((hq q hq').2 it hit).2.1; omega,
        fun m hm => (((hq q hq').2 it hit).2.2 m hm).mono hb hE⟩⟩,
    fun r hr' => ⟨by have := (hr r hr').1; omega, (hr r hr').2⟩, by omega⟩

/-- A state and a report within budget: the state is (`GCDue`'s, `End`'s premise). -/
theorem State.BoundedFor.bounded {s : State} {ev : Event} (h : s.BoundedFor ev) : s.Bounded := by
  obtain ⟨b, E, hs, -, -, hb, -⟩ := h
  refine ⟨b, E, ?_, hs⟩
  unfold Event.weight at hb
  push_cast at hb
  omega

/-! ## Lists of persistent elements -/

/-- A big separating conjunction of persistent elements with one pair replaced. -/
theorem bigSepL2_set {A B : Type} (Φ : A → B → IProp GF) [∀ a b, Persistent (Φ a b)]
    (l1 : List A) (l2 : List B) (i : Nat) (y1 : A) (y2 : B) (hi : i < l2.length) :
    ([∗list] x;y ∈ l1;l2, Φ x y) ∗ Φ y1 y2 ⊢ [∗list] x;y ∈ l1.set i y1;l2.set i y2, Φ x y := by
  iintro ⟨H, Hy⟩
  ihave %Hl := BigSepL2.bigSepL2_length $$ H
  obtain ⟨x1, hx1⟩ : ∃ x1, l1[i]? = some x1 := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨x2, hx2⟩ : ∃ x2, l2[i]? = some x2 := ⟨_, List.getElem?_eq_getElem hi⟩
  icases (BigSepL2.bigSepL2_insert_acc (Φ := fun _ x y => Φ x y) hx1 hx2) $$ H with ⟨-, Hset⟩
  iapply Hset
  iexact Hy

/-- `make` then `copy` from a slice of the same length: the copy holds the source's elements. -/
theorem copy_full {V : Type} (ps : List V) (n : Nat) (z : V) (h : ps.length = n) :
    (ps.take (List.replicate n z).length ++ (List.replicate n z).drop ps.length) = ps := by
  subst h; simp

/-- Element `k` of a big separating conjunction of persistent elements. -/
theorem bigSepL2_at {A B : Type} [Inhabited B] (Φ : A → B → IProp GF) [∀ a b, Persistent (Φ a b)]
    (l1 : List A) (l2 : List B) (k : Nat) (hk : k < l2.length) :
    ([∗list] x;y ∈ l1;l2, Φ x y) ⊢ ∃ x, ⌜l1[k]? = some x⌝ ∗ Φ x l2[k]! := by
  iintro #H
  ihave %Hl := BigSepL2.bigSepL2_length $$ H
  have h1 : l1[k]? = some l1[k] := List.getElem?_eq_getElem (by omega)
  have h2 : l2[k]? = some l2[k]! := by rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hk]; rfl
  iexists l1[k]
  isplitr
  · ipureintro; exact h1
  iapply BigSepL2.bigSepL2_lookup (Φ := fun _ x y => Φ x y) h1 h2
  iexact H

/-! ## Reading an element of a slice -/

/-- `sl[k]` (a load through `IndexRef`), in bounds: element `k` of what `sl` holds. -/
theorem wp_load_index {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.GoType}
    [IntoValTyped (GF := GF) V t] (sl : GoSlice) (k : w64) (gs : List V) (x : V) (hk : 0 ≤ sint.Z k)
    (hx : gs[sint.nat k]? = some x) :
    {{ (sl ↦*□ gs : IProp GF) }}
      (App (Val (GoInstruction (GoLoad t)))
        (if 0 ≤ sint.Z k ∧ sint.Z k < sint.Z sl.len then Val #(sliceIndexRef V (sint.Z k) sl)
         else Panic "slice index out of bounds"))
    {{ RET #x; True }} := by
  iintro %Φ #Hs HΦ
  ihave %Hl := ownSlice_len $$ Hs
  have hlt : sint.Z k < sint.Z sl.len := by
    have := (List.getElem?_eq_some_iff.1 hx).1
    rw [Hl.1] at this; word
  rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z sl.len from ⟨hk, hlt⟩))]
  wp_apply wp_load_slice_index sl (sint.Z k) gs DFrac.discard x hk $$ [Hs] as -
  · isplitr
    · iexact Hs
    ipureintro; exact hx
  iapply HΦ
  iempintro

/-- Element `k` of slice `sl` is `x` (read-only): what `sl[k]` loads (`wp_load_at`), opened once
from the slice's representation (`undoRO_at`, ...) and read as often as the Go reads it. -/
def sliceAt {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (sl : GoSlice) (k : w64) (x : V) : IProp GF :=
  iprop(∃ xs : List V, sl ↦*□ xs ∗ ⌜xs[sint.nat k]? = some x⌝)

instance sliceAt_persistent {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (sl : GoSlice) (k : w64)
    (x : V) : Persistent (sliceAt (GF := GF) sl k x) := by
  unfold sliceAt; infer_instance

/-- `sl[k]`: `x`. -/
theorem wp_load_at {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.GoType}
    [IntoValTyped (GF := GF) V t] (sl : GoSlice) (k : w64) (x : V) (hk : 0 ≤ sint.Z k) :
    {{ sliceAt (GF := GF) sl k x }}
      (App (Val (GoInstruction (GoLoad t)))
        (if 0 ≤ sint.Z k ∧ sint.Z k < sint.Z sl.len then Val #(sliceIndexRef V (sint.Z k) sl)
         else Panic "slice index out of bounds"))
    {{ RET #x; True }} := by
  iintro %Φ #H HΦ
  iunfold sliceAt at H
  icases H with ⟨%xs, #Hs, %Hx⟩
  wp_apply wp_load_index sl k xs x hk Hx $$ [Hs]
  · iexact Hs
  iapply HΦ
  iempintro

/-- A slice of persistent elements, element `k`. -/
theorem sliceRO_at {V A : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] [Inhabited A]
    (Φ : V → A → IProp GF) [∀ a b, Persistent (Φ a b)] (sl : GoSlice) (gs : List V) (xs : List A)
    (k : w64) (hk : 0 ≤ sint.Z k ∧ sint.Z k < xs.length) :
    sl ↦*□ gs ∗ ([∗list] g;x ∈ gs;xs, Φ g x) ⊢ ∃ g, sliceAt sl k g ∗ Φ g xs[sint.nat k]! := by
  iintro ⟨#Hs, #Hb⟩
  icases bigSepL2_at Φ gs xs (sint.nat k) (by word) $$ Hb with ⟨%g, %Hg, #Hx⟩
  iexists g
  iframe Hx
  iunfold sliceAt
  iexists gs
  iframe Hs
  ipureintro; exact Hg

/-- `Forall₂` at an index. -/
theorem forall₂_getElem {A B : Type} {R : A → B → Prop} :
    ∀ {l1 : List A} {l2 : List B}, List.Forall₂ R l1 l2 → ∀ (i : Nat) (h1 : i < l1.length)
      (h2 : i < l2.length), R l1[i] l2[i]
  | _, _, .nil, _, h1, _ => absurd h1 (Nat.not_lt_zero _)
  | _, _, .cons hab _, 0, _, _ => hab
  | _, _, .cons _ hr, i + 1, h1, h2 =>
    forall₂_getElem hr i (Nat.lt_of_succ_lt_succ h1) (Nat.lt_of_succ_lt_succ h2)

/-- A slice of values related by `R`, element `k`. -/
theorem sliceRel_at {V A : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] [Inhabited A]
    (R : V → A → Prop) (sl : GoSlice) (gs : List V) (xs : List A)
    (k : w64) (hk : 0 ≤ sint.Z k ∧ sint.Z k < xs.length) (hR : List.Forall₂ R gs xs) :
    sl ↦*□ gs ⊢ ∃ g, sliceAt (GF := GF) sl k g ∗ ⌜R g xs[sint.nat k]!⌝ := by
  iintro #Hs
  have hl := hR.length_eq
  have hk' : sint.nat k < gs.length := by rw [hl]; word
  iexists gs[sint.nat k]
  isplitl
  · iunfold sliceAt
    iexists gs
    iframe Hs
    ipureintro; exact List.getElem?_eq_getElem hk'
  ipureintro
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [← hl]; exact hk')]
  exact forall₂_getElem hR _ hk' (by rw [← hl]; exact hk')

/-! ## Reading a per-server variable: `s.F[n]`, the Lean's `s.f[n]!` -/

/-- `s.Undo[k]`. -/
theorem undoRO_at (sl : GoSlice) (us : List (Option Pre)) (k : w64) (hk : 0 ≤ sint.Z k ∧ sint.Z k < us.length) :
    undoRO (GF := GF) sl us ⊢ ∃ v : Loc, sliceAt sl k v ∗ preRO v us[sint.nat k]! := by
  iintro #H
  iunfold undoRO at H
  icases H with ⟨%ps, #Hps, #Hb⟩
  iapply sliceRO_at (fun p u => preRO (GF := GF) p u) sl ps us k hk
  iframe Hps Hb

/-- A log's length is its slice's. -/
theorem logRO_len (sl : GoSlice) (l : List Entry) : logRO (GF := GF) sl l ⊢ ⌜sint.Z sl.len = l.length⌝ := by
  iintro #H
  iunfold logRO at H
  icases H with ⟨%es, #Hes, #Hb⟩
  ihave %Hel := ownSlice_len $$ Hes
  ihave %Hl := BigSepL2.bigSepL2_length $$ Hb
  ipureintro; rw [← Hl, Hel.1]; word

/-- A slice of persistent elements: its length is the list's. -/
theorem sliceRO_len {V A : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (Φ : V → A → IProp GF) (sl : GoSlice) (gs : List V) (xs : List A) :
    sl ↦*□ gs ∗ ([∗list] g;x ∈ gs;xs, Φ g x) ⊢ ⌜sint.Z sl.len = xs.length⌝ := by
  iintro ⟨#Hs, Hb⟩
  ihave %Hel := ownSlice_len $$ Hs
  ihave %Hl := BigSepL2.bigSepL2_length $$ Hb
  ipureintro; rw [← Hl, Hel.1]; word

/-- A slice of values related by `R`: its length is the list's. -/
theorem sliceRel_len {V A : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (R : V → A → Prop) (sl : GoSlice) (gs : List V) (xs : List A) (hR : List.Forall₂ R gs xs) :
    (sl ↦*□ gs : IProp GF) ⊢ ⌜sint.Z sl.len = xs.length⌝ := by
  iintro #Hs
  ihave %Hel := ownSlice_len $$ Hs
  ipureintro; rw [← hR.length_eq, Hel.1]; word

theorem strsRO_len (sl : GoSlice) (xs : List Str) : strsRO (GF := GF) sl xs ⊢ ⌜sint.Z sl.len = xs.length⌝ := by
  iintro #H
  iunfold strsRO at H
  ihave %Hel := ownSlice_len $$ H
  ipureintro; rw [Hel.1]; word

theorem intsRO_len (sl : GoSlice) (xs : List Int) : intsRO (GF := GF) sl xs ⊢ ⌜sint.Z sl.len = xs.length⌝ := by
  iintro #H
  iunfold intsRO at H
  icases H with ⟨%ws, #Hws, %Hm⟩
  ihave %Hel := ownSlice_len $$ Hws
  ipureintro; rw [← Hm, List.length_map, Hel.1]; word

theorem msgsRO_len (sl : GoSlice) (ms : List Msg) : msgsRO (GF := GF) sl ms ⊢ ⌜sint.Z sl.len = ms.length⌝ := by
  iintro #H
  iunfold msgsRO at H
  icases H with ⟨%gs, #Hgs, #Hb⟩
  iapply sliceRO_len (fun g m => msgRO (GF := GF) g m) sl gs ms
  iframe Hgs Hb

theorem qitemsRO_len (sl : GoSlice) (q : List QItem) : qitemsRO (GF := GF) sl q ⊢ ⌜sint.Z sl.len = q.length⌝ := by
  iintro #H
  iunfold qitemsRO at H
  icases H with ⟨%gs, #Hgs, #Hb⟩
  iapply sliceRO_len (fun g x => qitemRO (GF := GF) g x) sl gs q
  iframe Hgs Hb

theorem factsRO_len (sl : GoSlice) (fs : List Fact) : factsRO (GF := GF) sl fs ⊢ ⌜sint.Z sl.len = fs.length⌝ := by
  iintro #H
  iunfold factsRO at H
  icases H with ⟨%gs, #Hgs, %HR⟩
  iapply sliceRel_len factRel sl gs fs HR
  iexact Hgs

theorem votesRO_len (sl : GoSlice) (vs : List VoteRec) : votesRO (GF := GF) sl vs ⊢ ⌜sint.Z sl.len = vs.length⌝ := by
  iintro #H
  iunfold votesRO at H
  icases H with ⟨%gs, #Hgs, %HR⟩
  iapply sliceRel_len voteRel sl gs vs HR
  iexact Hgs

theorem readRecsRO_len (sl : GoSlice) (r : List ReadRec) : readRecsRO (GF := GF) sl r ⊢ ⌜sint.Z sl.len = r.length⌝ := by
  iintro #H
  iunfold readRecsRO at H
  icases H with ⟨%gs, #Hgs, %HR⟩
  iapply sliceRel_len readRel sl gs r HR
  iexact Hgs

/-- A queue's sub-slice `sl[lo:hi]` holds the queue's items `[lo, hi)` (`Write`'s, `Flush`'s
`s.Queue[n][1:]`). -/
theorem qitemsRO_subslice (sl : GoSlice) (q : List QItem) (lo hi : w64)
    (hb : 0 ≤ sint.Z lo ∧ sint.Z lo ≤ sint.Z hi ∧ sint.Z hi ≤ sint.Z sl.len) :
    qitemsRO (GF := GF) sl q ⊢
      qitemsRO (slice.slice sl G.QItem lo hi) (subslice (sint.nat lo) (sint.nat hi) q) := by
  unfold qitemsRO
  iintro ⟨%gs, #Hgs, #Hb⟩
  ihave %Hl := BigSepL2.bigSepL2_length $$ Hb
  icases (ownSlice_slice lo hi sl _ gs hb).1 $$ Hgs with ⟨-, #H2, -⟩
  iexists (subslice (sint.nat lo) (sint.nat hi) gs)
  isplitr
  · iexact H2
  iapply bigSepL2_subslice (fun g x => qitemRO (GF := GF) g x) gs q _ _ Hl
  iexact Hb

/-- A node's reads' sub-slice `sl[lo:hi]` (`ReadAsked`'s `q[1:]`). -/
theorem readRecsRO_subslice (sl : GoSlice) (r : List ReadRec) (lo hi : w64)
    (hb : 0 ≤ sint.Z lo ∧ sint.Z lo ≤ sint.Z hi ∧ sint.Z hi ≤ sint.Z sl.len) :
    readRecsRO (GF := GF) sl r ⊢
      readRecsRO (slice.slice sl G.ReadRec lo hi) (subslice (sint.nat lo) (sint.nat hi) r) := by
  unfold readRecsRO
  iintro ⟨%gs, #Hgs, %HR⟩
  icases (ownSlice_slice lo hi sl _ gs hb).1 $$ Hgs with ⟨-, #H2, -⟩
  iexists (subslice (sint.nat lo) (sint.nat hi) gs)
  isplitl
  · iexact H2
  ipureintro
  unfold subslice
  exact (HR.take _).drop _

/-- `s.F[k]` for an `[]int` field. -/
theorem intsRO_at (sl : GoSlice) (xs : List Int) (k : w64) (hk : 0 ≤ sint.Z k ∧ sint.Z k < xs.length) :
    intsRO (GF := GF) sl xs ⊢ ∃ w : w64, sliceAt sl k w ∗ ⌜sint.Z w = xs[sint.nat k]!⌝ := by
  iintro #H
  iunfold intsRO at H
  icases H with ⟨%ws, #Hws, %Hx⟩
  have hR : List.Forall₂ (fun (w : w64) (x : Int) => sint.Z w = x) ws xs := by
    subst Hx; clear hk; induction ws with
    | nil => exact .nil
    | cons _ _ ih => exact .cons rfl ih
  iapply sliceRel_at (fun (w : w64) (x : Int) => sint.Z w = x) sl ws xs k hk hR
  iexact Hws

/-- `s.F[k]` for a `[]string` field. -/
theorem strsRO_at (sl : GoSlice) (xs : List Str) (k : w64) (hk : 0 ≤ sint.Z k ∧ sint.Z k < xs.length) :
    strsRO (GF := GF) sl xs ⊢ sliceAt sl k xs[sint.nat k]! := by
  iintro #H
  iunfold strsRO at H
  iunfold sliceAt
  iexists xs
  iframe H
  ipureintro
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by word)]; rfl

/-- `s.Log[k]`. -/
theorem logsRO_at (sl : GoSlice) (ls : List (List Entry)) (k : w64) (hk : 0 ≤ sint.Z k ∧ sint.Z k < ls.length) :
    logsRO (GF := GF) sl ls ⊢ ∃ v : GoSlice, sliceAt sl k v ∗ logRO v ls[sint.nat k]! := by
  iintro #H
  iunfold logsRO at H
  icases H with ⟨%gs, #Hgs, #Hb⟩
  iapply sliceRO_at (fun g l => logRO (GF := GF) g l) sl gs ls k hk
  iframe Hgs Hb

/-- `s.Config[k]`. -/
theorem confsRO_at (sl : GoSlice) (cs : List Conf) (k : w64) (hk : 0 ≤ sint.Z k ∧ sint.Z k < cs.length) :
    confsRO (GF := GF) sl cs ⊢ ∃ v : G.Conf, sliceAt sl k v ∗ confRO v cs[sint.nat k]! := by
  iintro #H
  iunfold confsRO at H
  icases H with ⟨%gs, #Hgs, #Hb⟩
  iapply sliceRO_at (fun g c => confRO (GF := GF) g c) sl gs cs k hk
  iframe Hgs Hb

/-- `s.Confirmed[k]`. -/
theorem confirmedsRO_at (sl : GoSlice) (cs : List Confirmed) (k : w64) (hk : 0 ≤ sint.Z k ∧ sint.Z k < cs.length) :
    confirmedsRO (GF := GF) sl cs ⊢ ∃ v : G.Confirmed, sliceAt sl k v ∗ ⌜confirmedRel v cs[sint.nat k]!⌝ := by
  iintro #H
  iunfold confirmedsRO at H
  icases H with ⟨%gs, #Hgs, %Hr⟩
  iapply sliceRel_at confirmedRel sl gs cs k hk Hr
  iexact Hgs

/-- `s.Pending[k]`. -/
theorem pendingRO_at (sl : GoSlice) (ms : List (List Msg)) (k : w64) (hk : 0 ≤ sint.Z k ∧ sint.Z k < ms.length) :
    pendingRO (GF := GF) sl ms ⊢ ∃ v : GoSlice, sliceAt sl k v ∗ msgsRO v ms[sint.nat k]! := by
  iintro #H
  iunfold pendingRO at H
  icases H with ⟨%gs, #Hgs, #Hb⟩
  iapply sliceRO_at (fun g m => msgsRO (GF := GF) g m) sl gs ms k hk
  iframe Hgs Hb

/-- `s.Queue[k]`. -/
theorem queueRO_at (sl : GoSlice) (qs : List (List QItem)) (k : w64) (hk : 0 ≤ sint.Z k ∧ sint.Z k < qs.length) :
    queueRO (GF := GF) sl qs ⊢ ∃ v : GoSlice, sliceAt sl k v ∗ qitemsRO v qs[sint.nat k]! := by
  iintro #H
  iunfold queueRO at H
  icases H with ⟨%gs, #Hgs, #Hb⟩
  iapply sliceRO_at (fun g q => qitemsRO (GF := GF) g q) sl gs qs k hk
  iframe Hgs Hb

/-- `s.Reads[k]`. -/
theorem readsRO_at (sl : GoSlice) (rs : List (List ReadRec)) (k : w64) (hk : 0 ≤ sint.Z k ∧ sint.Z k < rs.length) :
    readsRO (GF := GF) sl rs ⊢ ∃ v : GoSlice, sliceAt sl k v ∗ readRecsRO v rs[sint.nat k]! := by
  iintro #H
  iunfold readsRO at H
  icases H with ⟨%gs, #Hgs, #Hb⟩
  iapply sliceRO_at (fun g r => readRecsRO (GF := GF) g r) sl gs rs k hk
  iframe Hgs Hb

/-! ## Building a successor: `ns.F = x`, the Lean's `{ s with f := x }` -/

/-- `{ s with currentTerm := xs }`. -/
theorem stateFields_with_currentTerm (g : G.State) (s : State) (sl : GoSlice) (xs : List Int)
    (h : xs.length = s.cfg.server.length) :
    stateFields (GF := GF) g s ∗ intsRO sl xs ⊢ stateFields { g with CurrentTerm' := sl } { s with currentTerm := xs } := by
  iintro ⟨Hf, #Hn⟩
  iNamed Hf
  iunfold stateFields
  simp only
  have HWf' : ({ s with currentTerm := xs } : State).Wf := by
    obtain ⟨_, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := HWf
    exact ⟨h, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  iframe
  iframe Hn
  try (ipureintro; exact ⟨HI, HWf'⟩)
  try (ipureintro; exact HWf')

/-- `ns.CurrentTerm = sl` on an owned successor: `{ s with currentTerm := xs }`. -/
theorem wp_set_currentTerm (q : Loc) (s : State) (sl : GoSlice) (xs : List Int)
    (h : xs.length = s.cfg.server.length) :
    {{ stateOwn (GF := GF) q s ∗ intsRO sl xs }}
      (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.int))))
        (Val (PairV #(q.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State, go!"CurrentTerm"]) #sl)))
    {{ RET #(); stateOwn q { s with currentTerm := xs } }} := by
  iintro %Φ ⟨Hq, #Hn⟩ HΦ
  iunfold stateOwn at Hq
  iNamed Hq
  icases (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.State_access_store_CurrentTerm (GF := GF) q g sl).access_strict
    $$ Hp with ⟨Hfld, Hclose⟩
  wp_apply IntoValTyped.wp_store _ _ _ $$ Hfld as Hfld
  ihave Hp := Hclose $$ Hfld
  iapply HΦ
  iunfold stateOwn
  iexists _
  iframe Hp
  iapply stateFields_with_currentTerm g s sl xs h
  iframe Hf
  iexact Hn

/-- `{ s with voteTerm := xs }`. -/
theorem stateFields_with_voteTerm (g : G.State) (s : State) (sl : GoSlice) (xs : List Int)
    (h : xs.length = s.cfg.server.length) :
    stateFields (GF := GF) g s ∗ intsRO sl xs ⊢ stateFields { g with VoteTerm' := sl } { s with voteTerm := xs } := by
  iintro ⟨Hf, #Hn⟩
  iNamed Hf
  iunfold stateFields
  simp only
  have HWf' : ({ s with voteTerm := xs } : State).Wf := by
    obtain ⟨h0, _, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := HWf
    exact ⟨h0, h, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  iframe
  iframe Hn
  try (ipureintro; exact ⟨HI, HWf'⟩)
  try (ipureintro; exact HWf')

/-- `ns.VoteTerm = sl` on an owned successor: `{ s with voteTerm := xs }`. -/
theorem wp_set_voteTerm (q : Loc) (s : State) (sl : GoSlice) (xs : List Int)
    (h : xs.length = s.cfg.server.length) :
    {{ stateOwn (GF := GF) q s ∗ intsRO sl xs }}
      (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.int))))
        (Val (PairV #(q.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State, go!"VoteTerm"]) #sl)))
    {{ RET #(); stateOwn q { s with voteTerm := xs } }} := by
  iintro %Φ ⟨Hq, #Hn⟩ HΦ
  iunfold stateOwn at Hq
  iNamed Hq
  icases (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.State_access_store_VoteTerm (GF := GF) q g sl).access_strict
    $$ Hp with ⟨Hfld, Hclose⟩
  wp_apply IntoValTyped.wp_store _ _ _ $$ Hfld as Hfld
  ihave Hp := Hclose $$ Hfld
  iapply HΦ
  iunfold stateOwn
  iexists _
  iframe Hp
  iapply stateFields_with_voteTerm g s sl xs h
  iframe Hf
  iexact Hn

/-- `{ s with voteFor := xs }`. -/
theorem stateFields_with_voteFor (g : G.State) (s : State) (sl : GoSlice) (xs : List Str)
    (h : xs.length = s.cfg.server.length) :
    stateFields (GF := GF) g s ∗ strsRO sl xs ⊢ stateFields { g with VoteFor' := sl } { s with voteFor := xs } := by
  iintro ⟨Hf, #Hn⟩
  iNamed Hf
  iunfold stateFields
  simp only
  have HWf' : ({ s with voteFor := xs } : State).Wf := by
    obtain ⟨h0, h1, _, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := HWf
    exact ⟨h0, h1, h, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  iframe
  iframe Hn
  try (ipureintro; exact ⟨HI, HWf'⟩)
  try (ipureintro; exact HWf')

/-- `ns.VoteFor = sl` on an owned successor: `{ s with voteFor := xs }`. -/
theorem wp_set_voteFor (q : Loc) (s : State) (sl : GoSlice) (xs : List Str)
    (h : xs.length = s.cfg.server.length) :
    {{ stateOwn (GF := GF) q s ∗ strsRO sl xs }}
      (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.string))))
        (Val (PairV #(q.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State, go!"VoteFor"]) #sl)))
    {{ RET #(); stateOwn q { s with voteFor := xs } }} := by
  iintro %Φ ⟨Hq, #Hn⟩ HΦ
  iunfold stateOwn at Hq
  iNamed Hq
  icases (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.State_access_store_VoteFor (GF := GF) q g sl).access_strict
    $$ Hp with ⟨Hfld, Hclose⟩
  wp_apply IntoValTyped.wp_store _ _ _ $$ Hfld as Hfld
  ihave Hp := Hclose $$ Hfld
  iapply HΦ
  iunfold stateOwn
  iexists _
  iframe Hp
  iapply stateFields_with_voteFor g s sl xs h
  iframe Hf
  iexact Hn

/-- `{ s with log := xs }`. -/
theorem stateFields_with_log (g : G.State) (s : State) (sl : GoSlice) (xs : List (List Entry))
    (h : xs.length = s.cfg.server.length) :
    stateFields (GF := GF) g s ∗ logsRO sl xs ⊢ stateFields { g with Log' := sl } { s with log := xs } := by
  iintro ⟨Hf, #Hn⟩
  iNamed Hf
  iunfold stateFields
  simp only
  have HWf' : ({ s with log := xs } : State).Wf := by
    obtain ⟨h0, h1, h2, _, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := HWf
    exact ⟨h0, h1, h2, h, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  iframe
  iframe Hn
  try (ipureintro; exact ⟨HI, HWf'⟩)
  try (ipureintro; exact HWf')

/-- `ns.Log = sl` on an owned successor: `{ s with log := xs }`. -/
theorem wp_set_log (q : Loc) (s : State) (sl : GoSlice) (xs : List (List Entry))
    (h : xs.length = s.cfg.server.length) :
    {{ stateOwn (GF := GF) q s ∗ logsRO sl xs }}
      (App (Val (GoInstruction (GoStore (go.GoType.SliceType (go.GoType.SliceType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Entry.ty)))))
        (Val (PairV #(q.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State, go!"Log"]) #sl)))
    {{ RET #(); stateOwn q { s with log := xs } }} := by
  iintro %Φ ⟨Hq, #Hn⟩ HΦ
  iunfold stateOwn at Hq
  iNamed Hq
  icases (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.State_access_store_Log (GF := GF) q g sl).access_strict
    $$ Hp with ⟨Hfld, Hclose⟩
  wp_apply IntoValTyped.wp_store _ _ _ $$ Hfld as Hfld
  ihave Hp := Hclose $$ Hfld
  iapply HΦ
  iunfold stateOwn
  iexists _
  iframe Hp
  iapply stateFields_with_log g s sl xs h
  iframe Hf
  iexact Hn

/-- `{ s with commitIndex := xs }`. -/
theorem stateFields_with_commitIndex (g : G.State) (s : State) (sl : GoSlice) (xs : List Int)
    (h : xs.length = s.cfg.server.length) :
    stateFields (GF := GF) g s ∗ intsRO sl xs ⊢ stateFields { g with CommitIndex' := sl } { s with commitIndex := xs } := by
  iintro ⟨Hf, #Hn⟩
  iNamed Hf
  iunfold stateFields
  simp only
  have HWf' : ({ s with commitIndex := xs } : State).Wf := by
    obtain ⟨h0, h1, h2, h3, _, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := HWf
    exact ⟨h0, h1, h2, h3, h, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  iframe
  iframe Hn
  try (ipureintro; exact ⟨HI, HWf'⟩)
  try (ipureintro; exact HWf')

/-- `ns.CommitIndex = sl` on an owned successor: `{ s with commitIndex := xs }`. -/
theorem wp_set_commitIndex (q : Loc) (s : State) (sl : GoSlice) (xs : List Int)
    (h : xs.length = s.cfg.server.length) :
    {{ stateOwn (GF := GF) q s ∗ intsRO sl xs }}
      (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.int))))
        (Val (PairV #(q.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State, go!"CommitIndex"]) #sl)))
    {{ RET #(); stateOwn q { s with commitIndex := xs } }} := by
  iintro %Φ ⟨Hq, #Hn⟩ HΦ
  iunfold stateOwn at Hq
  iNamed Hq
  icases (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.State_access_store_CommitIndex (GF := GF) q g sl).access_strict
    $$ Hp with ⟨Hfld, Hclose⟩
  wp_apply IntoValTyped.wp_store _ _ _ $$ Hfld as Hfld
  ihave Hp := Hclose $$ Hfld
  iapply HΦ
  iunfold stateOwn
  iexists _
  iframe Hp
  iapply stateFields_with_commitIndex g s sl xs h
  iframe Hf
  iexact Hn

/-- `{ s with role := xs }`. -/
theorem stateFields_with_role (g : G.State) (s : State) (sl : GoSlice) (xs : List Str)
    (h : xs.length = s.cfg.server.length) :
    stateFields (GF := GF) g s ∗ strsRO sl xs ⊢ stateFields { g with Role' := sl } { s with role := xs } := by
  iintro ⟨Hf, #Hn⟩
  iNamed Hf
  iunfold stateFields
  simp only
  have HWf' : ({ s with role := xs } : State).Wf := by
    obtain ⟨h0, h1, h2, h3, h4, _, h6, h7, h8, h9, h10, h11, h12, h13⟩ := HWf
    exact ⟨h0, h1, h2, h3, h4, h, h6, h7, h8, h9, h10, h11, h12, h13⟩
  iframe
  iframe Hn
  try (ipureintro; exact ⟨HI, HWf'⟩)
  try (ipureintro; exact HWf')

/-- `ns.Role = sl` on an owned successor: `{ s with role := xs }`. -/
theorem wp_set_role (q : Loc) (s : State) (sl : GoSlice) (xs : List Str)
    (h : xs.length = s.cfg.server.length) :
    {{ stateOwn (GF := GF) q s ∗ strsRO sl xs }}
      (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.string))))
        (Val (PairV #(q.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State, go!"Role"]) #sl)))
    {{ RET #(); stateOwn q { s with role := xs } }} := by
  iintro %Φ ⟨Hq, #Hn⟩ HΦ
  iunfold stateOwn at Hq
  iNamed Hq
  icases (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.State_access_store_Role (GF := GF) q g sl).access_strict
    $$ Hp with ⟨Hfld, Hclose⟩
  wp_apply IntoValTyped.wp_store _ _ _ $$ Hfld as Hfld
  ihave Hp := Hclose $$ Hfld
  iapply HΦ
  iunfold stateOwn
  iexists _
  iframe Hp
  iapply stateFields_with_role g s sl xs h
  iframe Hf
  iexact Hn

/-- `{ s with lastApplied := xs }`. -/
theorem stateFields_with_lastApplied (g : G.State) (s : State) (sl : GoSlice) (xs : List Int)
    (h : xs.length = s.cfg.server.length) :
    stateFields (GF := GF) g s ∗ intsRO sl xs ⊢ stateFields { g with LastApplied' := sl } { s with lastApplied := xs } := by
  iintro ⟨Hf, #Hn⟩
  iNamed Hf
  iunfold stateFields
  simp only
  have HWf' : ({ s with lastApplied := xs } : State).Wf := by
    obtain ⟨h0, h1, h2, h3, h4, h5, _, h7, h8, h9, h10, h11, h12, h13⟩ := HWf
    exact ⟨h0, h1, h2, h3, h4, h5, h, h7, h8, h9, h10, h11, h12, h13⟩
  iframe
  iframe Hn
  try (ipureintro; exact ⟨HI, HWf'⟩)
  try (ipureintro; exact HWf')

/-- `ns.LastApplied = sl` on an owned successor: `{ s with lastApplied := xs }`. -/
theorem wp_set_lastApplied (q : Loc) (s : State) (sl : GoSlice) (xs : List Int)
    (h : xs.length = s.cfg.server.length) :
    {{ stateOwn (GF := GF) q s ∗ intsRO sl xs }}
      (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.int))))
        (Val (PairV #(q.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State, go!"LastApplied"]) #sl)))
    {{ RET #(); stateOwn q { s with lastApplied := xs } }} := by
  iintro %Φ ⟨Hq, #Hn⟩ HΦ
  iunfold stateOwn at Hq
  iNamed Hq
  icases (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.State_access_store_LastApplied (GF := GF) q g sl).access_strict
    $$ Hp with ⟨Hfld, Hclose⟩
  wp_apply IntoValTyped.wp_store _ _ _ $$ Hfld as Hfld
  ihave Hp := Hclose $$ Hfld
  iapply HΦ
  iunfold stateOwn
  iexists _
  iframe Hp
  iapply stateFields_with_lastApplied g s sl xs h
  iframe Hf
  iexact Hn

/-- `{ s with config := xs }`. -/
theorem stateFields_with_config (g : G.State) (s : State) (sl : GoSlice) (xs : List Conf)
    (h : xs.length = s.cfg.server.length) :
    stateFields (GF := GF) g s ∗ confsRO sl xs ⊢ stateFields { g with Config' := sl } { s with config := xs } := by
  iintro ⟨Hf, #Hn⟩
  iNamed Hf
  iunfold stateFields
  simp only
  have HWf' : ({ s with config := xs } : State).Wf := by
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, _, h8, h9, h10, h11, h12, h13⟩ := HWf
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h, h8, h9, h10, h11, h12, h13⟩
  iframe
  iframe Hn
  try (ipureintro; exact ⟨HI, HWf'⟩)
  try (ipureintro; exact HWf')

/-- `ns.Config = sl` on an owned successor: `{ s with config := xs }`. -/
theorem wp_set_config (q : Loc) (s : State) (sl : GoSlice) (xs : List Conf)
    (h : xs.length = s.cfg.server.length) :
    {{ stateOwn (GF := GF) q s ∗ confsRO sl xs }}
      (App (Val (GoInstruction (GoStore (go.GoType.SliceType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Conf.ty))))
        (Val (PairV #(q.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State, go!"Config"]) #sl)))
    {{ RET #(); stateOwn q { s with config := xs } }} := by
  iintro %Φ ⟨Hq, #Hn⟩ HΦ
  iunfold stateOwn at Hq
  iNamed Hq
  icases (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.State_access_store_Config (GF := GF) q g sl).access_strict
    $$ Hp with ⟨Hfld, Hclose⟩
  wp_apply IntoValTyped.wp_store _ _ _ $$ Hfld as Hfld
  ihave Hp := Hclose $$ Hfld
  iapply HΦ
  iunfold stateOwn
  iexists _
  iframe Hp
  iapply stateFields_with_config g s sl xs h
  iframe Hf
  iexact Hn

/-- `{ s with confAt := xs }`. -/
theorem stateFields_with_confAt (g : G.State) (s : State) (sl : GoSlice) (xs : List Int)
    (h : xs.length = s.cfg.server.length) :
    stateFields (GF := GF) g s ∗ intsRO sl xs ⊢ stateFields { g with ConfAt' := sl } { s with confAt := xs } := by
  iintro ⟨Hf, #Hn⟩
  iNamed Hf
  iunfold stateFields
  simp only
  have HWf' : ({ s with confAt := xs } : State).Wf := by
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, _, h9, h10, h11, h12, h13⟩ := HWf
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h, h9, h10, h11, h12, h13⟩
  iframe
  iframe Hn
  try (ipureintro; exact ⟨HI, HWf'⟩)
  try (ipureintro; exact HWf')

/-- `ns.ConfAt = sl` on an owned successor: `{ s with confAt := xs }`. -/
theorem wp_set_confAt (q : Loc) (s : State) (sl : GoSlice) (xs : List Int)
    (h : xs.length = s.cfg.server.length) :
    {{ stateOwn (GF := GF) q s ∗ intsRO sl xs }}
      (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.int))))
        (Val (PairV #(q.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State, go!"ConfAt"]) #sl)))
    {{ RET #(); stateOwn q { s with confAt := xs } }} := by
  iintro %Φ ⟨Hq, #Hn⟩ HΦ
  iunfold stateOwn at Hq
  iNamed Hq
  icases (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.State_access_store_ConfAt (GF := GF) q g sl).access_strict
    $$ Hp with ⟨Hfld, Hclose⟩
  wp_apply IntoValTyped.wp_store _ _ _ $$ Hfld as Hfld
  ihave Hp := Hclose $$ Hfld
  iapply HΦ
  iunfold stateOwn
  iexists _
  iframe Hp
  iapply stateFields_with_confAt g s sl xs h
  iframe Hf
  iexact Hn

/-- `{ s with confirmed := xs }`. -/
theorem stateFields_with_confirmed (g : G.State) (s : State) (sl : GoSlice) (xs : List Confirmed)
    (h : xs.length = s.cfg.server.length) :
    stateFields (GF := GF) g s ∗ confirmedsRO sl xs ⊢ stateFields { g with Confirmed' := sl } { s with confirmed := xs } := by
  iintro ⟨Hf, #Hn⟩
  iNamed Hf
  iunfold stateFields
  simp only
  have HWf' : ({ s with confirmed := xs } : State).Wf := by
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, _, h10, h11, h12, h13⟩ := HWf
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h, h10, h11, h12, h13⟩
  iframe
  iframe Hn
  try (ipureintro; exact ⟨HI, HWf'⟩)
  try (ipureintro; exact HWf')

/-- `ns.Confirmed = sl` on an owned successor: `{ s with confirmed := xs }`. -/
theorem wp_set_confirmed (q : Loc) (s : State) (sl : GoSlice) (xs : List Confirmed)
    (h : xs.length = s.cfg.server.length) :
    {{ stateOwn (GF := GF) q s ∗ confirmedsRO sl xs }}
      (App (Val (GoInstruction (GoStore (go.GoType.SliceType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Confirmed.ty))))
        (Val (PairV #(q.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State, go!"Confirmed"]) #sl)))
    {{ RET #(); stateOwn q { s with confirmed := xs } }} := by
  iintro %Φ ⟨Hq, #Hn⟩ HΦ
  iunfold stateOwn at Hq
  iNamed Hq
  icases (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.State_access_store_Confirmed (GF := GF) q g sl).access_strict
    $$ Hp with ⟨Hfld, Hclose⟩
  wp_apply IntoValTyped.wp_store _ _ _ $$ Hfld as Hfld
  ihave Hp := Hclose $$ Hfld
  iapply HΦ
  iunfold stateOwn
  iexists _
  iframe Hp
  iapply stateFields_with_confirmed g s sl xs h
  iframe Hf
  iexact Hn

/-- `{ s with msgs := xs }`. -/
theorem stateFields_with_msgs (g : G.State) (s : State) (sl : GoSlice) (xs : List Fact) :
    stateFields (GF := GF) g s ∗ factsRO sl xs ⊢ stateFields { g with Msgs' := sl } { s with msgs := xs } := by
  iintro ⟨Hf, #Hn⟩
  iNamed Hf
  iunfold stateFields
  simp only
  have HWf' : ({ s with msgs := xs } : State).Wf := by
    exact HWf
  iframe
  iframe Hn
  try (ipureintro; exact ⟨HI, HWf'⟩)
  try (ipureintro; exact HWf')

/-- `ns.Msgs = sl` on an owned successor: `{ s with msgs := xs }`. -/
theorem wp_set_msgs (q : Loc) (s : State) (sl : GoSlice) (xs : List Fact) :
    {{ stateOwn (GF := GF) q s ∗ factsRO sl xs }}
      (App (Val (GoInstruction (GoStore (go.GoType.SliceType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Fact.ty))))
        (Val (PairV #(q.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State, go!"Msgs"]) #sl)))
    {{ RET #(); stateOwn q { s with msgs := xs } }} := by
  iintro %Φ ⟨Hq, #Hn⟩ HΦ
  iunfold stateOwn at Hq
  iNamed Hq
  icases (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.State_access_store_Msgs (GF := GF) q g sl).access_strict
    $$ Hp with ⟨Hfld, Hclose⟩
  wp_apply IntoValTyped.wp_store _ _ _ $$ Hfld as Hfld
  ihave Hp := Hclose $$ Hfld
  iapply HΦ
  iunfold stateOwn
  iexists _
  iframe Hp
  iapply stateFields_with_msgs g s sl xs
  iframe Hf
  iexact Hn

/-- `{ s with votes := xs }`. -/
theorem stateFields_with_votes (g : G.State) (s : State) (sl : GoSlice) (xs : List VoteRec) :
    stateFields (GF := GF) g s ∗ votesRO sl xs ⊢ stateFields { g with Votes' := sl } { s with votes := xs } := by
  iintro ⟨Hf, #Hn⟩
  iNamed Hf
  iunfold stateFields
  simp only
  have HWf' : ({ s with votes := xs } : State).Wf := by
    exact HWf
  iframe
  iframe Hn
  try (ipureintro; exact ⟨HI, HWf'⟩)
  try (ipureintro; exact HWf')

/-- `ns.Votes = sl` on an owned successor: `{ s with votes := xs }`. -/
theorem wp_set_votes (q : Loc) (s : State) (sl : GoSlice) (xs : List VoteRec) :
    {{ stateOwn (GF := GF) q s ∗ votesRO sl xs }}
      (App (Val (GoInstruction (GoStore (go.GoType.SliceType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.VoteRec.ty))))
        (Val (PairV #(q.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State, go!"Votes"]) #sl)))
    {{ RET #(); stateOwn q { s with votes := xs } }} := by
  iintro %Φ ⟨Hq, #Hn⟩ HΦ
  iunfold stateOwn at Hq
  iNamed Hq
  icases (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.State_access_store_Votes (GF := GF) q g sl).access_strict
    $$ Hp with ⟨Hfld, Hclose⟩
  wp_apply IntoValTyped.wp_store _ _ _ $$ Hfld as Hfld
  ihave Hp := Hclose $$ Hfld
  iapply HΦ
  iunfold stateOwn
  iexists _
  iframe Hp
  iapply stateFields_with_votes g s sl xs
  iframe Hf
  iexact Hn

/-- `{ s with leaders := xs }`. -/
theorem stateFields_with_leaders (g : G.State) (s : State) (sl : GoSlice) (xs : List LeaderRec) :
    stateFields (GF := GF) g s ∗ leadersRO sl xs ⊢ stateFields { g with Leaders' := sl } { s with leaders := xs } := by
  iintro ⟨Hf, #Hn⟩
  iNamed Hf
  iunfold stateFields
  simp only
  have HWf' : ({ s with leaders := xs } : State).Wf := by
    exact HWf
  iframe
  iframe Hn
  try (ipureintro; exact ⟨HI, HWf'⟩)
  try (ipureintro; exact HWf')

/-- `ns.Leaders = sl` on an owned successor: `{ s with leaders := xs }`. -/
theorem wp_set_leaders (q : Loc) (s : State) (sl : GoSlice) (xs : List LeaderRec) :
    {{ stateOwn (GF := GF) q s ∗ leadersRO sl xs }}
      (App (Val (GoInstruction (GoStore (go.GoType.SliceType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.LeaderRec.ty))))
        (Val (PairV #(q.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State, go!"Leaders"]) #sl)))
    {{ RET #(); stateOwn q { s with leaders := xs } }} := by
  iintro %Φ ⟨Hq, #Hn⟩ HΦ
  iunfold stateOwn at Hq
  iNamed Hq
  icases (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.State_access_store_Leaders (GF := GF) q g sl).access_strict
    $$ Hp with ⟨Hfld, Hclose⟩
  wp_apply IntoValTyped.wp_store _ _ _ $$ Hfld as Hfld
  ihave Hp := Hclose $$ Hfld
  iapply HΦ
  iunfold stateOwn
  iexists _
  iframe Hp
  iapply stateFields_with_leaders g s sl xs
  iframe Hf
  iexact Hn

/-- `{ s with ledLog := xs }`. -/
theorem stateFields_with_ledLog (g : G.State) (s : State) (sl : GoSlice) (xs : TermFn (List Entry)) :
    stateFields (GF := GF) g s ∗ termLogsRO sl xs ⊢ stateFields { g with LedLog' := sl } { s with ledLog := xs } := by
  iintro ⟨Hf, #Hn⟩
  iNamed Hf
  iunfold stateFields
  simp only
  have HWf' : ({ s with ledLog := xs } : State).Wf := by
    exact HWf
  iframe
  iframe Hn
  try (ipureintro; exact ⟨HI, HWf'⟩)
  try (ipureintro; exact HWf')

/-- `ns.LedLog = sl` on an owned successor: `{ s with ledLog := xs }`. -/
theorem wp_set_ledLog (q : Loc) (s : State) (sl : GoSlice) (xs : TermFn (List Entry)) :
    {{ stateOwn (GF := GF) q s ∗ termLogsRO sl xs }}
      (App (Val (GoInstruction (GoStore (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermLogs.ty))))
        (Val (PairV #(q.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State, go!"LedLog"]) #sl)))
    {{ RET #(); stateOwn q { s with ledLog := xs } }} := by
  iintro %Φ ⟨Hq, #Hn⟩ HΦ
  iunfold stateOwn at Hq
  iNamed Hq
  icases (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.State_access_store_LedLog (GF := GF) q g sl).access_strict
    $$ Hp with ⟨Hfld, Hclose⟩
  wp_apply IntoValTyped.wp_store _ _ _ $$ Hfld as Hfld
  ihave Hp := Hclose $$ Hfld
  iapply HΦ
  iunfold stateOwn
  iexists _
  iframe Hp
  iapply stateFields_with_ledLog g s sl xs
  iframe Hf
  iexact Hn

/-- `{ s with ledConf := xs }`. -/
theorem stateFields_with_ledConf (g : G.State) (s : State) (sl : GoSlice) (xs : TermFn Conf) :
    stateFields (GF := GF) g s ∗ termConfsRO sl xs ⊢ stateFields { g with LedConf' := sl } { s with ledConf := xs } := by
  iintro ⟨Hf, #Hn⟩
  iNamed Hf
  iunfold stateFields
  simp only
  have HWf' : ({ s with ledConf := xs } : State).Wf := by
    exact HWf
  iframe
  iframe Hn
  try (ipureintro; exact ⟨HI, HWf'⟩)
  try (ipureintro; exact HWf')

/-- `ns.LedConf = sl` on an owned successor: `{ s with ledConf := xs }`. -/
theorem wp_set_ledConf (q : Loc) (s : State) (sl : GoSlice) (xs : TermFn Conf) :
    {{ stateOwn (GF := GF) q s ∗ termConfsRO sl xs }}
      (App (Val (GoInstruction (GoStore (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermConfs.ty))))
        (Val (PairV #(q.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State, go!"LedConf"]) #sl)))
    {{ RET #(); stateOwn q { s with ledConf := xs } }} := by
  iintro %Φ ⟨Hq, #Hn⟩ HΦ
  iunfold stateOwn at Hq
  iNamed Hq
  icases (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.State_access_store_LedConf (GF := GF) q g sl).access_strict
    $$ Hp with ⟨Hfld, Hclose⟩
  wp_apply IntoValTyped.wp_store _ _ _ $$ Hfld as Hfld
  ihave Hp := Hclose $$ Hfld
  iapply HΦ
  iunfold stateOwn
  iexists _
  iframe Hp
  iapply stateFields_with_ledConf g s sl xs
  iframe Hf
  iexact Hn

/-- `{ s with ledAt := xs }`. -/
theorem stateFields_with_ledAt (g : G.State) (s : State) (sl : GoSlice) (xs : TermFn Int) :
    stateFields (GF := GF) g s ∗ termIntsRO sl xs ⊢ stateFields { g with LedAt' := sl } { s with ledAt := xs } := by
  iintro ⟨Hf, #Hn⟩
  iNamed Hf
  iunfold stateFields
  simp only
  have HWf' : ({ s with ledAt := xs } : State).Wf := by
    exact HWf
  iframe
  iframe Hn
  try (ipureintro; exact ⟨HI, HWf'⟩)
  try (ipureintro; exact HWf')

/-- `ns.LedAt = sl` on an owned successor: `{ s with ledAt := xs }`. -/
theorem wp_set_ledAt (q : Loc) (s : State) (sl : GoSlice) (xs : TermFn Int) :
    {{ stateOwn (GF := GF) q s ∗ termIntsRO sl xs }}
      (App (Val (GoInstruction (GoStore (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermInts.ty))))
        (Val (PairV #(q.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State, go!"LedAt"]) #sl)))
    {{ RET #(); stateOwn q { s with ledAt := xs } }} := by
  iintro %Φ ⟨Hq, #Hn⟩ HΦ
  iunfold stateOwn at Hq
  iNamed Hq
  icases (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.State_access_store_LedAt (GF := GF) q g sl).access_strict
    $$ Hp with ⟨Hfld, Hclose⟩
  wp_apply IntoValTyped.wp_store _ _ _ $$ Hfld as Hfld
  ihave Hp := Hclose $$ Hfld
  iapply HΦ
  iunfold stateOwn
  iexists _
  iframe Hp
  iapply stateFields_with_ledAt g s sl xs
  iframe Hf
  iexact Hn

/-- `{ s with elAt := xs }`. -/
theorem stateFields_with_elAt (g : G.State) (s : State) (sl : GoSlice) (xs : TermFn Int) :
    stateFields (GF := GF) g s ∗ termIntsRO sl xs ⊢ stateFields { g with ElAt' := sl } { s with elAt := xs } := by
  iintro ⟨Hf, #Hn⟩
  iNamed Hf
  iunfold stateFields
  simp only
  have HWf' : ({ s with elAt := xs } : State).Wf := by
    exact HWf
  iframe
  iframe Hn
  try (ipureintro; exact ⟨HI, HWf'⟩)
  try (ipureintro; exact HWf')

/-- `ns.ElAt = sl` on an owned successor: `{ s with elAt := xs }`. -/
theorem wp_set_elAt (q : Loc) (s : State) (sl : GoSlice) (xs : TermFn Int) :
    {{ stateOwn (GF := GF) q s ∗ termIntsRO sl xs }}
      (App (Val (GoInstruction (GoStore (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermInts.ty))))
        (Val (PairV #(q.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State, go!"ElAt"]) #sl)))
    {{ RET #(); stateOwn q { s with elAt := xs } }} := by
  iintro %Φ ⟨Hq, #Hn⟩ HΦ
  iunfold stateOwn at Hq
  iNamed Hq
  icases (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.State_access_store_ElAt (GF := GF) q g sl).access_strict
    $$ Hp with ⟨Hfld, Hclose⟩
  wp_apply IntoValTyped.wp_store _ _ _ $$ Hfld as Hfld
  ihave Hp := Hclose $$ Hfld
  iapply HΦ
  iunfold stateOwn
  iexists _
  iframe Hp
  iapply stateFields_with_elAt g s sl xs
  iframe Hf
  iexact Hn

/-- `{ s with undo := xs }`. -/
theorem stateFields_with_undo (g : G.State) (s : State) (sl : GoSlice) (xs : List (Option Pre))
    (h : xs.length = s.cfg.server.length) :
    stateFields (GF := GF) g s ∗ undoRO sl xs ⊢ stateFields { g with Undo' := sl } { s with undo := xs } := by
  iintro ⟨Hf, #Hn⟩
  iNamed Hf
  iunfold stateFields
  simp only
  have HWf' : ({ s with undo := xs } : State).Wf := by
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, _, h11, h12, h13⟩ := HWf
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h, h11, h12, h13⟩
  iframe
  iframe Hn
  try (ipureintro; exact ⟨HI, HWf'⟩)
  try (ipureintro; exact HWf')

/-- `ns.Undo = sl` on an owned successor: `{ s with undo := xs }`. -/
theorem wp_set_undo (q : Loc) (s : State) (sl : GoSlice) (xs : List (Option Pre))
    (h : xs.length = s.cfg.server.length) :
    {{ stateOwn (GF := GF) q s ∗ undoRO sl xs }}
      (App (Val (GoInstruction (GoStore (go.GoType.SliceType (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Pre.ty)))))
        (Val (PairV #(q.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State, go!"Undo"]) #sl)))
    {{ RET #(); stateOwn q { s with undo := xs } }} := by
  iintro %Φ ⟨Hq, #Hn⟩ HΦ
  iunfold stateOwn at Hq
  iNamed Hq
  icases (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.State_access_store_Undo (GF := GF) q g sl).access_strict
    $$ Hp with ⟨Hfld, Hclose⟩
  wp_apply IntoValTyped.wp_store _ _ _ $$ Hfld as Hfld
  ihave Hp := Hclose $$ Hfld
  iapply HΦ
  iunfold stateOwn
  iexists _
  iframe Hp
  iapply stateFields_with_undo g s sl xs h
  iframe Hf
  iexact Hn

/-- `{ s with pending := xs }`. -/
theorem stateFields_with_pending (g : G.State) (s : State) (sl : GoSlice) (xs : List (List Msg))
    (h : xs.length = s.cfg.server.length) :
    stateFields (GF := GF) g s ∗ pendingRO sl xs ⊢ stateFields { g with Pending' := sl } { s with pending := xs } := by
  iintro ⟨Hf, #Hn⟩
  iNamed Hf
  iunfold stateFields
  simp only
  have HWf' : ({ s with pending := xs } : State).Wf := by
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, _, h12, h13⟩ := HWf
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h, h12, h13⟩
  iframe
  iframe Hn
  try (ipureintro; exact ⟨HI, HWf'⟩)
  try (ipureintro; exact HWf')

/-- `ns.Pending = sl` on an owned successor: `{ s with pending := xs }`. -/
theorem wp_set_pending (q : Loc) (s : State) (sl : GoSlice) (xs : List (List Msg))
    (h : xs.length = s.cfg.server.length) :
    {{ stateOwn (GF := GF) q s ∗ pendingRO sl xs }}
      (App (Val (GoInstruction (GoStore (go.GoType.SliceType (go.GoType.SliceType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.ty)))))
        (Val (PairV #(q.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State, go!"Pending"]) #sl)))
    {{ RET #(); stateOwn q { s with pending := xs } }} := by
  iintro %Φ ⟨Hq, #Hn⟩ HΦ
  iunfold stateOwn at Hq
  iNamed Hq
  icases (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.State_access_store_Pending (GF := GF) q g sl).access_strict
    $$ Hp with ⟨Hfld, Hclose⟩
  wp_apply IntoValTyped.wp_store _ _ _ $$ Hfld as Hfld
  ihave Hp := Hclose $$ Hfld
  iapply HΦ
  iunfold stateOwn
  iexists _
  iframe Hp
  iapply stateFields_with_pending g s sl xs h
  iframe Hf
  iexact Hn

/-- `{ s with queue := xs }`. -/
theorem stateFields_with_queue (g : G.State) (s : State) (sl : GoSlice) (xs : List (List QItem))
    (h : xs.length = s.cfg.server.length) :
    stateFields (GF := GF) g s ∗ queueRO sl xs ⊢ stateFields { g with Queue' := sl } { s with queue := xs } := by
  iintro ⟨Hf, #Hn⟩
  iNamed Hf
  iunfold stateFields
  simp only
  have HWf' : ({ s with queue := xs } : State).Wf := by
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, _, h13⟩ := HWf
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h, h13⟩
  iframe
  iframe Hn
  try (ipureintro; exact ⟨HI, HWf'⟩)
  try (ipureintro; exact HWf')

/-- `ns.Queue = sl` on an owned successor: `{ s with queue := xs }`. -/
theorem wp_set_queue (q : Loc) (s : State) (sl : GoSlice) (xs : List (List QItem))
    (h : xs.length = s.cfg.server.length) :
    {{ stateOwn (GF := GF) q s ∗ queueRO sl xs }}
      (App (Val (GoInstruction (GoStore (go.GoType.SliceType (go.GoType.SliceType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.QItem.ty)))))
        (Val (PairV #(q.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State, go!"Queue"]) #sl)))
    {{ RET #(); stateOwn q { s with queue := xs } }} := by
  iintro %Φ ⟨Hq, #Hn⟩ HΦ
  iunfold stateOwn at Hq
  iNamed Hq
  icases (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.State_access_store_Queue (GF := GF) q g sl).access_strict
    $$ Hp with ⟨Hfld, Hclose⟩
  wp_apply IntoValTyped.wp_store _ _ _ $$ Hfld as Hfld
  ihave Hp := Hclose $$ Hfld
  iapply HΦ
  iunfold stateOwn
  iexists _
  iframe Hp
  iapply stateFields_with_queue g s sl xs h
  iframe Hf
  iexact Hn

/-- `{ s with reads := xs }`. -/
theorem stateFields_with_reads (g : G.State) (s : State) (sl : GoSlice) (xs : List (List ReadRec))
    (h : xs.length = s.cfg.server.length) :
    stateFields (GF := GF) g s ∗ readsRO sl xs ⊢ stateFields { g with Reads' := sl } { s with reads := xs } := by
  iintro ⟨Hf, #Hn⟩
  iNamed Hf
  iunfold stateFields
  simp only
  have HWf' : ({ s with reads := xs } : State).Wf := by
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, _⟩ := HWf
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h⟩
  iframe
  iframe Hn
  try (ipureintro; exact ⟨HI, HWf'⟩)
  try (ipureintro; exact HWf')

/-- `ns.Reads = sl` on an owned successor: `{ s with reads := xs }`. -/
theorem wp_set_reads (q : Loc) (s : State) (sl : GoSlice) (xs : List (List ReadRec))
    (h : xs.length = s.cfg.server.length) :
    {{ stateOwn (GF := GF) q s ∗ readsRO sl xs }}
      (App (Val (GoInstruction (GoStore (go.GoType.SliceType (go.GoType.SliceType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.ReadRec.ty)))))
        (Val (PairV #(q.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State, go!"Reads"]) #sl)))
    {{ RET #(); stateOwn q { s with reads := xs } }} := by
  iintro %Φ ⟨Hq, #Hn⟩ HΦ
  iunfold stateOwn at Hq
  iNamed Hq
  icases (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.State_access_store_Reads (GF := GF) q g sl).access_strict
    $$ Hp with ⟨Hfld, Hclose⟩
  wp_apply IntoValTyped.wp_store _ _ _ $$ Hfld as Hfld
  ihave Hp := Hclose $$ Hfld
  iapply HΦ
  iunfold stateOwn
  iexists _
  iframe Hp
  iapply stateFields_with_reads g s sl xs h
  iframe Hf
  iexact Hn

/-- `{ s with chain := xs }`. -/
theorem stateFields_with_chain (g : G.State) (s : State) (sl : GoSlice) (xs : List Entry) :
    stateFields (GF := GF) g s ∗ logRO sl xs ⊢ stateFields { g with Chain' := sl } { s with chain := xs } := by
  iintro ⟨Hf, #Hn⟩
  iNamed Hf
  iunfold stateFields
  simp only
  have HWf' : ({ s with chain := xs } : State).Wf := by
    exact HWf
  iframe
  iframe Hn
  try (ipureintro; exact ⟨HI, HWf'⟩)
  try (ipureintro; exact HWf')

/-- `ns.Chain = sl` on an owned successor: `{ s with chain := xs }`. -/
theorem wp_set_chain (q : Loc) (s : State) (sl : GoSlice) (xs : List Entry) :
    {{ stateOwn (GF := GF) q s ∗ logRO sl xs }}
      (App (Val (GoInstruction (GoStore (go.GoType.SliceType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Entry.ty))))
        (Val (PairV #(q.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State, go!"Chain"]) #sl)))
    {{ RET #(); stateOwn q { s with chain := xs } }} := by
  iintro %Φ ⟨Hq, #Hn⟩ HΦ
  iunfold stateOwn at Hq
  iNamed Hq
  icases (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.State_access_store_Chain (GF := GF) q g sl).access_strict
    $$ Hp with ⟨Hfld, Hclose⟩
  wp_apply IntoValTyped.wp_store _ _ _ $$ Hfld as Hfld
  ihave Hp := Hclose $$ Hfld
  iapply HΦ
  iunfold stateOwn
  iexists _
  iframe Hp
  iapply stateFields_with_chain g s sl xs
  iframe Hf
  iexact Hn

/-- `{ s with termLen := xs }`. -/
theorem stateFields_with_termLen (g : G.State) (s : State) (sl : GoSlice) (xs : TermFn Int) :
    stateFields (GF := GF) g s ∗ termIntsRO sl xs ⊢ stateFields { g with TermLen' := sl } { s with termLen := xs } := by
  iintro ⟨Hf, #Hn⟩
  iNamed Hf
  iunfold stateFields
  simp only
  have HWf' : ({ s with termLen := xs } : State).Wf := by
    exact HWf
  iframe
  iframe Hn
  try (ipureintro; exact ⟨HI, HWf'⟩)
  try (ipureintro; exact HWf')

/-- `ns.TermLen = sl` on an owned successor: `{ s with termLen := xs }`. -/
theorem wp_set_termLen (q : Loc) (s : State) (sl : GoSlice) (xs : TermFn Int) :
    {{ stateOwn (GF := GF) q s ∗ termIntsRO sl xs }}
      (App (Val (GoInstruction (GoStore (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermInts.ty))))
        (Val (PairV #(q.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State, go!"TermLen"]) #sl)))
    {{ RET #(); stateOwn q { s with termLen := xs } }} := by
  iintro %Φ ⟨Hq, #Hn⟩ HΦ
  iunfold stateOwn at Hq
  iNamed Hq
  icases (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.State_access_store_TermLen (GF := GF) q g sl).access_strict
    $$ Hp with ⟨Hfld, Hclose⟩
  wp_apply IntoValTyped.wp_store _ _ _ $$ Hfld as Hfld
  ihave Hp := Hclose $$ Hfld
  iapply HΦ
  iunfold stateOwn
  iexists _
  iframe Hp
  iapply stateFields_with_termLen g s sl xs
  iframe Hf
  iexact Hn

/-- `{ s with viol := xs }`. -/
theorem stateFields_with_viol (g : G.State) (s : State) (sl : GoSlice) (xs : SSet) :
    stateFields (GF := GF) g s ∗ strsRO sl xs ⊢ stateFields { g with Viol' := sl } { s with viol := xs } := by
  iintro ⟨Hf, #Hn⟩
  iNamed Hf
  iunfold stateFields
  simp only
  have HWf' : ({ s with viol := xs } : State).Wf := by
    exact HWf
  iframe
  iframe Hn
  try (ipureintro; exact ⟨HI, HWf'⟩)
  try (ipureintro; exact HWf')

/-- `ns.Viol = sl` on an owned successor: `{ s with viol := xs }`. -/
theorem wp_set_viol (q : Loc) (s : State) (sl : GoSlice) (xs : SSet) :
    {{ stateOwn (GF := GF) q s ∗ strsRO sl xs }}
      (App (Val (GoInstruction (GoStore (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Set''.ty))))
        (Val (PairV #(q.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State, go!"Viol"]) #sl)))
    {{ RET #(); stateOwn q { s with viol := xs } }} := by
  iintro %Φ ⟨Hq, #Hn⟩ HΦ
  iunfold stateOwn at Hq
  iNamed Hq
  icases (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.State_access_store_Viol (GF := GF) q g sl).access_strict
    $$ Hp with ⟨Hfld, Hclose⟩
  wp_apply IntoValTyped.wp_store _ _ _ $$ Hfld as Hfld
  ihave Hp := Hclose $$ Hfld
  iapply HΦ
  iunfold stateOwn
  iexists _
  iframe Hp
  iapply stateFields_with_viol g s sl xs
  iframe Hf
  iexact Hn

/-- `{ s with i := x }` (`Step`'s `ns.I = s.I + 1`). -/
theorem stateFields_with_i (g : G.State) (s : State) (w : w64) :
    stateFields (GF := GF) g s ⊢ stateFields { g with I' := w } { s with i := sint.Z w } := by
  iintro Hf
  iNamed Hf
  iunfold stateFields
  simp only
  have HWf' : ({ s with i := sint.Z w } : State).Wf := by
    exact HWf
  iframe
  try (ipureintro; exact ⟨rfl, HWf'⟩)
  try (ipureintro; exact HWf')

/-- `ns.I = w` on an owned successor: `{ s with i := sint.Z w }`. -/
theorem wp_set_i (q : Loc) (s : State) (w : w64) :
    {{ stateOwn (GF := GF) q s }}
      (App (Val (GoInstruction (GoStore go.int)))
        (Val (PairV #(q.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State, go!"I"]) #w)))
    {{ RET #(); stateOwn q { s with i := sint.Z w } }} := by
  iintro %Φ Hq HΦ
  iunfold stateOwn at Hq
  iNamed Hq
  icases (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.State_access_store_I (GF := GF) q g w).access_strict
    $$ Hp with ⟨Hfld, Hclose⟩
  wp_apply IntoValTyped.wp_store _ _ _ $$ Hfld as Hfld
  ihave Hp := Hclose $$ Hfld
  iapply HΦ
  iunfold stateOwn
  iexists _
  iframe Hp
  iapply stateFields_with_i g s w
  iexact Hf

/-- A successor built, frozen: read-only from now on. -/
theorem stateOwn_persist (q : Loc) (s : State) : stateOwn (GF := GF) q s ⊢ |==> stateRO q s := by
  iintro Hq
  iunfold stateOwn at Hq
  iNamed Hq
  ipersist Hp
  imodintro
  iunfold stateRO
  iexists g
  iframe Hp Hf

end laws

end AntCheck
end EtcdGrove
end Perennial
