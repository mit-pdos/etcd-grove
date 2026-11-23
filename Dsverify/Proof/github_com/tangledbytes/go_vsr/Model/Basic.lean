/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Model/Basic.lean (lab master 915f964;
notes/dsv-vr.md): `Harness.Model`'s key-value map (`KvInput`, `KvOutput`, its step `kvStep`) restated
here.

The pure model of go-vsr's protocol (Viewstamped Replication, normal operation, view change and
state transfer), as the fixed fork implements it (`notes/fork.md`), for `n` replicas (a field of
the state: the deployment draws 3 or 5, f = 1 or 2; quorums are lists of more than `n / 2`
distinct replicas).

The global state `Sys` holds what the safety argument needs and no more:
* each replica's protocol state `Rep` (view number, status, log, last normal view), which the
  replica's code keeps equal to its Go fields (it owns half of a ghost variable, the system's
  invariant the other half);
* the log of each started view (`vlog`, the primary's log in that view) and its initial log
  (`vinit`, the log the view started with);
* what each replica accepted in each view (`acc r w`: its log while it was normal, or in state
  transfer, in view `w`);
* the linearized log `lin` (the ops in execution order, each first executed by some replica:
  the linearization points) and the registry `reg` of client requests.

`Inv` is the system's invariant; `Fact`s are stable predicates (preserved by every step), which
messages carry as persistent witnesses. Each step is a function on `Sys` that a handler of the
code performs (as a ghost update) with the step's premises established from its Go state and
the facts it holds.

Everything here is pure Lean; the Iris side is `Ghost/`.
-/
module

public import Perennial.Std.ByteString
public import Perennial.Std.ListBasics
public import Perennial.Proof.strings.Base

@[expose] public section

namespace VsrModel

open Perennial

/-- Inputs of the key-value map (the kit's `In`: a get of `k`, or a put of `v` at `k`; the
lab's `Harness.Model.KvInput`). -/
inductive KvInput (K V : Type) where
  | get (k : K)
  | put (k : K) (v : V)
deriving DecidableEq

/-- Outputs of the key-value map (`got none`: the key was never written; the lab's
`Harness.Model.KvOutput`). -/
inductive KvOutput (V : Type) where
  | got (v : Option V)
  | done

/-- The key-value map's step from `s` (the lab's `(Harness.Model.kv K V).step`): a get reads,
a put writes. -/
def kvStep {K V : Type} [DecidableEq K] (s : K → Option V) (i : KvInput K V) (s' : K → Option V)
    (o : KvOutput V) : Prop :=
  match i with
  | .get k => s' = s ∧ o = .got (s k)
  | .put k v => s' = (fun k' => if k' = k then some v else s k') ∧ o = .done

/-! ## Entries, statuses, replicas -/

/-- The primary of view `v` among `n` replicas (`primaryForView`: `v mod n` in `uint64`). -/
def primary (n v : Nat) : Nat := v % n

/-- A log entry (`log.Log`): the operation, the client id and the client's request number. -/
structure Entry where
  op : GoString
  cid : Nat
  req : Nat
deriving DecidableEq, Inhabited

/-- A replica's status (`ReplicaStatus`; go-vsr never uses `Recovery`). -/
inductive Status where
  | normal
  | viewChange
  | stateTransfer
deriving DecidableEq, Inhabited

/-- A replica's protocol state: `view` (`ViewNumber`), `status`, `log` (`Logs`; `OpNum` is its
length), `lnv` (`lastStableViewNumber`: the last view in which it was normal, meaningful in view
change). -/
structure Rep where
  view : Nat
  status : Status
  log : List Entry
  lnv : Nat
deriving DecidableEq, Inhabited

/-- The system's state. -/
structure Sys where
  reps : Nat → Rep
  vlog : Nat → Option (List Entry)
  vinit : Nat → Option (List Entry)
  acc : Nat → Nat → List Entry
  lin : List Entry
  /-- the registered requests: client id and request number ↦ the operation's input -/
  reg : Nat → Nat → Option (KvInput GoString GoString)
  /-- the number of replicas (fixed: every step keeps it) -/
  n : Nat

/-! ## The service: the key-value store's operations -/

/-- The operation string of a key-value input (`vsrnet.Op`): `"SET k v"` or `"GET k"`. -/
def encOp : KvInput GoString GoString → GoString
  | .put k v => go!"SET " ++ k ++ go!" " ++ v
  | .get k => go!"GET " ++ k

/-- The store's state as the service's (vsrkv's map: a key's value, or none). -/
abbrev Store := GoString → Option GoString

/-- The service's step on an input (the key-value model's): the new store and the reply string
(`vsrkv.Handle`: a put's value; a get's value, `""` if none). -/
def svcStep (m : Store) : KvInput GoString GoString → Store × GoString
  | .put k v => (fun k' => if k' = k then some v else m k', v)
  | .get k => (m, (m k).getD [])

/-- `vsrkv.Handle` on an operation string: `strings.Split(op, " ")`, then `SET k v` sets `k`
and replies `v`, `GET k` replies `k`'s value (`""` if none), anything else changes nothing and
replies `""`. -/
def handle (m : Store) (op : GoString) : Store × GoString :=
  match strings.split op go!" " with
  | [c, k, v] => if c = go!"SET" then (fun k' => if k' = k then some v else m k', v)
      else (m, [])
  | [c, k] => if c = go!"GET" then (m, (m k).getD []) else (m, [])
  | _ => (m, [])

/-- The store after the entries `l`. -/
def storeOf (l : List Entry) : Store :=
  l.foldl (fun m e => (handle m e.op).1) (fun _ => none)

/-- The reply string of the `i`-th entry of `l` (executed after the entries before it). -/
def outOf (l : List Entry) (i : Nat) : GoString :=
  match l[i]? with
  | some e => (handle (storeOf (l.take i)) e.op).2
  | none => []

private theorem ite_t {α : Sort _} {c : Prop} [Decidable c] (h : c) {a b : α} :
    (if c then a else b) = a := by simp [h]

private theorem ite_f {α : Sort _} {c : Prop} [Decidable c] (h : ¬c) {a b : α} :
    (if c then a else b) = b := by simp [h]

private theorem splitAux_word (k field : GoString) (hk : ∀ b ∈ k, b ≠ 32) :
    strings.splitAux go!" " k field = [field ++ k] := by
  induction k generalizing field with
  | nil => rw [strings.splitAux]; simp
  | cons c r ih =>
    rw [strings.splitAux]
    have hc : c ≠ 32 := hk c (by simp)
    rw [ite_f (by simp [List.cons_prefix_cons]; intro h; exact hc h.symm)]
    rw [ih _ (fun b hb => hk b (by simp [hb]))]
    simp

private theorem splitAux_sep (k rest field : GoString) (hk : ∀ b ∈ k, b ≠ 32) :
    strings.splitAux go!" " (k ++ 32 :: rest) field =
      (field ++ k) :: strings.splitAux go!" " rest [] := by
  induction k generalizing field with
  | nil => rw [List.nil_append, strings.splitAux]; simp [List.cons_prefix_cons]
  | cons c r ih =>
    rw [List.cons_append, strings.splitAux]
    have hc : c ≠ 32 := hk c (by simp)
    rw [ite_f (by simp [List.cons_prefix_cons]; intro h; exact hc h.symm)]
    rw [ih _ (fun b hb => hk b (by simp [hb]))]
    simp

/-- On a registered operation (a key without spaces, a value without spaces), `handle` is the
service's step. -/
theorem handle_encOp (m : Store) (i : KvInput GoString GoString)
    (hi : match i with
      | .get k => (∀ b ∈ k, b ≠ 32)
      | .put k v => (∀ b ∈ k, b ≠ 32) ∧ (∀ b ∈ v, b ≠ 32)) :
    handle m (encOp i) = svcStep m i := by
  cases i with
  | get k =>
    have e : encOp (.get k) = go!"GET" ++ 32 :: k := by simp [encOp]
    have hs : strings.split (encOp (.get k)) go!" " = [go!"GET", k] := by
      rw [e, strings.split, splitAux_sep _ _ _ (by decide), splitAux_word _ _ hi]; simp
    simp only [handle, hs, svcStep]; simp
  | put k v =>
    have e : encOp (.put k v) = go!"SET" ++ 32 :: (k ++ 32 :: v) := by simp [encOp]
    have hs : strings.split (encOp (.put k v)) go!" " = [go!"SET", k, v] := by
      rw [e, strings.split, splitAux_sep _ _ _ (by decide), splitAux_sep _ _ _ hi.1,
        splitAux_word _ _ hi.2]; simp
    simp only [handle, hs, svcStep]; simp

/-! ## Well-formed inputs and plain strings -/

/-- A plain string: what the kit's JSON codec writes as it is, in quotes (`jsoncodec.AppendString`:
every byte in `0x20..0x7e` other than `"`, `\`, `<`, `>`, `&`); the codec panics on any other
string (SF3). A space is plain (an operation `"SET k v"` is); keys and values have none
(`InputOk`). -/
def PlainStr (s : GoString) : Prop :=
  ∀ c ∈ s, 32 ≤ c.toNat ∧ c.toNat ≤ 126 ∧ c.toNat ≠ 34 ∧ c.toNat ≠ 92 ∧ c.toNat ≠ 60 ∧
    c.toNat ≠ 62 ∧ c.toNat ≠ 38

/-- A well-formed key: no space (vsrkv's `strings.Split(op, " ")` must give back the words),
plain; it may be empty (`kit.pre` admits the empty key: `"GET "` splits into `"GET"` and `""`). -/
def KeyOk (s : GoString) : Prop := (∀ b ∈ s, b ≠ 32) ∧ PlainStr s

/-- A well-formed value: non-empty (a reply `""` means "not found"), and a key. -/
def WordOk (s : GoString) : Prop := s ≠ [] ∧ (∀ b ∈ s, b ≠ 32) ∧ PlainStr s

/-- A well-formed input (what a client registers): its key is `KeyOk`, a put's value is
`WordOk`. -/
def InputOk : KvInput GoString GoString → Prop
  | .get k => KeyOk k
  | .put k v => KeyOk k ∧ WordOk v

/-- An input's strings are short (each below 2^16 bytes; SF4, D5): what `kit.pre` gives (keys and
values below 2^16 bytes), so that every message's line is bounded
(`VsrWire.line_bound`). -/
def InputBounded : KvInput GoString GoString → Prop
  | .get k => k.length < 2 ^ 16
  | .put k v => k.length < 2 ^ 16 ∧ v.length < 2 ^ 16

/-- The bounds of a registration (SF4, D5): client `c` of `1..6`, request number `n` of
`1..2^28 - 1` (each client's budget), its input's strings short. -/
def RegBound (c n : Nat) (i : KvInput GoString GoString) : Prop :=
  1 ≤ c ∧ c ≤ 6 ∧ 1 ≤ n ∧ n < 2 ^ 28 ∧ InputBounded i

/-- A well-formed input's operation string is plain. -/
theorem encOp_plain (i : KvInput GoString GoString) (hi : InputOk i) :
    PlainStr (encOp i) := by
  cases i with
  | get k =>
    intro c hc
    simp only [encOp, List.mem_append] at hc
    rcases hc with hc | hc
    · revert c hc; decide
    · exact hi.2 c hc
  | put k v =>
    intro c hc
    simp only [encOp, List.mem_append] at hc
    rcases hc with ((hc | hc) | hc) | hc
    · revert c hc; decide
    · exact hi.1.2 c hc
    · revert c hc; decide
    · exact hi.2.2.2 c hc

/-! Helpers: the service on well-formed inputs. -/

private theorem handle_ok (m : Store) {i : KvInput GoString GoString}
    (hi : InputOk i) : handle m (encOp i) = svcStep m i := by
  apply handle_encOp
  cases i with
  | get k => exact hi.1
  | put k v => exact ⟨hi.1.1, hi.2.2.1⟩

private theorem storeOf_snoc (l : List Entry) (e : Entry) :
    storeOf (l ++ [e]) = (handle (storeOf l) e.op).1 := by
  simp [storeOf, List.foldl_append]

/-! ## Quorums, commitment -/

/-- A quorum of `n` replicas: distinct replica ids below `n`, more than half of them (f + 1 of
2f + 1: two of three, three of five). -/
def Quorum (n : Nat) (Q : List Nat) : Prop := Q.Nodup ∧ (∀ a ∈ Q, a < n) ∧ n < 2 * Q.length

/-- `l` is committed in view `w`: a quorum accepted it in `w`. -/
def CommittedIn (s : Sys) (w : Nat) (l : List Entry) : Prop :=
  ∃ Q, Quorum s.n Q ∧ ∀ a ∈ Q, l <+: s.acc a w

/-- `l` is committed: a quorum accepted it in some view. -/
def Committed (s : Sys) (l : List Entry) : Prop := ∃ w, CommittedIn s w l

/-- `l` is committed in some view up to `v` (what a replica in view `v` knows of its commit
number: it learned it in its view or an earlier one). -/
def CommittedBy (s : Sys) (v : Nat) (l : List Entry) : Prop := ∃ w, w ≤ v ∧ CommittedIn s w l

/-- `l` may be committed in view `w`, now or later: a quorum each of whose members has accepted
it in `w` or may still accept in `w` (its view is at most `w`). -/
def PossCommitted (s : Sys) (w : Nat) (l : List Entry) : Prop :=
  ∃ Q, Quorum s.n Q ∧ ∀ a ∈ Q, l <+: s.acc a w ∨ (s.reps a).view ≤ w

/-- No two entries of `l` are the same request. -/
def NoDupReq (l : List Entry) : Prop := (l.map fun e => (e.cid, e.req)).Nodup

/-- Every entry of `l` is a registered request with its operation. -/
def Registered (s : Sys) (l : List Entry) : Prop :=
  ∀ e ∈ l, ∃ i, s.reg e.cid e.req = some i ∧ e.op = encOp i

/-! Helpers (lists, prefixes, quorums). -/


private theorem registered_prefix {s : Sys} {l L : List Entry} (h : l <+: L)
    (hL : Registered s L) : Registered s l :=
  fun e he => hL e (h.subset he)

private theorem noDupReq_prefix {l L : List Entry} (h : l <+: L) (hL : NoDupReq L) :
    NoDupReq l :=
  List.Nodup.sublist (h.sublist.map _) hL

private theorem poss_of_in {s : Sys} {w : Nat} {l : List Entry} (h : CommittedIn s w l) :
    PossCommitted s w l := by
  obtain ⟨Q, hq, hQ⟩ := h
  exact ⟨Q, hq, fun a ha => .inl (hQ a ha)⟩

private theorem take_eq_of_prefix {α} {l L : List α} (h : l <+: L) {c : Nat}
    (hc : c ≤ l.length) : L.take c = l.take c := by
  obtain ⟨t, rfl⟩ := h
  rw [List.take_append_of_le_length hc]

private theorem take_prefix_of_le {α} {l L : List α} (h : l <+: L) {c : Nat}
    (hc : c ≤ l.length) : L.take c <+: l := by
  rw [take_eq_of_prefix h hc]; exact List.take_prefix _ _

private theorem getElem?_of_prefix {α} {l L : List α} (h : l <+: L) {i : Nat} {e : α}
    (hi : l[i]? = some e) : L[i]? = some e := by
  obtain ⟨t, rfl⟩ := h
  have : i < l.length := (List.getElem?_eq_some_iff.mp hi).1
  rw [List.getElem?_append_left this]; exact hi

/-- Two quorums meet (pigeonhole: together they have more than `n` ids below `n`). -/
theorem quorum_meet {n : Nat} {Q Q' : List Nat} (h : Quorum n Q) (h' : Quorum n Q') :
    ∃ a, a ∈ Q ∧ a ∈ Q' := by
  obtain ⟨hnd, hlt, hlen⟩ := h
  obtain ⟨hnd', hlt', hlen'⟩ := h'
  apply Classical.byContradiction
  intro hno
  have hdisj : ∀ a ∈ Q, ∀ b ∈ Q', a ≠ b := by
    intro a ha b hb hab; subst hab; exact hno ⟨a, ha, hb⟩
  have hnd2 : (Q ++ Q').Nodup := List.nodup_append.mpr ⟨hnd, hnd', hdisj⟩
  have hsub : Q ++ Q' ⊆ List.range n := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact List.mem_range.mpr (hlt a ha)
    · exact List.mem_range.mpr (hlt' a ha)
  have := hnd2.length_le_of_subset hsub
  simp only [List.length_append, List.length_range] at this
  omega

private theorem Quorum.exists_mem {n : Nat} {Q : List Nat} (h : Quorum n Q) : ∃ a, a ∈ Q := by
  cases Q with
  | nil => obtain ⟨-, -, h3⟩ := h; simp at h3
  | cons a _ => exact ⟨a, List.mem_cons_self⟩

/-! ## The invariant -/

/-- Replica `r`'s part of the invariant. -/
def RepInv (s : Sys) (r : Nat) : Prop :=
  let p := s.reps r
  (∀ w, p.view < w → s.acc r w = []) ∧
  Registered s p.log ∧
  (p.status = .normal ∨ p.status = .stateTransfer →
    ∃ L I, s.vlog p.view = some L ∧ s.vinit p.view = some I ∧ p.log <+: L ∧ I <+: p.log ∧
      s.acc r p.view = p.log ∧ (primary s.n p.view = r → p.log = L)) ∧
  (p.status = .viewChange →
    p.lnv < p.view ∧ (∀ w, p.lnv < w → w ≤ p.view → s.acc r w = []) ∧
      s.acc r p.lnv = p.log ∧
      ∃ L I, s.vlog p.lnv = some L ∧ s.vinit p.lnv = some I ∧ p.log <+: L ∧ I <+: p.log)

/-- The system's invariant. -/
def Inv (s : Sys) : Prop :=
  (∀ r, r < s.n → RepInv s r) ∧
  -- started views: the initial log is a prefix of the log; a view not started has no
  -- acceptances; the primary of a started view is past it, or in it and not changing views
  (∀ v, (s.vinit v).isSome = (s.vlog v).isSome) ∧
  (∀ v I L, s.vinit v = some I → s.vlog v = some L → I <+: L ∧ NoDupReq L ∧ Registered s L) ∧
  (∀ v, s.vlog v = none → ∀ q, s.acc q v = []) ∧
  (∀ v L q, s.vlog v = some L → s.acc q v <+: L) ∧
  (∀ v, (s.vinit v).isSome → v < (s.reps (primary s.n v)).view ∨
    ((s.reps (primary s.n v)).view = v ∧ (s.reps (primary s.n v)).status ≠ .viewChange)) ∧
  -- the view-change safety: what may be committed in an earlier view is in a view's initial log
  (∀ u w l I, s.vinit u = some I → w < u → PossCommitted s w l → l <+: I) ∧
  -- the linearized log is committed and has each request once
  Committed s s.lin ∧ NoDupReq s.lin ∧ Registered s s.lin ∧
  -- every registered input is well formed, and the registrations are bounded (SF4, D5)
  (∀ c n i, s.reg c n = some i → InputOk i ∧ RegBound c n i) ∧
  -- there is at least one replica
  0 < s.n

/-- A replica's state at the start: normal in view 0 with an empty log. -/
def initRep : Rep := ⟨0, .normal, [], 0⟩

/-- The start, for `n` replicas: every replica normal in view 0 with an empty log; view 0
started empty. -/
def init (n : Nat) : Sys where
  reps := fun _ => initRep
  vlog := fun v => if v = 0 then some [] else none
  vinit := fun v => if v = 0 then some [] else none
  acc := fun _ _ => []
  lin := []
  reg := fun _ _ => none
  n := n

theorem init_inv (n : Nat) (hn : 0 < n) : Inv (init n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hn⟩
  · intro r _
    refine ⟨fun _ _ => rfl, fun e he => by simp [init, initRep] at he, fun _ => ?_,
      fun h => by simp [init, initRep] at h⟩
    exact ⟨[], [], by simp [init, initRep], by simp [init, initRep], by simp [init, initRep],
      by simp [init, initRep], rfl, fun _ => rfl⟩
  · intro v; by_cases hv : v = 0 <;> simp [init, hv]
  · intro v I L hI hL
    by_cases hv : v = 0 <;> simp [init, hv] at hI hL
    subst hI hL
    exact ⟨List.prefix_refl _, List.nodup_nil, fun e he => by simp at he⟩
  · intro _ _ _; rfl
  · intro _ _ _ _; exact List.nil_prefix
  · intro v hv
    by_cases hv0 : v = 0 <;> simp [init, initRep, hv0] at hv ⊢
  · intro u w l I hI hw
    by_cases hu : u = 0 <;> simp [init, hu] at hI
    omega
  · refine ⟨0, List.range n, ⟨List.nodup_range, fun a ha => List.mem_range.mp ha, ?_⟩,
      fun _ _ => List.nil_prefix⟩
    show n < 2 * (List.range n).length
    rw [List.length_range]; omega
  · exact List.nodup_nil
  · intro e he; simp [init] at he
  · intro c n i h; simp [init] at h

/-! Helpers: consequences of the invariant. -/

private theorem Inv.vlog_ok {s : Sys} (h : Inv s) {v : Nat} {L : List Entry}
    (hL : s.vlog v = some L) : ∃ I, s.vinit v = some I ∧ I <+: L ∧ NoDupReq L ∧ Registered s L := by
  obtain ⟨-, h2, h3, -⟩ := h
  have := h2 v
  rw [hL] at this
  cases hI : s.vinit v with
  | none => rw [hI] at this; simp at this
  | some I => exact ⟨I, rfl, h3 v I L hI hL⟩

private theorem Inv.vinit_ok {s : Sys} (h : Inv s) {v : Nat} {I : List Entry}
    (hI : s.vinit v = some I) : ∃ L, s.vlog v = some L ∧ I <+: L ∧ NoDupReq L ∧ Registered s L := by
  obtain ⟨-, h2, h3, -⟩ := h
  have := h2 v
  rw [hI] at this
  cases hL : s.vlog v with
  | none => rw [hL] at this; simp at this
  | some L => exact ⟨L, rfl, h3 v I L hI hL⟩

private theorem Inv.acc_prefix {s : Sys} (h : Inv s) (q w : Nat) :
    s.acc q w = [] ∨ ∃ L, s.vlog w = some L ∧ s.acc q w <+: L := by
  obtain ⟨-, -, -, h4, h5, -⟩ := h
  cases hv : s.vlog w with
  | none => exact .inl (h4 w hv q)
  | some L => exact .inr ⟨L, rfl, h5 w L q hv⟩

private theorem Inv.committedIn_ok {s : Sys} (h : Inv s) {w : Nat} {l : List Entry}
    (hc : CommittedIn s w l) : NoDupReq l ∧ Registered s l := by
  obtain ⟨Q, hq, hQ⟩ := hc
  obtain ⟨a, haQ⟩ := hq.exists_mem
  have ha := hQ a haQ
  rcases h.acc_prefix a w with h0 | ⟨L, hL, hp⟩
  · rw [h0] at ha
    rw [List.prefix_nil.mp ha]
    exact ⟨List.nodup_nil, fun e he => by simp at he⟩
  · obtain ⟨_, _, _, hnd, hreg⟩ := h.vlog_ok hL
    exact ⟨noDupReq_prefix (ha.trans hp) hnd, registered_prefix (ha.trans hp) hreg⟩

private theorem Inv.committed_ok {s : Sys} (h : Inv s) {l : List Entry}
    (hc : Committed s l) : NoDupReq l ∧ Registered s l := by
  obtain ⟨w, hw⟩ := hc; exact h.committedIn_ok hw

private theorem Inv.safety {s : Sys} (h : Inv s) {u w : Nat} {l I : List Entry}
    (hI : s.vinit u = some I) (hw : w < u) (hp : PossCommitted s w l) : l <+: I := by
  obtain ⟨-, -, -, -, -, -, h7, -⟩ := h
  exact h7 u w l I hI hw hp

private theorem Inv.rep {s : Sys} (h : Inv s) {r : Nat} (hr : r < s.n) : RepInv s r := by
  obtain ⟨h1, -⟩ := h; exact h1 r hr

private theorem Inv.inputOk {s : Sys} (h : Inv s) {c n : Nat} {i} (hi : s.reg c n = some i) :
    InputOk i := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h11, -⟩ := h; exact (h11 c n i hi).1

private theorem Inv.comparableIn {s : Sys} (h : Inv s) {l1 l2 : List Entry} {w1 w2 : Nat}
    (h1 : CommittedIn s w1 l1) (h2 : CommittedIn s w2 l2) (hw : w1 ≤ w2) :
    l1 <+: l2 ∨ l2 <+: l1 := by
  obtain ⟨Q2, hq2, hQ2⟩ := h2
  obtain ⟨a, haQ⟩ := hq2.exists_mem
  have ha := hQ2 a haQ
  rcases h.acc_prefix a w2 with h0 | ⟨L, hL, hp⟩
  · rw [h0] at ha; rw [List.prefix_nil.mp ha]; exact .inr List.nil_prefix
  · rcases Nat.lt_or_eq_of_le hw with hlt | heq
    · obtain ⟨I, hI, hIL, -⟩ := h.vlog_ok hL
      have h1I := h.safety hI hlt (poss_of_in h1)
      rcases List.prefix_or_prefix_of_prefix hIL (ha.trans hp) with hI2 | h2I
      · exact .inl (h1I.trans hI2)
      · exact List.prefix_or_prefix_of_prefix h1I h2I
    · subst heq
      obtain ⟨Q1, hq1, hQ1⟩ := h1
      obtain ⟨a', haQ'⟩ := hq1.exists_mem
      have ha' := hQ1 a' haQ'
      rcases h.acc_prefix a' w1 with h0 | ⟨L', hL', hp'⟩
      · rw [h0] at ha'; rw [List.prefix_nil.mp ha']; exact .inl List.nil_prefix
      · rw [hL] at hL'; cases hL'
        exact List.prefix_or_prefix_of_prefix (ha'.trans hp') (ha.trans hp)

private theorem Inv.comparable {s : Sys} (h : Inv s) {l1 l2 : List Entry}
    (h1 : Committed s l1) (h2 : Committed s l2) : l1 <+: l2 ∨ l2 <+: l1 := by
  obtain ⟨w1, h1⟩ := h1
  obtain ⟨w2, h2⟩ := h2
  rcases Nat.le_total w1 w2 with hw | hw
  · exact h.comparableIn h1 h2 hw
  · exact (h.comparableIn h2 h1 hw).symm

/-! ## Messages and facts -/

/-- A DoViewChange's content (`events.DoViewChange`). -/
structure Dvc where
  view : Nat
  log : List Entry
  lnv : Nat
  commit : Nat
  rid : Nat
deriving DecidableEq

/-- The events of `pkg/events` (the payloads), as the model sees them. -/
inductive Msg where
  | request (id cid : Nat) (op : GoString)
  | reply (id cid view : Nat) (result : GoString)
  | prepare (view opnum commit : Nat) (req : Entry) (rid : Nat)
  | prepareOK (view opnum rid : Nat)
  | commit (view commit rid : Nat)
  | startViewChange (view rid : Nat)
  | doViewChange (d : Dvc)
  | startView (view opnum commit : Nat) (logs : List Entry) (rid : Nat)
  | getState (view opnum rid : Nat)
  | newState (view : Nat) (logs : List Entry) (commit opnum rid : Nat)
  | heartbeat
deriving DecidableEq

/-- Every string of message `m` (operations, results) is plain: what encoding its event needs
(the codec panics otherwise). -/
def PlainMsg : Msg → Prop
  | .request _ _ op => PlainStr op
  | .reply _ _ _ res => PlainStr res
  | .prepare _ _ _ e _ => PlainStr e.op
  | .doViewChange d => ∀ e ∈ d.log, PlainStr e.op
  | .startView _ _ _ logs _ => ∀ e ∈ logs, PlainStr e.op
  | .newState _ logs _ _ _ => ∀ e ∈ logs, PlainStr e.op
  | _ => True

/-- An entry's ids fit in `uint64` (`log.Log`'s fields). -/
def EntryBound (e : Entry) : Prop := e.cid < 2 ^ 64 ∧ e.req < 2 ^ 64

/-- Every number of message `m` fits in `uint64` (its payload's fields, a DoViewChange's
`OpNum` = its log's length, and its log entries' ids): what decoding needs (the decoder rejects
larger numbers; codec-1, D5). Not a consequence of the model: writers have it from their Go
`uint64`s. -/
def MsgBound : Msg → Prop
  | .request id cid _ => id < 2 ^ 64 ∧ cid < 2 ^ 64
  | .reply id cid v _ => id < 2 ^ 64 ∧ cid < 2 ^ 64 ∧ v < 2 ^ 64
  | .prepare v k c e rid => v < 2 ^ 64 ∧ k < 2 ^ 64 ∧ c < 2 ^ 64 ∧ EntryBound e ∧ rid < 2 ^ 64
  | .prepareOK v k rid => v < 2 ^ 64 ∧ k < 2 ^ 64 ∧ rid < 2 ^ 64
  | .commit v c rid => v < 2 ^ 64 ∧ c < 2 ^ 64 ∧ rid < 2 ^ 64
  | .startViewChange v rid => v < 2 ^ 64 ∧ rid < 2 ^ 64
  | .doViewChange d => d.view < 2 ^ 64 ∧ d.log.length < 2 ^ 64 ∧ d.lnv < 2 ^ 64 ∧
      d.commit < 2 ^ 64 ∧ d.rid < 2 ^ 64 ∧ ∀ e ∈ d.log, EntryBound e
  | .startView v k c logs rid => v < 2 ^ 64 ∧ k < 2 ^ 64 ∧ c < 2 ^ 64 ∧ rid < 2 ^ 64 ∧
      ∀ e ∈ logs, EntryBound e
  | .getState v k rid => v < 2 ^ 64 ∧ k < 2 ^ 64 ∧ rid < 2 ^ 64
  | .newState v logs c k rid => v < 2 ^ 64 ∧ c < 2 ^ 64 ∧ k < 2 ^ 64 ∧ rid < 2 ^ 64 ∧
      ∀ e ∈ logs, EntryBound e
  | .heartbeat => True

/-- What a valid DoViewChange from replica `d.rid` for view `d.view` says: the replica is past
the view's start, accepted nothing after its last normal view `d.lnv`, and its log is what it
accepted in `d.lnv` (a prefix of that view's log, with its initial log), committed up to
`d.commit`. -/
def DvcValid (s : Sys) (d : Dvc) : Prop :=
  d.rid < s.n ∧ d.lnv < d.view ∧ d.view ≤ (s.reps d.rid).view ∧
  (∀ w, d.lnv < w → w < d.view → s.acc d.rid w = []) ∧
  s.acc d.rid d.lnv <+: d.log ∧
  (∃ L I, s.vlog d.lnv = some L ∧ s.vinit d.lnv = some I ∧ d.log <+: L ∧ I <+: d.log) ∧
  d.commit ≤ d.log.length ∧ CommittedBy s d.view (d.log.take d.commit)

/-- A message's validity (stable: `msgValid_mono`). -/
def MsgValid (s : Sys) : Msg → Prop
  | .request id cid op => ∃ i, s.reg cid id = some i ∧ op = encOp i
  | .reply id cid _ result => ∃ i e, s.lin[i]? = some e ∧ e.cid = cid ∧ e.req = id ∧
      outOf s.lin i = result
  | .prepare v k c e _ => ∃ L, s.vlog v = some L ∧ 1 ≤ k ∧ L[k - 1]? = some e ∧
      c ≤ L.length ∧ CommittedBy s v (L.take c)
  | .prepareOK v k j => j < s.n ∧ k ≤ (s.acc j v).length
  | .commit v c _ => ∃ L, s.vlog v = some L ∧ c ≤ L.length ∧ CommittedBy s v (L.take c)
  | .startViewChange _ _ => True
  | .doViewChange d => DvcValid s d
  | .startView v k c logs _ => s.vinit v = some logs ∧ k = logs.length ∧ c ≤ k ∧
      CommittedBy s v (logs.take c)
  | .getState _ _ _ => True
  | .newState v logs _ k _ => ∃ L, s.vlog v = some L ∧ k ≤ L.length ∧ logs.length ≤ k ∧
      logs = (L.take k).drop (k - logs.length)
  | .heartbeat => True

/-- The stable facts that persistent witnesses carry. -/
inductive Fact where
  /-- a message is valid -/
  | msg (m : Msg)
  /-- `l` is committed in a view up to `v` -/
  | committedBy (v : Nat) (l : List Entry)
  /-- `l` is a prefix of the linearized log -/
  | linPrefix (l : List Entry)
  /-- the system has `n` replicas -/
  | size (n : Nat)

/-- What a fact says of a state. -/
def Holds (s : Sys) : Fact → Prop
  | .msg m => MsgValid s m
  | .committedBy v l => CommittedBy s v l
  | .linPrefix l => l <+: s.lin
  | .size n => s.n = n

/-! ## Growth: every step only extends the state -/

/-- `s'` extends `s`: views do not decrease, started views stay started with the same initial
log and an extended log, acceptances and the linearized log are extended, registrations stay. -/
def Le (s s' : Sys) : Prop :=
  (∀ r, (s.reps r).view ≤ (s'.reps r).view) ∧
  (∀ v I, s.vinit v = some I → s'.vinit v = some I) ∧
  (∀ v L, s.vlog v = some L → ∃ L', s'.vlog v = some L' ∧ L <+: L') ∧
  (∀ r w, s.acc r w <+: s'.acc r w) ∧
  (∀ r w, (s.reps r).view ≠ w → s'.acc r w = s.acc r w ∨ (s.reps r).view < w) ∧
  s.lin <+: s'.lin ∧
  (∀ c n i, s.reg c n = some i → s'.reg c n = some i) ∧
  s'.n = s.n

private theorem Le.committedIn {s s' : Sys} (hle : Le s s') {w : Nat} {l : List Entry}
    (h : CommittedIn s w l) : CommittedIn s' w l := by
  obtain ⟨-, -, -, hacc, -, -, -, hn⟩ := hle
  obtain ⟨Q, hq, hQ⟩ := h
  exact ⟨Q, by rw [hn]; exact hq, fun a ha => (hQ a ha).trans (hacc a w)⟩

private theorem Le.committedBy {s s' : Sys} (hle : Le s s') {v : Nat} {l : List Entry}
    (h : CommittedBy s v l) : CommittedBy s' v l := by
  obtain ⟨w, hw, h⟩ := h; exact ⟨w, hw, hle.committedIn h⟩

private theorem Le.committed {s s' : Sys} (hle : Le s s') {l : List Entry}
    (h : Committed s l) : Committed s' l := by
  obtain ⟨w, h⟩ := h; exact ⟨w, hle.committedIn h⟩

private theorem Le.registered {s s' : Sys} (hle : Le s s') {l : List Entry}
    (h : Registered s l) : Registered s' l := by
  obtain ⟨-, -, -, -, -, -, hreg, -⟩ := hle
  intro e he
  obtain ⟨i, hi, hop⟩ := h e he
  exact ⟨i, hreg _ _ _ hi, hop⟩

/-- Going back along `Le`: what may be committed later may be committed now. -/
private theorem Le.poss_back {s s' : Sys} (hle : Le s s') {w : Nat} {l : List Entry}
    (h : PossCommitted s' w l) : PossCommitted s w l := by
  obtain ⟨hview, -, -, -, hfix, -, -, hn⟩ := hle
  have key : ∀ a, (l <+: s'.acc a w ∨ (s'.reps a).view ≤ w) →
      (l <+: s.acc a w ∨ (s.reps a).view ≤ w) := by
    intro a ha
    rcases ha with ha | ha
    · by_cases hv : (s.reps a).view = w
      · exact .inr (by omega)
      · rcases hfix a w hv with he | he
        · rw [he] at ha; exact .inl ha
        · exact .inr (by omega)
    · exact .inr (Nat.le_trans (hview a) ha)
  obtain ⟨Q, hq, hQ⟩ := h
  exact ⟨Q, by rw [← hn]; exact hq, fun a ha => key a (hQ a ha)⟩

private theorem outOf_prefix {l L : List Entry} (h : l <+: L) {i : Nat} (hi : i < l.length) :
    outOf L i = outOf l i := by
  obtain ⟨t, rfl⟩ := h
  unfold outOf
  rw [List.getElem?_append_left hi, List.take_append_of_le_length (Nat.le_of_lt hi)]

private theorem Le.refl (s : Sys) : Le s s :=
  ⟨fun _ => Nat.le_refl _, fun _ _ h => h, fun _ L h => ⟨L, h, List.prefix_refl _⟩,
    fun _ _ => List.prefix_refl _, fun _ _ _ => .inl rfl, List.prefix_refl _, fun _ _ _ h => h,
    rfl⟩

theorem holds_mono {s s' : Sys} (h : Le s s') (f : Fact) : Holds s f → Holds s' f := by
  have hle := h
  obtain ⟨hview, hvinit, hvlog, hacc, hfix, hlin, hreg, hn⟩ := h
  cases f with
  | size n' => exact fun h' => hn.trans h'
  | committedBy v l => exact hle.committedBy
  | linPrefix l => exact fun h' => h'.trans hlin
  | msg m =>
    cases m with
    | request id cid op =>
      rintro ⟨i, hi, hop⟩; exact ⟨i, hreg _ _ _ hi, hop⟩
    | reply id cid v res =>
      rintro ⟨i, e, hie, hc, hr, hout⟩
      have hi : i < s.lin.length := (List.getElem?_eq_some_iff.mp hie).1
      exact ⟨i, e, getElem?_of_prefix hlin hie, hc, hr, by rw [outOf_prefix hlin hi]; exact hout⟩
    | prepare v k c e rid =>
      rintro ⟨L, hL, hk, hLe, hc, hcom⟩
      obtain ⟨L', hL', hLL'⟩ := hvlog v L hL
      exact ⟨L', hL', hk, getElem?_of_prefix hLL' hLe, Nat.le_trans hc hLL'.length_le,
        by rw [take_eq_of_prefix hLL' hc]; exact hle.committedBy hcom⟩
    | prepareOK v k j =>
      rintro ⟨hj, hk⟩; exact ⟨by rw [hn]; exact hj, Nat.le_trans hk (hacc j v).length_le⟩
    | commit v c rid =>
      rintro ⟨L, hL, hc, hcom⟩
      obtain ⟨L', hL', hLL'⟩ := hvlog v L hL
      exact ⟨L', hL', Nat.le_trans hc hLL'.length_le,
        by rw [take_eq_of_prefix hLL' hc]; exact hle.committedBy hcom⟩
    | startViewChange v rid => exact id
    | doViewChange d =>
      rintro ⟨hrid, hlnv, hview', hnone, hacc', ⟨L, I, hL, hI, hdL, hId⟩, hc, hcom⟩
      obtain ⟨L', hL', hLL'⟩ := hvlog _ L hL
      refine ⟨by rw [hn]; exact hrid, hlnv, Nat.le_trans hview' (hview _), ?_, ?_, ⟨L', I, hL', hvinit _ _ hI,
        hdL.trans hLL', hId⟩, hc, hle.committedBy hcom⟩
      · intro w h1 h2
        rcases hfix d.rid w (by omega) with he | he
        · rw [he]; exact hnone w h1 h2
        · omega
      · rcases hfix d.rid d.lnv (by omega) with he | he
        · rw [he]; exact hacc'
        · omega
    | startView v k c logs rid =>
      rintro ⟨hI, hk, hc, hcom⟩; exact ⟨hvinit _ _ hI, hk, hc, hle.committedBy hcom⟩
    | getState v k rid => exact id
    | newState v logs c k rid =>
      rintro ⟨L, hL, hk, hlen, heq⟩
      obtain ⟨L', hL', hLL'⟩ := hvlog v L hL
      exact ⟨L', hL', Nat.le_trans hk hLL'.length_le, hlen, by rw [take_eq_of_prefix hLL' hk]; exact heq⟩
    | heartbeat => exact id

/-! ## The steps -/

/-- `s` with replica `r`'s state `p`. -/
def Sys.setRep (s : Sys) (r : Nat) (p : Rep) : Sys :=
  { s with reps := fun x => if x = r then p else s.reps x }

/-- `s` with replica `r`'s acceptance in view `w` set to `l`. -/
def Sys.setAcc (s : Sys) (r w : Nat) (l : List Entry) : Sys :=
  { s with acc := fun x y => if x = r ∧ y = w then l else s.acc x y }

/-- `s` with view `v`'s log set to `l`. -/
def Sys.setVlog (s : Sys) (v : Nat) (l : List Entry) : Sys :=
  { s with vlog := fun x => if x = v then some l else s.vlog x }

/-- A replica's part of the invariant survives a step that leaves its state and acceptances
alone, only extends view logs (not its own as primary), keeps initial logs and registrations. -/
private theorem repInv_frame {s s' : Sys} {q : Nat} (hR : RepInv s q)
    (hn : s'.n = s.n)
    (hrep : s'.reps q = s.reps q) (hacc : ∀ w, s'.acc q w = s.acc q w)
    (hvlog : ∀ w L, s.vlog w = some L →
      ∃ L', s'.vlog w = some L' ∧ L <+: L' ∧ (primary s.n w = q → L' = L))
    (hvinit : ∀ w I, s.vinit w = some I → s'.vinit w = some I)
    (hreg : ∀ {l}, Registered s l → Registered s' l) : RepInv s' q := by
  unfold RepInv at hR ⊢
  simp only [hrep, hacc, hn]
  obtain ⟨r1, r2, r3, r4⟩ := hR
  refine ⟨r1, hreg r2, fun hs => ?_, fun hs => ?_⟩
  · obtain ⟨L, I, hL, hI, hpL, hIp, ha, hprim⟩ := r3 hs
    obtain ⟨L', hL', hLL', hpr⟩ := hvlog _ _ hL
    exact ⟨L', I, hL', hvinit _ _ hI, hpL.trans hLL', hIp, ha,
      fun hp => by rw [hpr hp]; exact hprim hp⟩
  · obtain ⟨a, b, c, L, I, hL, hI, hpL, hIp⟩ := r4 hs
    obtain ⟨L', hL', hLL', -⟩ := hvlog _ _ hL
    exact ⟨a, b, c, L', I, hL', hvinit _ _ hI, hpL.trans hLL', hIp⟩

/-- `Le` for a step that changes only replica `r`'s state and acceptances. -/
private theorem le_of_rep_step {s s' : Sys} (r : Nat) (hvlog : s'.vlog = s.vlog)
    (hvinit : s'.vinit = s.vinit) (hlin : s'.lin = s.lin) (hreg : s'.reg = s.reg)
    (hn : s'.n = s.n)
    (hreps : ∀ x, x ≠ r → s'.reps x = s.reps x) (hacc : ∀ x w, x ≠ r → s'.acc x w = s.acc x w)
    (hview : (s.reps r).view ≤ (s'.reps r).view) (haccr : ∀ w, s.acc r w <+: s'.acc r w)
    (hfixr : ∀ w, (s.reps r).view ≠ w → s'.acc r w = s.acc r w ∨ (s.reps r).view < w) :
    Le s s' := by
  refine ⟨?_, fun w I h => by rw [hvinit]; exact h, fun w L h => ⟨L, by rw [hvlog]; exact h,
    List.prefix_refl _⟩, ?_, ?_, by rw [hlin]; exact List.prefix_refl _,
    fun c n i h => by rw [hreg]; exact h, hn⟩
  · intro x; by_cases hx : x = r
    · subst hx; exact hview
    · rw [hreps x hx]; exact Nat.le_refl _
  · intro x w; by_cases hx : x = r
    · subst hx; exact haccr w
    · rw [hacc x w hx]; exact List.prefix_refl _
  · intro x w hxw; by_cases hx : x = r
    · subst hx; exact hfixr w hxw
    · exact .inl (hacc x w hx)

/-- `Inv` after a step that changes only replica `r`'s state and acceptances. -/
private theorem inv_of_rep_step {s s' : Sys} (h : Inv s) (r : Nat) (hle : Le s s')
    (hvlog : s'.vlog = s.vlog) (hvinit : s'.vinit = s.vinit) (hlin : s'.lin = s.lin)
    (hreg : s'.reg = s.reg)
    (hreps : ∀ x, x ≠ r → s'.reps x = s.reps x) (hacc : ∀ x w, x ≠ r → s'.acc x w = s.acc x w)
    (hrep : RepInv s' r)
    (hacc5 : ∀ L w, s.vlog w = some L → s'.acc r w <+: L)
    (hacc4 : ∀ w, s.vlog w = none → s'.acc r w = [])
    (hprim : ∀ u, (s.vinit u).isSome → primary s.n u = r → u < (s'.reps r).view ∨
      ((s'.reps r).view = u ∧ (s'.reps r).status ≠ .viewChange)) :
    Inv s' := by
  have hn : s'.n = s.n := hle.2.2.2.2.2.2.2
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, hl, hnd, hrg, hin, hpos⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hn]; exact hpos⟩
  · intro q hq
    rw [hn] at hq
    by_cases hqr : q = r
    · subst hqr; exact hrep
    · exact repInv_frame (h1 q hq) hn (hreps q hqr) (fun w => hacc q w hqr)
        (fun w L hL => ⟨L, by rw [hvlog]; exact hL, List.prefix_refl _, fun _ => rfl⟩)
        (fun w I hI => by rw [hvinit]; exact hI) hle.registered
  · intro w; rw [hvinit, hvlog]; exact h2 w
  · intro w I L hI hL
    rw [hvinit] at hI; rw [hvlog] at hL
    obtain ⟨a, b, c⟩ := h3 w I L hI hL
    exact ⟨a, b, hle.registered c⟩
  · intro w hw q
    rw [hvlog] at hw
    by_cases hqr : q = r
    · subst hqr; exact hacc4 w hw
    · rw [hacc q w hqr]; exact h4 w hw q
  · intro w L q hL
    rw [hvlog] at hL
    by_cases hqr : q = r
    · subst hqr; exact hacc5 L w hL
    · rw [hacc q w hqr]; exact h5 w L q hL
  · intro u hu
    rw [hvinit] at hu
    rw [hn]
    by_cases hPr : primary s.n u = r
    · rw [hPr]; exact hprim u hu hPr
    · rw [hreps _ hPr]; exact h6 u hu
  · intro u w l I hI hw hp
    rw [hvinit] at hI
    exact h7 u w l I hI hw (hle.poss_back hp)
  · rw [hlin]; exact hle.committed hl
  · rw [hlin]; exact hnd
  · rw [hlin]; exact hle.registered hrg
  · intro c n i hi; rw [hreg] at hi; exact hin c n i hi

private theorem prefix_snoc {α} {P L : List α} {e : α} (h : P <+: L) (he : L[P.length]? = some e) :
    P ++ [e] <+: L := by
  obtain ⟨t, rfl⟩ := h
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at he
  cases t with
  | nil => simp at he
  | cons x t =>
    simp at he
    subst he
    exact ⟨t, by simp⟩

/-- A client registers request `n` of client `c` with input `i` (`client.Request`, before the
request is sent). -/
def stepRegister (s : Sys) (c n : Nat) (i : KvInput GoString GoString) : Sys :=
  { s with reg := fun x y => if x = c ∧ y = n then some i else s.reg x y }

theorem stepRegister_inv (s : Sys) (c n : Nat) (i : KvInput GoString GoString)
    (h : Inv s) (hn : s.reg c n = none) (hi : InputOk i) (hb : RegBound c n i) :
    Inv (stepRegister s c n i) ∧ Le s (stepRegister s c n i) := by
  have hle : Le s (stepRegister s c n i) := by
    refine ⟨fun _ => Nat.le_refl _, fun _ _ h => h, fun _ L h => ⟨L, h, List.prefix_refl _⟩,
      fun _ _ => List.prefix_refl _, fun _ _ _ => .inl rfl, List.prefix_refl _, ?_, rfl⟩
    intro x y j hj
    simp only [stepRegister]
    split
    · rename_i hxy; obtain ⟨rfl, rfl⟩ := hxy; rw [hn] at hj; cases hj
    · exact hj
  refine ⟨?_, hle⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, hlin, hnd, hreg, hin, hpos⟩ := h
  refine ⟨fun q hq => repInv_frame (h1 q hq) rfl rfl (fun _ => rfl)
      (fun w L hL => ⟨L, hL, List.prefix_refl _, fun _ => rfl⟩) (fun _ _ h => h) hle.registered,
    h2, fun v I L hI hL => ?_, h4, h5, h6, fun u w l I hI hw hp => h7 u w l I hI hw (hle.poss_back hp),
    hle.committed hlin, hnd, hle.registered hreg, ?_, hpos⟩
  · obtain ⟨a, b, c⟩ := h3 v I L hI hL; exact ⟨a, b, hle.registered c⟩
  · intro x y j hj
    simp only [stepRegister] at hj
    split at hj
    · rename_i hxy; obtain ⟨rfl, rfl⟩ := hxy; cases hj; exact ⟨hi, hb⟩
    · exact hin x y j hj

/-- The primary `r` appends a request `e` to its log (`onRequest`). -/
def stepAppend (s : Sys) (r : Nat) (e : Entry) : Sys :=
  let p := s.reps r
  let l := p.log ++ [e]
  ((s.setRep r { p with log := l }).setAcc r p.view l).setVlog p.view l

theorem stepAppend_inv (s : Sys) (r : Nat) (e : Entry) (h : Inv s) (hr : r < s.n)
    (hn : (s.reps r).status = .normal) (hp : primary s.n (s.reps r).view = r)
    (hreg : ∃ i, s.reg e.cid e.req = some i ∧ e.op = encOp i)
    (hnew : ∀ e' ∈ (s.reps r).log, e'.cid = e.cid → e'.req < e.req) :
    Inv (stepAppend s r e) ∧ Le s (stepAppend s r e) := by
  have hRr := h.rep hr
  obtain ⟨r1, r2, r3, -⟩ := hRr
  obtain ⟨L, I, hL, hI, hpL, hIp, hacc, hprim⟩ := r3 (.inl hn)
  have hPL := hprim hp
  subst hPL
  obtain ⟨_, _, _, hndL, -⟩ := h.vlog_ok hL
  have hregl : Registered s ((s.reps r).log ++ [e]) := by
    intro e' he'
    rcases List.mem_append.mp he' with h' | h'
    · exact r2 e' h'
    · rw [List.mem_singleton] at h'; subst h'; exact hreg
  have hndl : NoDupReq ((s.reps r).log ++ [e]) := by
    unfold NoDupReq at hndL ⊢
    rw [List.map_append, List.nodup_append]
    refine ⟨hndL, by simp, ?_⟩
    intro a ha b hb heq
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp ha
    simp at hb
    subst hb
    simp only [Prod.mk.injEq] at heq
    have := hnew e' he' heq.1
    omega
  have h6o : ∀ u, (s.vinit u).isSome → primary s.n u = r → u < (s.reps r).view ∨
      ((s.reps r).view = u ∧ (s.reps r).status ≠ .viewChange) := by
    obtain ⟨-, -, -, -, -, h6, -⟩ := h
    intro u hu hPr; have := h6 u hu; rw [hPr] at this; exact this
  have ereps : ∀ x, (stepAppend s r e).reps x =
      if x = r then { s.reps r with log := (s.reps r).log ++ [e] } else s.reps x := fun _ => rfl
  have eacc : ∀ x y, (stepAppend s r e).acc x y =
      if x = r ∧ y = (s.reps r).view then (s.reps r).log ++ [e] else s.acc x y := fun _ _ => rfl
  have evlog : ∀ x, (stepAppend s r e).vlog x =
      if x = (s.reps r).view then some ((s.reps r).log ++ [e]) else s.vlog x := fun _ => rfl
  have evinit : (stepAppend s r e).vinit = s.vinit := rfl
  have elin : (stepAppend s r e).lin = s.lin := rfl
  have ereg : (stepAppend s r e).reg = s.reg := rfl
  have en : (stepAppend s r e).n = s.n := rfl
  generalize stepAppend s r e = s' at *
  generalize hV : (s.reps r).view = V at *
  generalize hP : (s.reps r).log = P at *
  have hreps : ∀ x, x ≠ r → s'.reps x = s.reps x := fun x hx => by rw [ereps, ite_f hx]
  have haccx : ∀ x w, x ≠ r → s'.acc x w = s.acc x w :=
    fun x w hx => by rw [eacc, ite_f (fun h => hx h.1)]
  have hrr : s'.reps r = { s.reps r with log := P ++ [e] } := by rw [ereps, ite_t rfl]
  have haccr : ∀ w, w ≠ V → s'.acc r w = s.acc r w :=
    fun w hw => by rw [eacc, ite_f (fun h => hw h.2)]
  have haccv : s'.acc r V = P ++ [e] := by rw [eacc, ite_t ⟨rfl, rfl⟩]
  have hvl : ∀ w, w ≠ V → s'.vlog w = s.vlog w := fun w hw => by rw [evlog, ite_f hw]
  have hvlV : s'.vlog V = some (P ++ [e]) := by rw [evlog, ite_t rfl]
  have hle : Le s s' := by
    refine ⟨?_, fun w I h => by rw [evinit]; exact h, ?_, ?_, ?_, by rw [elin]; exact List.prefix_refl _,
      fun c n i h => by rw [ereg]; exact h, en⟩
    · intro x
      by_cases hx : x = r
      · subst hx; rw [hrr]; exact Nat.le_refl _
      · rw [hreps x hx]; exact Nat.le_refl _
    · intro w L0 hL0
      by_cases hw : w = V
      · subst hw; rw [hL] at hL0; cases hL0
        exact ⟨P ++ [e], hvlV, List.prefix_append _ _⟩
      · rw [hvl w hw]; exact ⟨L0, hL0, List.prefix_refl _⟩
    · intro x w
      by_cases hxw : x = r ∧ w = V
      · obtain ⟨rfl, rfl⟩ := hxw; rw [haccv, hacc]; exact List.prefix_append _ _
      · rw [eacc, ite_f hxw]; exact List.prefix_refl _
    · intro x w hxw
      by_cases hx : x = r
      · subst hx
        rw [hV] at hxw
        exact .inl (haccr w (Ne.symm hxw))
      · exact .inl (haccx x w hx)
  refine ⟨?_, hle⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, hlin, hnd, hrg, hin, hpos⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [en]; exact hpos⟩
  · intro q hq
    rw [en] at hq
    by_cases hqr : q = r
    · subst hqr
      unfold RepInv
      rw [hrr, en]
      dsimp only
      rw [hV]
      refine ⟨fun w hw => ?_, hle.registered hregl, fun _ => ⟨P ++ [e], I, hvlV,
        by rw [evinit]; exact hI, List.prefix_refl _, hIp.trans (List.prefix_append _ _), haccv,
        fun _ => rfl⟩, fun hs => by rw [hn] at hs; cases hs⟩
      rw [haccr w (by omega)]; exact r1 w (by omega)
    · refine repInv_frame (h1 q hq) en (hreps q hqr) (fun w => haccx q w hqr) ?_
        (fun w I h => by rw [evinit]; exact h) hle.registered
      intro w L0 hL0
      by_cases hw : w = V
      · subst hw; rw [hL] at hL0; cases hL0
        exact ⟨P ++ [e], hvlV, List.prefix_append _ _, fun hpq => absurd (hp.symm.trans hpq).symm hqr⟩
      · rw [hvl w hw]; exact ⟨L0, hL0, List.prefix_refl _, fun _ => rfl⟩
  · intro w; rw [evinit]
    by_cases hw : w = V
    · subst hw; rw [hvlV, hI]; rfl
    · rw [hvl w hw]; exact h2 w
  · intro w I0 L0 hI0 hL0
    rw [evinit] at hI0
    by_cases hw : w = V
    · subst hw; rw [hvlV] at hL0; cases hL0; rw [hI] at hI0; cases hI0
      exact ⟨hIp.trans (List.prefix_append _ _), hndl, hle.registered hregl⟩
    · rw [hvl w hw] at hL0
      obtain ⟨a, b, c⟩ := h3 w I0 L0 hI0 hL0
      exact ⟨a, b, hle.registered c⟩
  · intro w hw q
    by_cases hwV : w = V
    · subst hwV; rw [hvlV] at hw; cases hw
    · rw [hvl w hwV] at hw
      by_cases hqr : q = r
      · subst hqr; rw [haccr w hwV]; exact h4 w hw q
      · rw [haccx q w hqr]; exact h4 w hw q
  · intro w L0 q hL0
    by_cases hwV : w = V
    · subst hwV; rw [hvlV] at hL0; cases hL0
      by_cases hqr : q = r
      · subst hqr; rw [haccv]; exact List.prefix_refl _
      · rw [haccx q w hqr]; exact (h5 w P q hL).trans (List.prefix_append _ _)
    · rw [hvl w hwV] at hL0
      by_cases hqr : q = r
      · subst hqr; rw [haccr w hwV]; exact h5 w L0 q hL0
      · rw [haccx q w hqr]; exact h5 w L0 q hL0
  · intro u hu
    rw [evinit] at hu
    rw [en]
    by_cases hPr : primary s.n u = r
    · rw [hPr, hrr]; dsimp only; rw [hV]; exact h6o u hu hPr
    · rw [hreps _ hPr]; exact h6 u hu
  · intro u w l I0 hI0 hw hpc
    rw [evinit] at hI0
    exact h7 u w l I0 hI0 hw (hle.poss_back hpc)
  · rw [elin]; exact hle.committed hlin
  · rw [elin]; exact hnd
  · rw [elin]; exact hle.registered hrg
  · intro c n i hi; rw [ereg] at hi; exact hin c n i hi

/-- A backup `r` accepts a Prepare's request `e` as its next entry (`onPrepare`). -/
def stepAccept (s : Sys) (r : Nat) (e : Entry) : Sys :=
  let p := s.reps r
  let l := p.log ++ [e]
  (s.setRep r { p with log := l }).setAcc r p.view l

theorem stepAccept_inv (s : Sys) (r : Nat) (e : Entry) (c rid : Nat) (h : Inv s) (hr : r < s.n)
    (hn : (s.reps r).status = .normal) (hp : primary s.n (s.reps r).view ≠ r)
    (hm : MsgValid s (.prepare (s.reps r).view ((s.reps r).log.length + 1) c e rid)) :
    Inv (stepAccept s r e) ∧ Le s (stepAccept s r e) := by
  have hRr := h.rep hr
  obtain ⟨r1, r2, r3, -⟩ := hRr
  obtain ⟨L, I, hL, hI, hpL, hIp, hacc, -⟩ := r3 (.inl hn)
  obtain ⟨L', hL', -, hLe, -⟩ := hm
  rw [hL] at hL'; cases hL'
  have hLe' : L[(s.reps r).log.length]? = some e := by simpa using hLe
  have hsnoc := prefix_snoc hpL hLe'
  obtain ⟨_, _, _, _, hregL⟩ := h.vlog_ok hL
  have hregl : Registered s ((s.reps r).log ++ [e]) := registered_prefix hsnoc hregL
  have h6o : ∀ u, (s.vinit u).isSome → primary s.n u = r → u < (s.reps r).view ∨
      ((s.reps r).view = u ∧ (s.reps r).status ≠ .viewChange) := by
    obtain ⟨-, -, -, -, -, h6, -⟩ := h
    intro u hu hPr; have := h6 u hu; rw [hPr] at this; exact this
  have h5o : ∀ w L q, s.vlog w = some L → s.acc q w <+: L := by
    obtain ⟨-, -, -, -, h5, -⟩ := h; exact h5
  have h4o : ∀ w, s.vlog w = none → ∀ q, s.acc q w = [] := by
    obtain ⟨-, -, -, h4, -⟩ := h; exact h4
  have ereps : ∀ x, (stepAccept s r e).reps x =
      if x = r then { s.reps r with log := (s.reps r).log ++ [e] } else s.reps x := fun _ => rfl
  have eacc : ∀ x y, (stepAccept s r e).acc x y =
      if x = r ∧ y = (s.reps r).view then (s.reps r).log ++ [e] else s.acc x y := fun _ _ => rfl
  have evlog : (stepAccept s r e).vlog = s.vlog := rfl
  have evinit : (stepAccept s r e).vinit = s.vinit := rfl
  have elin : (stepAccept s r e).lin = s.lin := rfl
  have ereg : (stepAccept s r e).reg = s.reg := rfl
  have en : (stepAccept s r e).n = s.n := rfl
  generalize stepAccept s r e = s' at *
  have hreps : ∀ x, x ≠ r → s'.reps x = s.reps x := fun x hx => by rw [ereps, ite_f hx]
  have haccx : ∀ x w, x ≠ r → s'.acc x w = s.acc x w :=
    fun x w hx => by rw [eacc, ite_f (fun h => hx h.1)]
  have hrr : s'.reps r = { s.reps r with log := (s.reps r).log ++ [e] } := by rw [ereps, ite_t rfl]
  have haccr : ∀ w, w ≠ (s.reps r).view → s'.acc r w = s.acc r w :=
    fun w hw => by rw [eacc, ite_f (fun h => hw h.2)]
  have haccv : s'.acc r (s.reps r).view = (s.reps r).log ++ [e] := by rw [eacc, ite_t ⟨rfl, rfl⟩]
  have hle : Le s s' := by
    refine le_of_rep_step r evlog evinit elin ereg en hreps haccx (by rw [hrr]; exact Nat.le_refl _)
      ?_ ?_
    · intro w
      by_cases hw : w = (s.reps r).view
      · subst hw; rw [haccv, hacc]; exact List.prefix_append _ _
      · rw [haccr w hw]; exact List.prefix_refl _
    · intro w hw; exact .inl (haccr w (Ne.symm hw))
  refine ⟨inv_of_rep_step h r hle evlog evinit elin ereg hreps haccx ?_ ?_ ?_ ?_, hle⟩
  · unfold RepInv
    rw [hrr, en]
    dsimp only
    refine ⟨fun w hw => ?_, hle.registered hregl, fun _ => ⟨L, I, by rw [evlog]; exact hL,
      by rw [evinit]; exact hI, hsnoc, hIp.trans (List.prefix_append _ _), haccv,
      fun hp' => absurd hp' hp⟩, fun hs => by rw [hn] at hs; cases hs⟩
    rw [haccr w (by omega)]; exact r1 w hw
  · intro L0 w hL0
    by_cases hw : w = (s.reps r).view
    · subst hw; rw [hL] at hL0; cases hL0; rw [haccv]; exact hsnoc
    · rw [haccr w hw]; exact h5o w L0 r hL0
  · intro w hw
    by_cases hw' : w = (s.reps r).view
    · subst hw'; rw [hL] at hw; cases hw
    · rw [haccr w hw']; exact h4o w hw r
  · intro u hu hPr; rw [hrr]; exact h6o u hu hPr

/-- An op is executed for the first time anywhere: the linearized log grows by the `k`-th entry
of a committed log `l` (`k` its length plus one). Any replica executing op `k` performs this
step; when `lin` is already longer it is the identity. -/
def stepLin (s : Sys) (l : List Entry) (k : Nat) : Sys :=
  if s.lin.length < k then { s with lin := s.lin ++ (l.drop (k - 1)).take 1 } else s

theorem stepLin_inv (s : Sys) (l mine : List Entry) (k : Nat) (h : Inv s)
    (hc : Committed s l) (hk : k ≤ l.length) (hmine : mine <+: s.lin) (hml : mine <+: l)
    (hlen : mine.length + 1 = k) :
    Inv (stepLin s l k) ∧ Le s (stepLin s l k) ∧ l.take k <+: (stepLin s l k).lin := by
  have hcok := h.committed_ok hc
  have hlinc : Committed s s.lin := by obtain ⟨-, -, -, -, -, -, -, x, -⟩ := h; exact x
  have hml_len := hmine.length_le
  by_cases hg : s.lin.length < k
  · have hlm : mine = s.lin := hmine.eq_of_length (by omega)
    have hlinE : s.lin = l.take (k - 1) := by
      rw [← hlm]
      conv => lhs; rw [List.prefix_iff_eq_take.mp hml]
      congr 1; omega
    have htk : l.take k = s.lin ++ (l.drop (k - 1)).take 1 := by
      calc l.take k = l.take ((k - 1) + 1) := by congr 1; omega
        _ = l.take (k - 1) ++ (l.drop (k - 1)).take 1 := List.take_add ..
        _ = s.lin ++ (l.drop (k - 1)).take 1 := by rw [hlinE]
    have e : stepLin s l k = { s with lin := l.take k } := by
      simp only [stepLin, ite_t hg]; rw [htk]
    rw [e]
    have hcom' : Committed s (l.take k) := by
      obtain ⟨w, Q, hq, hQ⟩ := hc
      exact ⟨w, Q, hq, fun a ha => (List.take_prefix _ _).trans (hQ a ha)⟩
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, -, -, -, hin, hpos⟩ := h
    refine ⟨⟨h1, h2, h3, h4, h5, h6, h7, hcom', noDupReq_prefix (List.take_prefix _ _) hcok.1,
      registered_prefix (List.take_prefix _ _) hcok.2, hin, hpos⟩,
      ⟨fun _ => Nat.le_refl _, fun _ _ h => h, fun _ L h => ⟨L, h, List.prefix_refl _⟩,
        fun _ _ => List.prefix_refl _, fun _ _ _ => .inl rfl, ?_, fun _ _ _ h => h, rfl⟩,
      List.prefix_refl _⟩
    show s.lin <+: l.take k
    rw [htk]; exact List.prefix_append _ _
  · have e : stepLin s l k = s := by simp only [stepLin, ite_f hg]
    rw [e]
    refine ⟨h, Le.refl s, ?_⟩
    rcases h.comparable hc hlinc with h1 | h1
    · exact (List.take_prefix _ _).trans h1
    · exact take_prefix_of_le h1 (by omega)

/-- Replica `r` starts a view change to `v` (`initiateViewChange`). -/
def stepInitVC (s : Sys) (r v : Nat) : Sys :=
  let p := s.reps r
  s.setRep r ⟨v, .viewChange, p.log, if p.status = .viewChange then p.lnv else p.view⟩

theorem stepInitVC_inv (s : Sys) (r v : Nat) (h : Inv s) (hr : r < s.n)
    (hv : (s.reps r).view < v) :
    Inv (stepInitVC s r v) ∧ Le s (stepInitVC s r v) := by
  have hRr := h.rep hr
  obtain ⟨r1, r2, r3, r4⟩ := hRr
  have h6o : ∀ u, (s.vinit u).isSome → primary s.n u = r → u < (s.reps r).view ∨
      ((s.reps r).view = u ∧ (s.reps r).status ≠ .viewChange) := by
    obtain ⟨-, -, -, -, -, h6, -⟩ := h
    intro u hu hPr; have := h6 u hu; rw [hPr] at this; exact this
  have h5o : ∀ w L q, s.vlog w = some L → s.acc q w <+: L := by
    obtain ⟨-, -, -, -, h5, -⟩ := h; exact h5
  have h4o : ∀ w, s.vlog w = none → ∀ q, s.acc q w = [] := by
    obtain ⟨-, -, -, h4, -⟩ := h; exact h4
  have ereps : ∀ x, (stepInitVC s r v).reps x =
      if x = r then ⟨v, .viewChange, (s.reps r).log,
        if (s.reps r).status = .viewChange then (s.reps r).lnv else (s.reps r).view⟩
      else s.reps x := fun _ => rfl
  have eacc : (stepInitVC s r v).acc = s.acc := rfl
  have evlog : (stepInitVC s r v).vlog = s.vlog := rfl
  have evinit : (stepInitVC s r v).vinit = s.vinit := rfl
  have elin : (stepInitVC s r v).lin = s.lin := rfl
  have ereg : (stepInitVC s r v).reg = s.reg := rfl
  have en : (stepInitVC s r v).n = s.n := rfl
  generalize stepInitVC s r v = s' at *
  have hreps : ∀ x, x ≠ r → s'.reps x = s.reps x := fun x hx => by rw [ereps, ite_f hx]
  have haccx : ∀ x w, x ≠ r → s'.acc x w = s.acc x w := fun x w _ => by rw [eacc]
  have hrr := ereps r
  rw [ite_t rfl] at hrr
  have hle : Le s s' :=
    le_of_rep_step r evlog evinit elin ereg en hreps haccx (by rw [hrr]; exact Nat.le_of_lt hv)
      (fun w => by rw [eacc]; exact List.prefix_refl _) (fun w _ => .inl (by rw [eacc]))
  refine ⟨inv_of_rep_step h r hle evlog evinit elin ereg hreps haccx ?_ ?_ ?_ ?_, hle⟩
  · unfold RepInv
    rw [hrr, eacc, evlog, evinit]
    dsimp only
    refine ⟨fun w hw => r1 w (by omega), hle.registered r2, fun hs => ?_, fun _ => ?_⟩
    · rcases hs with hs | hs <;> cases hs
    · by_cases hst : (s.reps r).status = .viewChange
      · rw [ite_t hst]
        obtain ⟨hl, hnone, hacc, L, I, hL, hI, hpL, hIp⟩ := r4 hst
        refine ⟨by omega, fun w h1 h2 => ?_, hacc, L, I, hL, hI, hpL, hIp⟩
        by_cases hw : w ≤ (s.reps r).view
        · exact hnone w h1 hw
        · exact r1 w (by omega)
      · rw [ite_f hst]
        have hs' : (s.reps r).status = .normal ∨ (s.reps r).status = .stateTransfer := by
          cases h' : (s.reps r).status
          · exact .inl rfl
          · exact absurd h' hst
          · exact .inr rfl
        obtain ⟨L, I, hL, hI, hpL, hIp, hacc, -⟩ := r3 hs'
        exact ⟨hv, fun w h1 _ => r1 w h1, hacc, L, I, hL, hI, hpL, hIp⟩
  · intro L w hL; rw [eacc]; exact h5o w L r hL
  · intro w hw; rw [eacc]; exact h4o w hw r
  · intro u hu hPr
    rw [hrr]; left
    show u < v
    rcases h6o u hu hPr with h' | ⟨h', -⟩ <;> omega

/-- The new primary `r` starts view `v` with log `l` (`finalizeViewChange`). -/
def stepFinalize (s : Sys) (r v : Nat) (l : List Entry) : Sys :=
  let p := s.reps r
  ((({ s with vinit := fun x => if x = v then some l else s.vinit x }).setVlog v l).setRep r
    { p with view := v, status := .normal, log := l }).setAcc r v l

/-- The selection's spec: `l` is the log of one of the DoViewChanges, with the largest last
normal view and, among those, the largest length. -/
def IsBest (ds : List Dvc) (l : List Entry) : Prop :=
  ∃ d ∈ ds, d.log = l ∧ ∀ d' ∈ ds, d'.lnv < d.lnv ∨ (d'.lnv = d.lnv ∧ d'.log.length ≤ l.length)

/-- The view-change safety argument: what may be committed in a view `w < v` is a prefix of the
selected log. A member `x` of the DoViewChange quorum is in the possible-commit quorum, and its
view is past `w`, so it accepted `l'` in `w`. If `w` is below the best's last normal view, the
safety clause for that view's initial log closes it; if `w` is past `x`'s last normal view, `x`
accepted nothing in `w`; otherwise `w` is both last normal views and the best log is the longer
prefix of `w`'s log. -/
private theorem finalize_key (s : Sys) (v : Nat) (ds : List Dvc) (l : List Entry) (h : Inv s)
    (hds : ∀ d ∈ ds, d.view = v ∧ DvcValid s d)
    (hq : ∃ Q, Quorum s.n Q ∧ ∀ a ∈ Q, ∃ d ∈ ds, d.rid = a)
    (hbest : IsBest ds l) {w : Nat} (hw : w < v) {l' : List Entry}
    (hpc : PossCommitted s w l') : l' <+: l := by
  obtain ⟨dB, hdB, rfl, hball⟩ := hbest
  obtain ⟨-, -, -, -, -, ⟨LB, IB, hLB, hIB, hBL, hIBl⟩, -⟩ := (hds dB hdB).2
  have good : ∀ d ∈ ds, ∀ x, x = d.rid → (l' <+: s.acc x w ∨ (s.reps x).view ≤ w) →
      l' <+: s.acc d.rid w := by
    intro d hd x hx hor
    subst hx
    obtain ⟨hdv, -, -, hvle, -⟩ := hds d hd
    rcases hor with h' | h'
    · exact h'
    · omega
  have hx : ∃ d ∈ ds, l' <+: s.acc d.rid w := by
    obtain ⟨Q, hq1, hQ⟩ := hpc
    obtain ⟨Q', hq2, hQ'⟩ := hq
    obtain ⟨a, ha, ha'⟩ := quorum_meet hq1 hq2
    obtain ⟨d, hd, hda⟩ := hQ' a ha'
    exact ⟨d, hd, good d hd a hda.symm (hQ a ha)⟩
  obtain ⟨d, hd, hacc⟩ := hx
  obtain ⟨hdv, -, -, -, hnone, haccd, ⟨Ld, Id, hLd, -, hdLd, -⟩, -⟩ := hds d hd
  by_cases hwB : w < dB.lnv
  · exact (h.safety hIB hwB hpc).trans hIBl
  · have empty : d.lnv < w → l' <+: dB.log := by
      intro hlt
      rw [hnone w hlt (by omega)] at hacc
      rw [List.prefix_nil.mp hacc]; exact List.nil_prefix
    rcases hball d hd with hlt | ⟨heq, hlen⟩
    · exact empty (by omega)
    · by_cases hwd : w = d.lnv
      · subst hwd
        rw [heq, hLB] at hLd
        cases hLd
        exact hacc.trans (haccd.trans (List.prefix_of_prefix_length_le hdLd hBL hlen))
      · exact empty (by omega)

/-- The new primary of `v`, still in view change at a view up to `v`: `v` has not started. -/
private theorem finalize_vinit_none {s : Sys} {r v : Nat} (h : Inv s) (hp : primary s.n v = r)
    (hvc : (s.reps r).status = .viewChange) (hv : (s.reps r).view ≤ v) : s.vinit v = none := by
  obtain ⟨-, -, -, -, -, h6, -⟩ := h
  cases hI : s.vinit v with
  | none => rfl
  | some I =>
    have := h6 v (by rw [hI]; rfl)
    rw [hp] at this
    rcases this with h' | ⟨-, h'⟩
    · omega
    · exact absurd hvc h'

private theorem finalize_mine_aux (s : Sys) (r v : Nat) (ds : List Dvc) (l mine : List Entry)
    (h : Inv s) (hp : primary s.n v = r) (hvc : (s.reps r).status = .viewChange)
    (hv : (s.reps r).view ≤ v)
    (hds : ∀ d ∈ ds, d.view = v ∧ DvcValid s d)
    (hq : ∃ Q, Quorum s.n Q ∧ ∀ a ∈ Q, ∃ d ∈ ds, d.rid = a)
    (hbest : IsBest ds l) (hmine : CommittedBy s v mine) : mine <+: l := by
  obtain ⟨w, hw, hcin⟩ := hmine
  rcases Nat.lt_or_eq_of_le hw with hlt | heq
  · exact finalize_key s v ds l h hds hq hbest hlt (poss_of_in hcin)
  · subst heq
    have hnone := finalize_vinit_none h hp hvc hv
    obtain ⟨Q, hq', hQ⟩ := hcin
    obtain ⟨a, haQ⟩ := hq'.exists_mem
    have ha := hQ a haQ
    rcases h.acc_prefix a w with h0 | ⟨L, hL, -⟩
    · rw [h0] at ha; rw [List.prefix_nil.mp ha]; exact List.nil_prefix
    · obtain ⟨I, hI, -⟩ := h.vlog_ok hL; rw [hnone] at hI; cases hI

theorem stepFinalize_inv (s : Sys) (r v : Nat) (ds : List Dvc) (l : List Entry) (h : Inv s)
    (hr : r < s.n) (hp : primary s.n v = r) (hvc : (s.reps r).status = .viewChange)
    (hv : (s.reps r).view ≤ v)
    (hds : ∀ d ∈ ds, d.view = v ∧ DvcValid s d)
    (hq : ∃ Q, Quorum s.n Q ∧ ∀ a ∈ Q, ∃ d ∈ ds, d.rid = a)
    (hbest : IsBest ds l) :
    Inv (stepFinalize s r v l) ∧ Le s (stepFinalize s r v l) := by
  have hnone := finalize_vinit_none h hp hvc hv
  have hvl : s.vlog v = none := by
    obtain ⟨-, h2, -⟩ := h
    have := h2 v
    rw [hnone] at this
    cases hL : s.vlog v with
    | none => rfl
    | some _ => rw [hL] at this; simp at this
  have hacc0 : ∀ q, s.acc q v = [] := by obtain ⟨-, -, -, h4, -⟩ := h; exact h4 v hvl
  have hlok : NoDupReq l ∧ Registered s l := by
    obtain ⟨dB, hdB, rfl, -⟩ := hbest
    obtain ⟨-, -, -, -, -, ⟨LB, IB, hLB, -, hBL, -⟩, -⟩ := (hds dB hdB).2
    obtain ⟨_, _, _, hnd, hrg⟩ := h.vlog_ok hLB
    exact ⟨noDupReq_prefix hBL hnd, registered_prefix hBL hrg⟩
  have hkey := fun w (hw : w < v) l' (hpc : PossCommitted s w l') =>
    finalize_key s v ds l h hds hq hbest hw hpc
  have hRr := h.rep hr
  have ereps : ∀ x, (stepFinalize s r v l).reps x =
      if x = r then { s.reps r with view := v, status := .normal, log := l } else s.reps x :=
    fun _ => rfl
  have evlog : ∀ x, (stepFinalize s r v l).vlog x = if x = v then some l else s.vlog x :=
    fun _ => rfl
  have evinit : ∀ x, (stepFinalize s r v l).vinit x = if x = v then some l else s.vinit x :=
    fun _ => rfl
  have eacc : ∀ x y, (stepFinalize s r v l).acc x y = if x = r ∧ y = v then l else s.acc x y :=
    fun _ _ => rfl
  have elin : (stepFinalize s r v l).lin = s.lin := rfl
  have ereg : (stepFinalize s r v l).reg = s.reg := rfl
  have en : (stepFinalize s r v l).n = s.n := rfl
  generalize stepFinalize s r v l = s' at *
  have hvi : ∀ w I, s.vinit w = some I → s'.vinit w = some I := by
    intro w I hI; rw [evinit]
    by_cases hw : w = v
    · subst hw; rw [hnone] at hI; cases hI
    · rw [ite_f hw]; exact hI
  have hle : Le s s' := by
    refine ⟨?_, hvi, ?_, ?_, ?_, ?_, ?_, en⟩
    · intro x; rw [ereps]
      by_cases hx : x = r
      · subst hx; rw [ite_t rfl]; exact hv
      · rw [ite_f hx]; exact Nat.le_refl _
    · intro w L hL; rw [evlog]
      by_cases hw : w = v
      · subst hw; rw [hvl] at hL; cases hL
      · rw [ite_f hw]; exact ⟨L, hL, List.prefix_refl _⟩
    · intro x y; rw [eacc]
      by_cases hxy : x = r ∧ y = v
      · rw [ite_t hxy, hxy.2, hacc0]; exact List.nil_prefix
      · rw [ite_f hxy]; exact List.prefix_refl _
    · intro x w hxw; rw [eacc]
      by_cases hxy : x = r ∧ w = v
      · obtain ⟨rfl, rfl⟩ := hxy; right; omega
      · rw [ite_f hxy]; left; rfl
    · rw [elin]; exact List.prefix_refl _
    · intro c n i hi; rw [ereg]; exact hi
  refine ⟨?_, hle⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, hlin, hnd, hreg, hin, hpos⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [en]; exact hpos⟩
  · intro q hq
    rw [en] at hq
    by_cases hqr : q = r
    · subst hqr
      unfold RepInv
      rw [ereps, ite_t rfl, en]
      dsimp only
      refine ⟨fun w hw => ?_, hle.registered hlok.2,
        fun _ => ⟨l, l, ?_, ?_, List.prefix_refl _, List.prefix_refl _, ?_, fun _ => rfl⟩,
        fun hs => by cases hs⟩
      · rw [eacc, ite_f (fun h => by omega)]; exact hRr.1 w (by omega)
      · rw [evlog, ite_t rfl]
      · rw [evinit, ite_t rfl]
      · rw [eacc, ite_t ⟨rfl, rfl⟩]
    · refine repInv_frame (h1 q hq) en (by rw [ereps, ite_f hqr])
        (fun w => by rw [eacc, ite_f (fun h => hqr h.1)]) ?_ hvi hle.registered
      intro w L hL; rw [evlog]
      by_cases hw : w = v
      · subst hw; rw [hvl] at hL; cases hL
      · rw [ite_f hw]; exact ⟨L, hL, List.prefix_refl _, fun _ => rfl⟩
  · intro w; rw [evinit, evlog]
    by_cases hw : w = v
    · rw [ite_t hw, ite_t hw]
    · rw [ite_f hw, ite_f hw]; exact h2 w
  · intro w I L hI hL
    rw [evinit] at hI; rw [evlog] at hL
    by_cases hw : w = v
    · rw [ite_t hw] at hI hL; cases hI; cases hL
      exact ⟨List.prefix_refl _, hlok.1, hle.registered hlok.2⟩
    · rw [ite_f hw] at hI hL
      obtain ⟨a, b, c⟩ := h3 w I L hI hL
      exact ⟨a, b, hle.registered c⟩
  · intro w hw q
    rw [evlog] at hw; rw [eacc]
    by_cases hwv : w = v
    · rw [ite_t hwv] at hw; cases hw
    · rw [ite_f hwv] at hw; rw [ite_f (fun h => hwv h.2)]; exact h4 w hw q
  · intro w L q hL
    rw [evlog] at hL; rw [eacc]
    by_cases hwv : w = v
    · subst hwv; rw [ite_t rfl] at hL; cases hL
      by_cases hqr : q = r
      · rw [ite_t ⟨hqr, rfl⟩]; exact List.prefix_refl _
      · rw [ite_f (fun h => hqr h.1), hacc0]; exact List.nil_prefix
    · rw [ite_f hwv] at hL; rw [ite_f (fun h => hwv h.2)]; exact h5 w L q hL
  · intro u hu
    rw [evinit] at hu; rw [en, ereps]
    by_cases huv : u = v
    · subst huv; rw [hp, ite_t rfl]; right; exact ⟨rfl, by simp⟩
    · rw [ite_f huv] at hu
      have := h6 u hu
      by_cases hPr : primary s.n u = r
      · rw [ite_t hPr]; rw [hPr] at this
        rcases this with h' | ⟨-, h'⟩
        · left; show u < v; omega
        · exact absurd hvc h'
      · rw [ite_f hPr]; exact this
  · intro u w l' I hI hw hpc
    rw [evinit] at hI
    have hpc0 := hle.poss_back hpc
    by_cases huv : u = v
    · rw [ite_t huv] at hI; cases hI; subst huv; exact hkey w hw l' hpc0
    · rw [ite_f huv] at hI; exact h7 u w l' I hI hw hpc0
  · rw [elin]; exact hle.committed hlin
  · rw [elin]; exact hnd
  · rw [elin]; exact hle.registered hreg
  · intro c n i hi; rw [ereg] at hi; exact hin c n i hi

/-- A backup `r` installs view `v`'s initial log (`onStartView`). -/
def stepStartView (s : Sys) (r v : Nat) (l : List Entry) : Sys :=
  let p := s.reps r
  (s.setRep r { p with view := v, status := .normal, log := l }).setAcc r v l

theorem stepStartView_inv (s : Sys) (r v : Nat) (l : List Entry) (h : Inv s) (hr : r < s.n)
    (hinit : s.vinit v = some l)
    (hv : (s.reps r).view < v ∨ ((s.reps r).view = v ∧ (s.reps r).status = .viewChange)) :
    Inv (stepStartView s r v l) ∧ Le s (stepStartView s r v l) := by
  have hRr := h.rep hr
  obtain ⟨r1, r2, r3, r4⟩ := hRr
  obtain ⟨Lv, hLv, hlLv, -, hregLv⟩ := h.vinit_ok hinit
  have h6o : ∀ u, (s.vinit u).isSome → primary s.n u = r → u < (s.reps r).view ∨
      ((s.reps r).view = u ∧ (s.reps r).status ≠ .viewChange) := by
    obtain ⟨-, -, -, -, -, h6, -⟩ := h
    intro u hu hPr; have := h6 u hu; rw [hPr] at this; exact this
  have h5o : ∀ w L q, s.vlog w = some L → s.acc q w <+: L := by
    obtain ⟨-, -, -, -, h5, -⟩ := h; exact h5
  have h4o : ∀ w, s.vlog w = none → ∀ q, s.acc q w = [] := by
    obtain ⟨-, -, -, h4, -⟩ := h; exact h4
  have hnp : primary s.n v ≠ r := by
    intro hPr
    rcases h6o v (by rw [hinit]; rfl) hPr with h' | ⟨h', h''⟩
    · omega
    · rcases hv with hv | ⟨-, hv⟩
      · omega
      · exact h'' hv
  have hacc0 : s.acc r v = [] := by
    rcases hv with hv | ⟨hv, hvc⟩
    · exact r1 v hv
    · obtain ⟨hl, hnone, -⟩ := r4 hvc
      exact hnone v (by omega) (by omega)
  have ereps : ∀ x, (stepStartView s r v l).reps x =
      if x = r then { s.reps r with view := v, status := .normal, log := l } else s.reps x :=
    fun _ => rfl
  have eacc : ∀ x y, (stepStartView s r v l).acc x y =
      if x = r ∧ y = v then l else s.acc x y := fun _ _ => rfl
  have evlog : (stepStartView s r v l).vlog = s.vlog := rfl
  have evinit : (stepStartView s r v l).vinit = s.vinit := rfl
  have elin : (stepStartView s r v l).lin = s.lin := rfl
  have ereg : (stepStartView s r v l).reg = s.reg := rfl
  have en : (stepStartView s r v l).n = s.n := rfl
  generalize stepStartView s r v l = s' at *
  have hreps : ∀ x, x ≠ r → s'.reps x = s.reps x := fun x hx => by rw [ereps, ite_f hx]
  have haccx : ∀ x w, x ≠ r → s'.acc x w = s.acc x w :=
    fun x w hx => by rw [eacc, ite_f (fun h => hx h.1)]
  have hrr : s'.reps r = { s.reps r with view := v, status := .normal, log := l } := by
    rw [ereps, ite_t rfl]
  have haccr : ∀ w, w ≠ v → s'.acc r w = s.acc r w :=
    fun w hw => by rw [eacc, ite_f (fun h => hw h.2)]
  have haccv : s'.acc r v = l := by rw [eacc, ite_t ⟨rfl, rfl⟩]
  have hvle : (s.reps r).view ≤ v := by rcases hv with hv | ⟨hv, -⟩ <;> omega
  have hle : Le s s' := by
    refine le_of_rep_step r evlog evinit elin ereg en hreps haccx (by rw [hrr]; exact hvle) ?_ ?_
    · intro w
      by_cases hw : w = v
      · subst hw; rw [haccv, hacc0]; exact List.nil_prefix
      · rw [haccr w hw]; exact List.prefix_refl _
    · intro w hw
      by_cases hwv : w = v
      · subst hwv; right; omega
      · exact .inl (haccr w hwv)
  refine ⟨inv_of_rep_step h r hle evlog evinit elin ereg hreps haccx ?_ ?_ ?_ ?_, hle⟩
  · unfold RepInv
    rw [hrr, en]
    dsimp only
    refine ⟨fun w hw => ?_, hle.registered (registered_prefix hlLv hregLv),
      fun _ => ⟨Lv, l, by rw [evlog]; exact hLv, by rw [evinit]; exact hinit, hlLv,
        List.prefix_refl _, haccv, fun hp' => absurd hp' hnp⟩, fun hs => by cases hs⟩
    rw [haccr w (by omega)]; exact r1 w (by omega)
  · intro L0 w hL0
    by_cases hw : w = v
    · subst hw; rw [hLv] at hL0; cases hL0; rw [haccv]; exact hlLv
    · rw [haccr w hw]; exact h5o w L0 r hL0
  · intro w hw
    by_cases hw' : w = v
    · subst hw'; rw [hLv] at hw; cases hw
    · rw [haccr w hw']; exact h4o w hw r
  · intro u hu hPr
    rw [hrr]
    rcases h6o u hu hPr with h' | ⟨h', h''⟩
    · left; show u < v; omega
    · rcases hv with hv | ⟨-, hv⟩
      · left; show u < v; omega
      · exact absurd hv h''

/-- Replica `r` enters state transfer, keeping its view and log (`initiateStateTransfer`). -/
def stepEnterST (s : Sys) (r : Nat) : Sys :=
  s.setRep r { s.reps r with status := .stateTransfer }

theorem stepEnterST_inv (s : Sys) (r : Nat) (h : Inv s) (hr : r < s.n)
    (hs : (s.reps r).status ≠ .viewChange) :
    Inv (stepEnterST s r) ∧ Le s (stepEnterST s r) := by
  have hRr := h.rep hr
  obtain ⟨r1, r2, r3, r4⟩ := hRr
  have h6o : ∀ u, (s.vinit u).isSome → primary s.n u = r → u < (s.reps r).view ∨
      ((s.reps r).view = u ∧ (s.reps r).status ≠ .viewChange) := by
    obtain ⟨-, -, -, -, -, h6, -⟩ := h
    intro u hu hPr; have := h6 u hu; rw [hPr] at this; exact this
  have h5o : ∀ w L q, s.vlog w = some L → s.acc q w <+: L := by
    obtain ⟨-, -, -, -, h5, -⟩ := h; exact h5
  have h4o : ∀ w, s.vlog w = none → ∀ q, s.acc q w = [] := by
    obtain ⟨-, -, -, h4, -⟩ := h; exact h4
  have hs' : (s.reps r).status = .normal ∨ (s.reps r).status = .stateTransfer := by
    cases h' : (s.reps r).status
    · exact .inl rfl
    · exact absurd h' hs
    · exact .inr rfl
  have ereps : ∀ x, (stepEnterST s r).reps x =
      if x = r then { s.reps r with status := .stateTransfer } else s.reps x := fun _ => rfl
  have eacc : (stepEnterST s r).acc = s.acc := rfl
  have evlog : (stepEnterST s r).vlog = s.vlog := rfl
  have evinit : (stepEnterST s r).vinit = s.vinit := rfl
  have elin : (stepEnterST s r).lin = s.lin := rfl
  have ereg : (stepEnterST s r).reg = s.reg := rfl
  have en : (stepEnterST s r).n = s.n := rfl
  generalize stepEnterST s r = s' at *
  have hreps : ∀ x, x ≠ r → s'.reps x = s.reps x := fun x hx => by rw [ereps, ite_f hx]
  have haccx : ∀ x w, x ≠ r → s'.acc x w = s.acc x w := fun x w _ => by rw [eacc]
  have hrr := ereps r
  rw [ite_t rfl] at hrr
  have hle : Le s s' :=
    le_of_rep_step r evlog evinit elin ereg en hreps haccx (by rw [hrr]; exact Nat.le_refl _)
      (fun w => by rw [eacc]; exact List.prefix_refl _) (fun w _ => .inl (by rw [eacc]))
  refine ⟨inv_of_rep_step h r hle evlog evinit elin ereg hreps haccx ?_ ?_ ?_ ?_, hle⟩
  · unfold RepInv
    rw [hrr, eacc, evlog, evinit]
    dsimp only
    rw [en]
    exact ⟨r1, hle.registered r2, fun _ => r3 hs', fun hs'' => by cases hs''⟩
  · intro L w hL; rw [eacc]; exact h5o w L r hL
  · intro w hw; rw [eacc]; exact h4o w hw r
  · intro u hu hPr
    rw [hrr]
    rcases h6o u hu hPr with h' | ⟨h', -⟩
    · exact .inl h'
    · exact .inr ⟨h', by simp⟩

/-- Replica `r` in state transfer appends a NewState's logs (`onNewState`) and is normal again. -/
def stepNewState (s : Sys) (r : Nat) (logs : List Entry) : Sys :=
  let p := s.reps r
  let l := p.log ++ logs
  (s.setRep r { p with status := .normal, log := l }).setAcc r p.view l

theorem stepNewState_inv (s : Sys) (r : Nat) (logs : List Entry) (c k rid : Nat) (h : Inv s)
    (hr : r < s.n) (hst : (s.reps r).status = .stateTransfer)
    (hm : MsgValid s (.newState (s.reps r).view logs c k rid))
    (hk : k = (s.reps r).log.length + logs.length) :
    Inv (stepNewState s r logs) ∧ Le s (stepNewState s r logs) := by
  have hRr := h.rep hr
  obtain ⟨r1, r2, r3, -⟩ := hRr
  obtain ⟨L, I, hL, hI, hpL, hIp, hacc, hprim⟩ := r3 (.inr hst)
  obtain ⟨L', hL', hkL, hlen, hlogs⟩ := hm
  rw [hL] at hL'; cases hL'
  have hnew : (s.reps r).log ++ logs = L.take k := by
    have hPk : (s.reps r).log.length ≤ k := by omega
    have hPL : (s.reps r).log = (L.take k).take (s.reps r).log.length := by
      rw [List.take_take, Nat.min_eq_left hPk]; exact List.prefix_iff_eq_take.mp hpL
    have hd : k - logs.length = (s.reps r).log.length := by omega
    rw [hd] at hlogs
    rw [hlogs]
    calc (s.reps r).log ++ List.drop (s.reps r).log.length (L.take k)
        = (L.take k).take (s.reps r).log.length ++ (L.take k).drop (s.reps r).log.length := by
          rw [← hPL]
      _ = L.take k := List.take_append_drop _ _
  have hsub : (s.reps r).log ++ logs <+: L := by rw [hnew]; exact List.take_prefix _ _
  obtain ⟨_, _, _, _, hregL⟩ := h.vlog_ok hL
  have hregl : Registered s ((s.reps r).log ++ logs) := registered_prefix hsub hregL
  have h6o : ∀ u, (s.vinit u).isSome → primary s.n u = r → u < (s.reps r).view ∨
      ((s.reps r).view = u ∧ (s.reps r).status ≠ .viewChange) := by
    obtain ⟨-, -, -, -, -, h6, -⟩ := h
    intro u hu hPr; have := h6 u hu; rw [hPr] at this; exact this
  have h5o : ∀ w L q, s.vlog w = some L → s.acc q w <+: L := by
    obtain ⟨-, -, -, -, h5, -⟩ := h; exact h5
  have h4o : ∀ w, s.vlog w = none → ∀ q, s.acc q w = [] := by
    obtain ⟨-, -, -, h4, -⟩ := h; exact h4
  have ereps : ∀ x, (stepNewState s r logs).reps x =
      if x = r then { s.reps r with status := .normal, log := (s.reps r).log ++ logs }
      else s.reps x := fun _ => rfl
  have eacc : ∀ x y, (stepNewState s r logs).acc x y =
      if x = r ∧ y = (s.reps r).view then (s.reps r).log ++ logs else s.acc x y := fun _ _ => rfl
  have evlog : (stepNewState s r logs).vlog = s.vlog := rfl
  have evinit : (stepNewState s r logs).vinit = s.vinit := rfl
  have elin : (stepNewState s r logs).lin = s.lin := rfl
  have ereg : (stepNewState s r logs).reg = s.reg := rfl
  have en : (stepNewState s r logs).n = s.n := rfl
  generalize stepNewState s r logs = s' at *
  have hreps : ∀ x, x ≠ r → s'.reps x = s.reps x := fun x hx => by rw [ereps, ite_f hx]
  have haccx : ∀ x w, x ≠ r → s'.acc x w = s.acc x w :=
    fun x w hx => by rw [eacc, ite_f (fun h => hx h.1)]
  have hrr : s'.reps r = { s.reps r with status := .normal, log := (s.reps r).log ++ logs } := by
    rw [ereps, ite_t rfl]
  have haccr : ∀ w, w ≠ (s.reps r).view → s'.acc r w = s.acc r w :=
    fun w hw => by rw [eacc, ite_f (fun h => hw h.2)]
  have haccv : s'.acc r (s.reps r).view = (s.reps r).log ++ logs := by
    rw [eacc, ite_t ⟨rfl, rfl⟩]
  have hle : Le s s' := by
    refine le_of_rep_step r evlog evinit elin ereg en hreps haccx (by rw [hrr]; exact Nat.le_refl _)
      ?_ ?_
    · intro w
      by_cases hw : w = (s.reps r).view
      · subst hw; rw [haccv, hacc]; exact List.prefix_append _ _
      · rw [haccr w hw]; exact List.prefix_refl _
    · intro w hw; exact .inl (haccr w (Ne.symm hw))
  refine ⟨inv_of_rep_step h r hle evlog evinit elin ereg hreps haccx ?_ ?_ ?_ ?_, hle⟩
  · unfold RepInv
    rw [hrr, en]
    dsimp only
    refine ⟨fun w hw => ?_, hle.registered hregl, fun _ => ⟨L, I, by rw [evlog]; exact hL,
      by rw [evinit]; exact hI, hsub, hIp.trans (List.prefix_append _ _), haccv,
      fun hp' => ?_⟩, fun hs => by cases hs⟩
    · rw [haccr w (by omega)]; exact r1 w hw
    · have hPL := hprim hp'
      rw [hnew]
      apply List.take_of_length_le
      have : (s.reps r).log.length = L.length := by rw [hPL]
      omega
  · intro L0 w hL0
    by_cases hw : w = (s.reps r).view
    · subst hw; rw [hL] at hL0; cases hL0; rw [haccv]; exact hsub
    · rw [haccr w hw]; exact h5o w L0 r hL0
  · intro w hw
    by_cases hw' : w = (s.reps r).view
    · subst hw'; rw [hL] at hw; cases hw
    · rw [haccr w hw']; exact h4o w hw r
  · intro u hu hPr
    rw [hrr]
    rcases h6o u hu hPr with h' | ⟨h', -⟩
    · exact .inl h'
    · exact .inr ⟨h', by simp⟩

/-! ## What the replicas and clients learn from the invariant -/

/-- Two committed logs are prefixes of one another. -/
theorem committed_comparable (s : Sys) (h : Inv s) (l1 l2 : List Entry)
    (h1 : Committed s l1) (h2 : Committed s l2) : l1 <+: l2 ∨ l2 <+: l1 := by
  exact h.comparable h1 h2

/-- A prefix of a committed log is committed. -/
theorem committed_prefix (s : Sys) (l1 l2 : List Entry) (h : l1 <+: l2)
    (h2 : Committed s l2) : Committed s l1 := by
  obtain ⟨w, Q, hq, hQ⟩ := h2
  exact ⟨w, Q, hq, fun a ha => h.trans (hQ a ha)⟩

/-- The primary's commit: a quorum's PrepareOKs for op `k` of view `v` commit the view's log up
to `k` (`onPrepareOK`). -/
theorem committed_of_prepareOKs (s : Sys) (h : Inv s) (v k : Nat) (Q : List Nat) (L : List Entry)
    (hL : s.vlog v = some L) (hk : k ≤ L.length) (hq : Quorum s.n Q)
    (hQ : ∀ a ∈ Q, MsgValid s (.prepareOK v k a)) :
    CommittedIn s v (L.take k) := by
  obtain ⟨-, -, -, -, h5, -⟩ := h
  exact ⟨Q, hq, fun a ha => take_prefix_of_le (h5 v L a hL) (hQ a ha).2⟩

/-- What is committed in a view is committed by any later one. -/
theorem committedBy_of_in (s : Sys) (v w : Nat) (l : List Entry) (hw : w ≤ v)
    (h : CommittedIn s w l) : CommittedBy s v l := ⟨w, hw, h⟩

/-- What is committed by a view is committed. -/
theorem committed_of_by (s : Sys) (v : Nat) (l : List Entry) (h : CommittedBy s v l) :
    Committed s l := by obtain ⟨w, _, hw⟩ := h; exact ⟨w, hw⟩

/-- A prefix of what is committed by a view is committed by it. -/
theorem committedBy_prefix (s : Sys) (v : Nat) (l1 l2 : List Entry) (h : l1 <+: l2)
    (h2 : CommittedBy s v l2) : CommittedBy s v l1 := by
  obtain ⟨w, hw, Q, hq, hQ⟩ := h2
  exact ⟨w, hw, Q, hq, fun a ha => h.trans (hQ a ha)⟩

/-- A replica's own acceptance: a replica normal (or in state transfer) in its view has accepted
its log there (its PrepareOKs are valid). -/
theorem prepareOK_own (s : Sys) (h : Inv s) (r k : Nat) (hr : r < s.n)
    (hn : (s.reps r).status = .normal ∨ (s.reps r).status = .stateTransfer)
    (hk : k ≤ (s.reps r).log.length) :
    MsgValid s (.prepareOK (s.reps r).view k r) := by
  obtain ⟨-, -, r3, -⟩ := h.rep hr
  obtain ⟨L, I, -, -, -, -, hacc, -⟩ := r3 hn
  exact ⟨hr, by rw [hacc]; exact hk⟩

/-- A replica in a view change may send its DoViewChange. -/
theorem dvc_own (s : Sys) (h : Inv s) (r c : Nat) (hr : r < s.n)
    (hvc : (s.reps r).status = .viewChange) (hc : c ≤ (s.reps r).log.length)
    (hcom : CommittedBy s (s.reps r).view ((s.reps r).log.take c)) :
    DvcValid s ⟨(s.reps r).view, (s.reps r).log, (s.reps r).lnv, c, r⟩ := by
  obtain ⟨-, -, -, r4⟩ := h.rep hr
  obtain ⟨hl, hnone, hacc, L, I, hL, hI, hpL, hIp⟩ := r4 hvc
  exact ⟨hr, hl, Nat.le_refl _, fun w h1 h2 => hnone w h1 (Nat.le_of_lt h2),
    by rw [hacc]; exact List.prefix_refl _, ⟨L, I, hL, hI, hpL, hIp⟩, hc, hcom⟩

/-- After the view change, each DoViewChange's commit number is committed in the selected log
(the new primary's commit number, `finalizeViewChange`). The new primary `r` of `v` is still in
view change at a view up to `v` (so `v` has not started: nothing is committed in `v` yet). -/
theorem finalize_committed (s : Sys) (r v : Nat) (ds : List Dvc) (l : List Entry) (h : Inv s)
    (hr : r < s.n) (hp : primary s.n v = r) (hvc : (s.reps r).status = .viewChange)
    (hv : (s.reps r).view ≤ v)
    (hds : ∀ d ∈ ds, d.view = v ∧ DvcValid s d)
    (hq : ∃ Q, Quorum s.n Q ∧ ∀ a ∈ Q, ∃ d ∈ ds, d.rid = a)
    (hbest : IsBest ds l) (d : Dvc) (hd : d ∈ ds) :
    d.commit ≤ l.length ∧ CommittedBy s v (l.take d.commit) := by
  obtain ⟨hdv, hval⟩ := hds d hd
  obtain ⟨-, -, -, -, -, -, hc, hcom⟩ := hval
  have hpre : d.log.take d.commit <+: l :=
    finalize_mine_aux s r v ds l _ h hp hvc hv hds hq hbest (by rw [← hdv]; exact hcom)
  have heq := List.prefix_iff_eq_take.mp hpre
  rw [List.length_take, Nat.min_eq_left hc] at heq
  have hlen := hpre.length_le
  rw [List.length_take, Nat.min_eq_left hc] at hlen
  refine ⟨hlen, ?_⟩
  rw [← heq, ← hdv]; exact hcom

/-- The new primary's log extends what it has executed (committed by its view, at most `v`):
`finalizeViewChange` executes the rest up to its commit number. -/
theorem finalize_mine (s : Sys) (r v : Nat) (ds : List Dvc) (l mine : List Entry) (h : Inv s)
    (hr : r < s.n) (hp : primary s.n v = r) (hvc : (s.reps r).status = .viewChange)
    (hv : (s.reps r).view ≤ v)
    (hds : ∀ d ∈ ds, d.view = v ∧ DvcValid s d)
    (hq : ∃ Q, Quorum s.n Q ∧ ∀ a ∈ Q, ∃ d ∈ ds, d.rid = a)
    (hbest : IsBest ds l) (hmine : CommittedBy s v mine) : mine <+: l := by
  exact finalize_mine_aux s r v ds l mine h hp hvc hv hds hq hbest hmine

/-- A replica installing view `v`'s initial log (`onStartView`): what it executed is a prefix of
it. What it executed is committed by a view `u < v`: its last normal view (`lnv`) if it is in
view change, its view (then `< v`) if it is normal or in state transfer (it executes only while
normal, and a replica in view change at `v` was last normal before `v`). -/
theorem startView_mine (s : Sys) (v u : Nat) (l mine : List Entry) (h : Inv s)
    (hinit : s.vinit v = some l) (hu : u < v)
    (hmine : CommittedBy s u mine) : mine <+: l := by
  obtain ⟨w, hw, hcin⟩ := hmine
  exact h.safety hinit (by omega) (poss_of_in hcin)

/-- The primary's Prepare for its last entry. -/
theorem prepare_own (s : Sys) (h : Inv s) (r c : Nat) (e : Entry) (hr : r < s.n)
    (hn : (s.reps r).status = .normal) (hp : primary s.n (s.reps r).view = r)
    (hlast : (s.reps r).log.getLast? = some e)
    (hc : c ≤ (s.reps r).log.length)
    (hcom : CommittedBy s (s.reps r).view ((s.reps r).log.take c)) :
    MsgValid s (.prepare (s.reps r).view (s.reps r).log.length c e r) := by
  obtain ⟨-, -, r3, -⟩ := h.rep hr
  obtain ⟨L, I, hL, -, -, -, -, hprim⟩ := r3 (.inl hn)
  have hlog := hprim hp
  have hne : (s.reps r).log ≠ [] := by intro h0; rw [h0] at hlast; simp at hlast
  refine ⟨L, hL, List.length_pos_iff.mpr hne, ?_, ?_, ?_⟩
  · rw [← hlog, ← List.getLast?_eq_getElem?]; exact hlast
  · rw [← hlog]; exact hc
  · rw [← hlog]; exact hcom

/-- A replica normal in its view (or in state transfer) may send a Commit up to a committed
prefix of its log (the primary's commits; the internal Commit of a Prepare is the Prepare's). -/
theorem commit_own (s : Sys) (h : Inv s) (r c : Nat) (hr : r < s.n)
    (hn : (s.reps r).status = .normal ∨ (s.reps r).status = .stateTransfer)
    (hc : c ≤ (s.reps r).log.length)
    (hcom : CommittedBy s (s.reps r).view ((s.reps r).log.take c)) :
    MsgValid s (.commit (s.reps r).view c r) := by
  obtain ⟨-, -, r3, -⟩ := h.rep hr
  obtain ⟨L, I, hL, -, hpL, -⟩ := r3 hn
  exact ⟨L, hL, Nat.le_trans hc hpL.length_le, by rw [take_eq_of_prefix hpL hc]; exact hcom⟩

/-- A Prepare's commit number makes a valid Commit. -/
theorem commit_of_prepare (s : Sys) (v k c rid rid' : Nat) (e : Entry)
    (hm : MsgValid s (.prepare v k c e rid)) : MsgValid s (.commit v c rid') := by
  obtain ⟨L, hL, -, -, hc, hcom⟩ := hm
  exact ⟨L, hL, hc, hcom⟩

/-- A replica normal in its view answers a GetState with its log after `k`. -/
theorem newState_own (s : Sys) (h : Inv s) (r k c : Nat) (hr : r < s.n)
    (hn : (s.reps r).status = .normal) (hk : k ≤ (s.reps r).log.length) :
    MsgValid s (.newState (s.reps r).view ((s.reps r).log.drop k) c (s.reps r).log.length r) :=
  by
  obtain ⟨-, -, r3, -⟩ := h.rep hr
  obtain ⟨L, I, hL, -, hpL, -⟩ := r3 (.inl hn)
  refine ⟨L, hL, hpL.length_le, by simp, ?_⟩
  rw [← List.prefix_iff_eq_take.mp hpL, List.length_drop]
  congr 1; omega

/-- A replica's log up to a valid Commit's number, when it is in the Commit's view and has that
many entries, is committed (`onCommit`). -/
theorem committed_of_commit (s : Sys) (h : Inv s) (r c rid : Nat) (hr : r < s.n)
    (hn : (s.reps r).status = .normal)
    (hm : MsgValid s (.commit (s.reps r).view c rid)) (hc : c ≤ (s.reps r).log.length) :
    CommittedBy s (s.reps r).view ((s.reps r).log.take c) := by
  obtain ⟨L, hL, -, hcom⟩ := hm
  obtain ⟨-, -, r3, -⟩ := h.rep hr
  obtain ⟨L', I, hL', -, hpL, -⟩ := r3 (.inl hn)
  rw [hL] at hL'; cases hL'
  rw [← take_eq_of_prefix hpL hc]; exact hcom

/-- A StartView's commit number is committed in its log. -/
theorem committed_of_startView (s : Sys) (v k c rid : Nat) (logs : List Entry)
    (hm : MsgValid s (.startView v k c logs rid)) : CommittedBy s v (logs.take c) := by
  exact hm.2.2.2

/-- A replica's log's entries are registered. -/
theorem registered_of_inv (s : Sys) (h : Inv s) (r : Nat) (hr : r < s.n) :
    Registered s (s.reps r).log := by
  exact (h.rep hr).2.1

/-- Every string of a valid message is plain: operations are `encOp` of registered (`InputOk`)
inputs, results are registered put values or `""`. -/
private theorem foldl_plain (s : Sys) (h : Inv s) :
    ∀ (l : List Entry) (m : Store), Registered s l → (∀ k v, m k = some v → PlainStr v) →
      ∀ k v, (l.foldl (fun m e => (handle m e.op).1) m) k = some v → PlainStr v := by
  intro l
  induction l with
  | nil => intro m _ hm; exact hm
  | cons e l ih =>
    intro m hl hm
    apply ih _ (fun e' he' => hl e' (List.mem_cons_of_mem _ he'))
    obtain ⟨i, hi, hop⟩ := hl e List.mem_cons_self
    have hiok := h.inputOk hi
    show ∀ k v, (handle m e.op).1 k = some v → PlainStr v
    rw [hop, handle_ok _ hiok]
    cases i with
    | get k => exact hm
    | put k v =>
      intro k' v' hk'
      simp only [svcStep] at hk'
      split at hk'
      · cases hk'; exact hiok.2.2.2
      · exact hm k' v' hk'

private theorem outOf_plain (s : Sys) (h : Inv s) (i : Nat) : PlainStr (outOf s.lin i) := by
  have hlinreg : Registered s s.lin := by
    obtain ⟨-, -, -, -, -, -, -, -, -, x, -⟩ := h; exact x
  unfold outOf
  cases he : s.lin[i]? with
  | none => intro c hc; cases hc
  | some e =>
    dsimp only
    obtain ⟨i', hi', hop⟩ := hlinreg e (List.mem_of_getElem? he)
    have hiok := h.inputOk hi'
    rw [hop, handle_ok _ hiok]
    have hst := foldl_plain s h (s.lin.take i) (fun _ => none)
      (registered_prefix (List.take_prefix _ _) hlinreg) (fun _ _ h => by cases h)
    cases i' with
    | put k v => exact hiok.2.2.2
    | get k =>
      simp only [svcStep]
      cases hk : storeOf (s.lin.take i) k with
      | none => intro c hc; cases hc
      | some v => exact hst k v hk

theorem msgValid_plain (s : Sys) (h : Inv s) (m : Msg) (hm : MsgValid s m) : PlainMsg m := by
  have hvl : ∀ v L, s.vlog v = some L → ∀ e ∈ L, PlainStr e.op := by
    intro v L hL e he
    obtain ⟨_, _, _, _, hreg⟩ := h.vlog_ok hL
    obtain ⟨i, hi, hop⟩ := hreg e he
    rw [hop]; exact encOp_plain i (h.inputOk hi)
  cases m with
  | request id cid op =>
    obtain ⟨i, hi, rfl⟩ := hm; exact encOp_plain i (h.inputOk hi)
  | reply id cid v res =>
    obtain ⟨i, e, -, -, -, rfl⟩ := hm; exact outOf_plain s h i
  | prepare v k c e rid =>
    obtain ⟨L, hL, -, hLe, -⟩ := hm; exact hvl v L hL e (List.mem_of_getElem? hLe)
  | prepareOK => trivial
  | commit => trivial
  | startViewChange => trivial
  | doViewChange d =>
    obtain ⟨-, -, -, -, -, ⟨L, I, hL, -, hdL, -⟩, -⟩ := hm
    exact fun e he => hvl _ L hL e (hdL.subset he)
  | startView v k c logs rid =>
    obtain ⟨hI, -⟩ := hm
    obtain ⟨L, hL, hlL, -⟩ := h.vinit_ok hI
    exact fun e he => hvl v L hL e (hlL.subset he)
  | getState => trivial
  | newState v logs c k rid =>
    obtain ⟨L, hL, -, -, heq⟩ := hm
    intro e he
    rw [heq] at he
    exact hvl v L hL e (List.mem_of_mem_take (List.mem_of_mem_drop he))
  | heartbeat => trivial

/-- Once view `u` has started, the replicas at a view `w < u` or below are no quorum (the
"may still accept" disjunct of `PossCommitted` in the safety clause). -/
theorem started_past (s : Sys) (h : Inv s) (u w : Nat) (I : List Entry)
    (hI : s.vinit u = some I) (hw : w < u) (Q : List Nat) (hq : Quorum s.n Q)
    (hQ : ∀ a ∈ Q, (s.reps a).view ≤ w) : False := by
  have h' := h.safety hI hw (l := I ++ [default]) ⟨Q, hq, fun a ha => .inr (hQ a ha)⟩
  have := h'.length_le
  simp at this
  omega

/-! ## The service's linearization -/

/-- The abstract key-value state: the store after the linearized log. -/
def absState (s : Sys) : Store := storeOf s.lin

/-- When the linearized log grows by one entry of a registered request with input `i`, the
abstract state takes the key-value model's step on `i`, and the entry's reply string is the
store's. -/
theorem stepLin_kv (s : Sys) (l mine : List Entry) (k : Nat) (h : Inv s)
    (hc : Committed s l) (hk : k ≤ l.length) (hmine : mine <+: s.lin) (hml : mine <+: l)
    (hlen : mine.length + 1 = k) (hgrow : s.lin.length < k) (e : Entry)
    (he : l[k - 1]? = some e) (i : KvInput GoString GoString)
    (hi : s.reg e.cid e.req = some i) :
    (stepLin s l k).lin = s.lin ++ [e] ∧
    (∀ e' ∈ s.lin, (e'.cid, e'.req) ≠ (e.cid, e.req)) ∧
    absState (stepLin s l k) = (svcStep (absState s) i).1 ∧
    outOf (stepLin s l k).lin s.lin.length = (svcStep (absState s) i).2 := by
  have hcok := h.committed_ok hc
  have hlm : mine = s.lin := hmine.eq_of_length (by have := hmine.length_le; omega)
  have hlinE : s.lin = l.take (k - 1) := by
    rw [← hlm]
    conv => lhs; rw [List.prefix_iff_eq_take.mp hml]
    congr 1; omega
  have hd : (l.drop (k - 1)).take 1 = [e] := by
    rw [List.take_one, List.head?_drop, he]; rfl
  have htk : l.take k = s.lin ++ [e] := by
    calc l.take k = l.take ((k - 1) + 1) := by congr 1; omega
      _ = l.take (k - 1) ++ (l.drop (k - 1)).take 1 := List.take_add ..
      _ = s.lin ++ [e] := by rw [hlinE, hd]
  have hstep : (stepLin s l k).lin = s.lin ++ [e] := by
    simp only [stepLin, ite_t hgrow]; rw [hd]
  have hel : e ∈ l := List.mem_of_getElem? he
  obtain ⟨i', hi', hop⟩ := hcok.2 e hel
  rw [hi] at hi'; cases hi'
  have hhandle := handle_ok (storeOf s.lin) (h.inputOk hi)
  refine ⟨hstep, ?_, ?_, ?_⟩
  · have hnd := noDupReq_prefix (List.take_prefix k l) hcok.1
    rw [htk] at hnd
    unfold NoDupReq at hnd
    rw [List.map_append, List.nodup_append] at hnd
    intro e' he' heq
    exact hnd.2.2 _ (List.mem_map.mpr ⟨e', he', rfl⟩) _ (by simp) heq
  · unfold absState; rw [hstep, storeOf_snoc, hop, hhandle]
  · have h1 : (s.lin ++ [e])[s.lin.length]? = some e := by simp
    have h2 : (s.lin ++ [e]).take s.lin.length = s.lin := by simp
    rw [hstep]; unfold outOf; rw [h1]; dsimp only
    rw [h2, hop, hhandle]; rfl


/-! ## Bounds (SF4, D5) -/


private theorem keys_length_le (L : List (Nat × Nat)) (hnd : L.Nodup)
    (hb : ∀ p ∈ L, 1 ≤ p.1 ∧ p.1 ≤ 6 ∧ p.2 < 2 ^ 28) : L.length ≤ 6 * 2 ^ 28 := by
  have hsub : L ⊆ (List.range' 1 6).flatMap (fun c => (List.range (2 ^ 28)).map (Prod.mk c)) := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := hb p hp
    simp only [List.mem_flatMap, List.mem_map, List.mem_range', List.mem_range]
    exact ⟨p.1, ⟨p.1 - 1, by omega, by omega⟩, p.2, h3, rfl⟩
  have := hnd.length_le_of_subset hsub
  simp [List.length_flatMap] at this
  exact Nat.le_trans this (by decide)

/-- Every view's log is bounded: its entries are registered requests without duplicates, and
the registrations are bounded (six clients, request numbers below 2^28). -/
theorem vlog_length_le (s : Sys) (h : Inv s) (v : Nat) (L : List Entry)
    (hL : s.vlog v = some L) : L.length ≤ 6 * 2 ^ 28 := by
  obtain ⟨_, _, _, hnd, hreg⟩ := h.vlog_ok hL
  have hb : ∀ e ∈ L, ∃ i, RegBound e.cid e.req i := by
    intro e he
    obtain ⟨i, hi, -⟩ := hreg e he
    obtain ⟨-, -, -, -, -, -, -, -, -, -, h11, -⟩ := h
    exact ⟨i, (h11 _ _ _ hi).2⟩
  have := keys_length_le (L.map fun e : Entry => (e.cid, e.req)) hnd (by
    intro p hp
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
    obtain ⟨_, h1, h2, h3, h4, -⟩ := hb e he
    exact ⟨h1, h2, h4⟩)
  simpa using this

/-- Every replica's log is bounded (as `vlog_length_le`). -/
theorem repLog_length_le (s : Sys) (h : Inv s) (r : Nat) (hr : r < s.n) :
    (s.reps r).log.length ≤ 6 * 2 ^ 28 := by
  obtain ⟨-, -, r3, r4⟩ := h.rep hr
  cases hst : (s.reps r).status with
  | viewChange =>
    obtain ⟨-, -, -, L, -, hL, -, hpL, -⟩ := r4 hst
    exact Nat.le_trans hpL.length_le (vlog_length_le s h _ L hL)
  | normal =>
    obtain ⟨L, -, hL, -, hpL, -⟩ := r3 (.inl hst)
    exact Nat.le_trans hpL.length_le (vlog_length_le s h _ L hL)
  | stateTransfer =>
    obtain ⟨L, -, hL, -, hpL, -⟩ := r3 (.inr hst)
    exact Nat.le_trans hpL.length_le (vlog_length_le s h _ L hL)

end VsrModel
