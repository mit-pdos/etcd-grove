/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/Rabia/Protocol.lean`, run `rabia-r1wake-1`.)

Rabia's protocol, purely (interface, stage 1): the record `M` of everything the servers and
clients have said (one global, append-only map of facts), its validity `Valid M` (each fact is
justified by facts recorded before it, following the code's rules: executor.go, msgHandler.go,
proxy.go, kit.go), and the two properties the client spec rests on:

* **agreement** (`agree`): two decisions of a slot are the same (NULL, or the same request);
* **at most once** (`atMostOnce`): no client request is decided in two slots.

The facts are keyed (`FKey`), each key set at most once (`M : FKey → Option FVal`, one-shot): a
server's proposal, state and vote messages per slot and phase, its local decision per slot, a
proxy's consensus objects, a client's registered requests, the global decision of each slot.
A fact's justification may only mention facts already recorded, and facts are never changed, so
validity is preserved by adding a justified fact (`Valid.insert`).

Stage 2: the rules are stated for the configuration `c` the client node chose (`RCfg`; its
record `.cfg` is the first fact), any `n ≥ 2f + 1`, `f ≥ 1`: a round's quorum is `q = n - f`
messages of distinct servers (`Senders`), and every value a server sends is the function the code
computes of the quorum it received (`VoteOk`, `StateOk`); a decision rests on evidence of one of
three kinds (`DecEvidence`): `f + 1` votes, or (the fast paths, reachable when `MajorityPlusF ≤
n - f`) `MajorityPlusF` states or proposals. A consensus object carries a batch of requests
(`.pobj id ↦ .reqs rs`).
-/
module

public import Dsverify.Proof.rabia.Core.Model

@[expose] public section

namespace Perennial.rabia.model

/-- A request id: client `c`'s `n`-th request (the ghost counter; the wire's `CliSeq` is `n` as a
`uint32`). -/
abbrev ReqId := Nat × Nat

/-- A consensus object's id `(ProId, ProSeq)`: proxy `X`'s `q`-th object. -/
abbrev ObjId := Nat × Nat

/-- A slot's value: NULL or a consensus object (by its id). -/
inductive DVal where
  | null
  | obj (id : ObjId)
deriving DecidableEq, Inhabited

/-- The keys of the facts. -/
inductive FKey where
  /-- client `c`'s `n`-th request is the command (`Op` registers it before sending) -/
  | reg (r : ReqId)
  /-- the deployment's configuration (recorded first, by the client node's `New`) -/
  | cfg
  /-- proxy `X`'s object `q` carries the requests `rs`, in order (`CmdReceiver`'s batch) -/
  | pobj (id : ObjId)
  /-- request `r` is carried by object `id` of proxy `X` (recorded with `pobj id`, by the
  request's proxy `X`: a request is in one object only) -/
  | robj (X : Nat) (r : ReqId)
  /-- server `X`'s proposal for slot `s` (`genProposalMsg`) -/
  | prop (X s : Nat)
  /-- server `X`'s state of phase `p ≥ 1` for slot `s` -/
  | st (X s p : Nat)
  /-- server `X`'s vote of phase `p` for slot `s` (`0`, `1`, or `2` for `?`) -/
  | vt (X s p : Nat)
  /-- server `X`'s decision of slot `s` (its `epilogue`) -/
  | mydec (X s : Nat)
  /-- slot `s`'s decision (the first server to decide it records it) -/
  | dec (s : Nat)
  /-- server `X` asked for slot `s`'s proposal (`requestProposalAndWait`'s `ProposalRequest`) -/
  | preq (X s : Nat)
deriving DecidableEq, Inhabited

/-- The facts' values. -/
inductive FVal where
  | cmd (c : GoString)
  | reqs (rs : List ReqId)
  | cfgv (c : RCfg)
  | obj (id : ObjId)
  | bit (b : Nat)
  | dval (d : DVal)
deriving DecidableEq, Inhabited

/-- The record of facts. -/
abbrev Facts := FKey → Option FVal

/-- `M` with the fact `k = v` added. -/
def Facts.set (M : Facts) (k : FKey) (v : FVal) : Facts := fun k' => if k' = k then some v else M k'

/-- `M'` extends `M` (facts are never changed). -/
def Facts.le (M M' : Facts) : Prop := ∀ k v, M k = some v → M' k = some v

/-! ## The rules -/

section rules
variable (c : RCfg)

/-- Messages of distinct servers (each below `n`), with their values. -/
def Senders {α : Type} (W : List (Nat × α)) : Prop :=
  (W.map Prod.fst).Nodup ∧ ∀ x ∈ W, x.1 < c.n

/-- `RecvBCMsgsMajV`/`MajT` of received values (each `0`, `1` or `2` for `?`): the majority of
`0`s against `1`s (ties go to `1`), and its tally. -/
def majV (vs : List Nat) : Nat := if vs.count 0 > vs.count 1 then 0 else 1
def majT (vs : List Nat) : Nat := if vs.count 0 > vs.count 1 then vs.count 0 else vs.count 1

/-- Object `id` has the proposals of a majority of the servers at slot `s` (`RecvProposalsMajT ≥
Majority`, or a `ProposalReply`'s). -/
def MajProp (M : Facts) (s : Nat) (id : ObjId) : Prop :=
  ∃ W : List Nat, (W.Nodup ∧ ∀ X ∈ W, X < c.n) ∧ W.length ≥ c.maj ∧
    ∀ X ∈ W, M (.prop X s) = some (.obj id)

/-- A quorum of proposals of slot `s` (`n - f` from distinct servers). -/
def PropQuorum (M : Facts) (s : Nat) (W : List (Nat × ObjId)) : Prop :=
  Senders c W ∧ W.length = c.q ∧ ∀ x ∈ W, M (.prop x.1 s) = some (.obj x.2)

/-- A quorum of the states (`r = 1`, phase `p ≥ 1`) or votes (`r = 2`) of slot `s`. -/
def BitQuorum (M : Facts) (s p r : Nat) (W : List (Nat × Nat)) : Prop :=
  Senders c W ∧ W.length = c.q ∧
    ∀ x ∈ W, M (if r = 1 then .st x.1 s p else .vt x.1 s p) = some (.bit x.2)

/-- The vote of phase `p` a server sends after a quorum of proposals (phase 0:
`phase0Round1AfterWait`, not deciding: `1` if an object has a majority, else `?`) or of states
(`phaseNRound1AfterWait`, not deciding: their majority value if its tally reaches `Majority`, else
`?`). -/
def VoteOk (M : Facts) (s p b : Nat) : Prop :=
  if p = 0 then
    (b = 1 ∧ ∃ id, MajProp c M s id) ∨
    (b = 2 ∧ ∃ W, PropQuorum c M s W ∧ ∀ id, (W.filter (·.2 = id)).length < c.maj)
  else
    ∃ W, BitQuorum c M s p 1 W ∧
      b = (if majT (W.map Prod.snd) ≥ c.maj then majV (W.map Prod.snd) else 2)

/-- The state of phase `p + 1` a server sends after a quorum of votes of phase `p` that does not
let it decide (`phase0Round2AfterWait`, `phaseNRound2AfterWait`): their majority if one is not
`?`; if all are `?`, `0` at phase 0 and any bit (the coin) after. -/
def StateOk (M : Facts) (s p b : Nat) : Prop :=
  ∃ W, BitQuorum c M s p 2 W ∧ majT (W.map Prod.snd) < c.fp1 ∧
    (if majT (W.map Prod.snd) ≥ 1 then b = majV (W.map Prod.snd)
     else (if p = 0 then b = 0 else b ≤ 1))

/-- What a decided bit means: `0` NULL, `1` the object with a majority of proposals
(`findReturnValue`: the server's own quorum's, or a `ProposalReply`'s). -/
def BitDec (M : Facts) (s b : Nat) (d : DVal) : Prop :=
  b ≤ 1 ∧ (b = 0 → d = .null) ∧ (b = 1 → ∃ id, d = .obj id ∧ MajProp c M s id)

/-- A server's own evidence that slot `s` is decided `d`: `f + 1` servers' votes of a phase agree
on a bit (`phase0Round2AfterWait`, `phaseNRound2AfterWait`), or `MajorityPlusF` servers' states of
a phase `≥ 1` do (`phaseNRound1AfterWait`), or `MajorityPlusF` servers proposed one object
(`phase0Round1AfterWait`'s `genDecMsgType1`). -/
def DecEvidence (M : Facts) (s : Nat) (d : DVal) : Prop :=
  (∃ (p b : Nat) (W : List Nat), (W.Nodup ∧ ∀ X ∈ W, X < c.n) ∧ W.length ≥ c.fp1 ∧
    (∀ X ∈ W, M (.vt X s p) = some (.bit b)) ∧ BitDec c M s b d) ∨
  (∃ (p b : Nat) (W : List Nat), p ≥ 1 ∧ (W.Nodup ∧ ∀ X ∈ W, X < c.n) ∧ W.length ≥ c.mpf ∧
    (∀ X ∈ W, M (.st X s p) = some (.bit b)) ∧ BitDec c M s b d) ∨
  (∃ (id : ObjId) (W : List Nat), (W.Nodup ∧ ∀ X ∈ W, X < c.n) ∧ W.length ≥ c.mpf ∧
    (∀ X ∈ W, M (.prop X s) = some (.obj id)) ∧ d = .obj id)

/-- A server's proposal for slot `t` is an object it did not already see decided as its own
proposal at an earlier slot (`getRequest` pops it from the pending queue, which never holds an
object after the server's proposal of it was decided: `epilogue` puts back only an unmatched or
NULL proposal). -/
def PropOk (M : Facts) (X t : Nat) (id : ObjId) : Prop :=
  (∀ s < t, ∃ i d, M (.prop X s) = some (.obj i) ∧ M (.mydec X s) = some (.dval d)) ∧
  ∀ s < t, M (.prop X s) = some (.obj id) → M (.mydec X s) ≠ some (.dval (.obj id))

/-- Each fact, justified by the facts of `M`. -/
def Justified (M : Facts) : FKey → FVal → Prop
  | .cfg, .cfgv c' => c' = c
  | .reg _, .cmd _ => True
  | .pobj id, .reqs rs => rs ≠ [] ∧ rs.Nodup ∧ id.1 < c.n ∧ ∀ r ∈ rs,
      (∃ cm, M (.reg r) = some (.cmd cm)) ∧ id.1 = r.1 % c.n ∧ M (.robj id.1 r) = some (.obj id)
  | .robj X r, .obj id => X = id.1 ∧ ∃ rs, M (.pobj id) = some (.reqs rs) ∧ r ∈ rs
  | .prop X s, .obj id => X < c.n ∧ (∃ rs, M (.pobj id) = some (.reqs rs)) ∧ PropOk M X s id
  | .st X _ _, .bit b => X < c.n ∧ b ≤ 1  -- refined below (`StateRule`)
  | .vt X _ _, .bit b => X < c.n ∧ b ≤ 2  -- refined below (`VoteRule`)
  | .mydec X s, .dval d => X < c.n ∧ (DecEvidence c M s d ∨ M (.dec s) = some (.dval d))
  -- the first server to decide a slot decides it from its own evidence (a server learns a
  -- decision from a `Decision` message only after its sender recorded it)
  | .dec s, .dval d => DecEvidence c M s d
  | .preq X _, .bit _ => X < c.n
  | _, _ => False

/-- The rules of states and votes (phase `p ≥ 1` states come from phase `p - 1` votes). -/
def StateRule (M : Facts) : Prop :=
  ∀ X s p b, M (.st X s p) = some (.bit b) → p ≥ 1 ∧ StateOk c M s (p - 1) b
def VoteRule (M : Facts) : Prop :=
  ∀ X s p b, M (.vt X s p) = some (.bit b) → VoteOk c M s p b

/-- Validity at configuration `c`: every fact is justified; the rules hold; slots are decided in
order (a server decides slot `s` only after `s - 1`, so the decided slots are a prefix). -/
def ValidAt (M : Facts) : Prop :=
  (∀ k v, M k = some v → Justified c M k v) ∧ StateRule c M ∧ VoteRule c M ∧
  (∀ s, M (.dec (s + 1)) ≠ none → M (.dec s) ≠ none) ∧
  (∀ X s, M (.mydec X (s + 1)) ≠ none → M (.mydec X s) ≠ none) ∧
  (∀ X s, M (.mydec X s) ≠ none → M (.dec s) ≠ none)

/-- Slot `s` is decided `d`: by some server's evidence, or recorded, or some server's decision. -/
def Decided (M : Facts) (s : Nat) (d : DVal) : Prop :=
  DecEvidence c M s d ∨ M (.dec s) = some (.dval d) ∨ ∃ X, M (.mydec X s) = some (.dval d)

end rules

/-- Validity: before the configuration is recorded, nothing is; after, the record is valid at the
configuration, which `choose` can pick. -/
def Valid (M : Facts) : Prop :=
  match M .cfg with
  | some (.cfgv c) => c.Ok ∧ ValidAt c M
  | _ => ∀ k, M k = none

/-- The configuration of a record (once recorded). -/
def CfgOf (M : Facts) (c : RCfg) : Prop := M .cfg = some (.cfgv c)

/-! ## The properties (proved in Prove; statements of the interface) -/

section props
variable {c : RCfg}

/-- Facts only grow. -/
theorem Facts.le_insert (M : Facts) (k : FKey) (v : FVal) (hk : M k = none) :
    M.le (M.set k v) := by
  intro k' v' h
  simp only [Facts.set]
  split
  · subst_vars; rw [hk] at h; cases h
  · exact h

theorem Facts.le_ne_none {M M' : Facts} (hle : M.le M') {k : FKey} (h : M k ≠ none) :
    M' k ≠ none := by
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp h
  rw [hle _ _ hv]; simp

/-- A valid record with a configuration is valid at it. -/
theorem Valid.at {M : Facts} (hM : Valid M) (hc : CfgOf M c) : c.Ok ∧ ValidAt c M := by
  unfold Valid at hM; unfold CfgOf at hc; rw [hc] at hM; exact hM

/-! ## Helper lemmas: counting -/

/-- A list of distinct numbers below `n` has at most `n` elements. -/
theorem nb_length_le {n : Nat} {L : List Nat} (hnd : L.Nodup) (hlt : ∀ X ∈ L, X < n) :
    L.length ≤ n := by
  have := hnd.length_le_of_subset (l₂ := List.range n) (fun x hx => List.mem_range.mpr (hlt x hx))
  simpa using this

theorem length_filter_add_not {α : Type} (p : α → Bool) (L : List α) :
    (L.filter p).length + (L.filter (fun x => !p x)).length = L.length := by
  induction L with
  | nil => rfl
  | cons a L ih => cases h : p a <;> simp [h] <;> omega

theorem length_filter_mono {α : Type} {p q : α → Bool} {L : List α}
    (h : ∀ x ∈ L, p x = true → q x = true) :
    (L.filter p).length ≤ (L.filter q).length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ih := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have ha := h a (List.mem_cons_self ..)
    cases hp : p a <;> cases hq : q a <;> simp [hp, hq] at ha ⊢ <;> omega

/-- Two sets of distinct servers below `n` share at least `|A| + |B| - n` servers. -/
theorem inter_count {n : Nat} {A B : List Nat} (hA : A.Nodup) (hA' : ∀ X ∈ A, X < n)
    (hB : B.Nodup) (hB' : ∀ X ∈ B, X < n) :
    A.length + B.length ≤ (A.filter (fun x => decide (x ∈ B))).length + n := by
  have hC : (A.filter (fun x => !decide (x ∈ B)) ++ B).Nodup := by
    rw [List.nodup_append]
    refine ⟨hA.sublist List.filter_sublist, hB, ?_⟩
    intro a ha b hb e
    subst e
    simp [List.mem_filter] at ha
    exact ha.2 hb
  have hC' : ∀ X ∈ A.filter (fun x => !decide (x ∈ B)) ++ B, X < n := by
    intro X hX
    rcases List.mem_append.mp hX with h|h
    · exact hA' X (List.mem_filter.mp h).1
    · exact hB' X h
  have h1 := nb_length_le hC hC'
  have h2 := length_filter_add_not (fun x => decide (x ∈ B)) A
  simp only [List.length_append] at h1
  omega

/-- Two sets of distinct servers below `n` whose sizes sum above `n` meet. -/
theorem meet_of_length {n : Nat} {A B : List Nat} (hA : A.Nodup) (hA' : ∀ X ∈ A, X < n)
    (hB : B.Nodup) (hB' : ∀ X ∈ B, X < n) (h : A.length + B.length > n) :
    ∃ X, X ∈ A ∧ X ∈ B := by
  have := inter_count hA hA' hB hB'
  cases hf : A.filter (fun x => decide (x ∈ B)) with
  | nil => rw [hf] at this; simp at this; omega
  | cons X _ =>
    have hX : X ∈ A.filter (fun x => decide (x ∈ B)) := by rw [hf]; simp
    simp only [List.mem_filter, decide_eq_true_eq] at hX
    exact ⟨X, hX⟩

/-- `inter_count` for messages (sender, value). -/
theorem inter_count_pairs {α : Type} {n : Nat} {W : List (Nat × α)} {B : List Nat}
    (hW : (W.map Prod.fst).Nodup) (hW' : ∀ x ∈ W, x.1 < n) (hB : B.Nodup)
    (hB' : ∀ X ∈ B, X < n) :
    W.length + B.length ≤ (W.filter (fun x => decide (x.1 ∈ B))).length + n := by
  have := inter_count hW (fun X hX => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hX; exact hW' x hx) hB hB'
  rw [List.filter_map, List.length_map, List.length_map] at this
  exact this

theorem count_eq_filter (W : List (Nat × Nat)) (b : Nat) :
    (W.map Prod.snd).count b = (W.filter (fun x => decide (x.2 = b))).length := by
  induction W with
  | nil => rfl
  | cons a W ih => by_cases h : a.2 = b <;> simp [h, ih]

theorem count01_le (vs : List Nat) : vs.count 0 + vs.count 1 ≤ vs.length := by
  induction vs with
  | nil => simp
  | cons a vs ih =>
    by_cases h0 : a = 0
    · subst h0; simp; omega
    · by_cases h1 : a = 1
      · subst h1; simp; omega
      · simp [h0, h1]; omega

theorem majT_eq (vs : List Nat) : majT vs = vs.count (majV vs) := by
  unfold majT majV; split <;> rfl

theorem majT_ge (vs : List Nat) : vs.count 0 ≤ majT vs ∧ vs.count 1 ≤ majT vs := by
  unfold majT; split <;> omega

theorem maj_of_counts {vs : List Nat} {b m : Nat} (hb : b ≤ 1) (h1 : vs.count b ≥ m)
    (h2 : vs.count (1 - b) < m) : majV vs = b ∧ majT vs = vs.count b := by
  have : b = 0 ∨ b = 1 := by omega
  rcases this with rfl|rfl <;> simp at h2 <;> unfold majV majT <;> split <;> omega

theorem maj_all {vs : List Nat} {b : Nat} (hb : b ≤ 1) (h : ∀ x ∈ vs, x = b)
    (hl : vs.length ≥ 1) : majV vs = b ∧ majT vs = vs.length := by
  have e1 : vs.count b = vs.length := List.count_eq_length.mpr (fun x hx => (h x hx).symm)
  have e2 : vs.count (1 - b) = 0 := List.count_eq_zero.mpr (fun hx => by have := h _ hx; omega)
  have h1 : vs.count b ≥ 1 := by omega
  have h2 : vs.count (1 - b) < 1 := by omega
  have := maj_of_counts hb h1 h2
  exact ⟨this.1, this.2.trans e1⟩

theorem maj_b2 {vs : List Nat} {b : Nat} (hb : b ≤ 1) (h : ∀ x ∈ vs, x = b ∨ x = 2)
    (hl : vs.count b ≥ 1) : majV vs = b ∧ majT vs = vs.count b := by
  have e2 : vs.count (1 - b) = 0 := List.count_eq_zero.mpr (fun hx => by have := h _ hx; omega)
  exact maj_of_counts (m := 1) hb hl (by omega)

/-- What the protocol needs of the numbers. -/
theorem RCfg.Ok.nums {c : RCfg} (hc : c.Ok) :
    c.q + c.fp1 > c.n ∧ 2 * c.maj > c.n ∧ 2 * c.mpf > c.n ∧ c.maj ≤ c.q ∧ c.fp1 ≤ c.q ∧
    c.n + c.maj ≤ c.q + c.mpf ∧ c.q < 2 * c.maj ∧ 1 ≤ c.q ∧ 1 ≤ c.fp1 ∧ c.maj ≤ c.mpf ∧
    1 ≤ c.maj := by
  have := hc.nf; unfold RCfg.q RCfg.maj RCfg.mpf RCfg.fp1; omega

theorem RCfg.two_maj (c : RCfg) : 2 * c.maj > c.n := by unfold RCfg.maj; omega

/-! ## Helper lemmas: the rules' consequences -/

theorem ValidAt.st_bit {M : Facts} (hM : ValidAt c M) {X s p : Nat} {v : FVal}
    (h : M (.st X s p) = some v) : ∃ b, v = .bit b ∧ b ≤ 1 := by
  have := hM.1 _ _ h
  cases v <;> simp only [Justified] at this
  exact ⟨_, rfl, this.2⟩

theorem ValidAt.vt_bit {M : Facts} (hM : ValidAt c M) {X s p : Nat} {v : FVal}
    (h : M (.vt X s p) = some v) : ∃ b, v = .bit b ∧ b ≤ 2 := by
  have := hM.1 _ _ h
  cases v <;> simp only [Justified] at this
  exact ⟨_, rfl, this.2⟩

theorem BitQuorum.st {M : Facts} {s p : Nat} {W : List (Nat × Nat)} (h : BitQuorum c M s p 1 W) :
    ∀ x ∈ W, M (.st x.1 s p) = some (.bit x.2) := by
  intro x hx; simpa using h.2.2 x hx

theorem BitQuorum.vt {M : Facts} {s p : Nat} {W : List (Nat × Nat)} (h : BitQuorum c M s p 2 W) :
    ∀ x ∈ W, M (.vt x.1 s p) = some (.bit x.2) := by
  intro x hx; simpa using h.2.2 x hx

/-- Votes of a phase `r ≥ 1` whose states are all `b` are all `b`. -/
theorem ValidAt.votes_of_states {M : Facts} (hc : c.Ok) (hM : ValidAt c M) {s r b : Nat}
    (hr : r ≠ 0) (hb : b ≤ 1) (hst : ∀ X v, M (.st X s r) = some v → v = .bit b) :
    ∀ X v, M (.vt X s r) = some v → v = .bit b := by
  have hn := hc.nums
  intro X v h
  obtain ⟨a, rfl, _⟩ := hM.vt_bit h
  have hv := hM.2.2.1 _ _ _ _ h
  simp only [VoteOk, hr, ↓reduceIte] at hv
  obtain ⟨W, hW, rfl⟩ := hv
  have hall : ∀ y ∈ W.map Prod.snd, y = b := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    have := hst _ _ (hW.st x hx)
    simpa using this
  have hlen : (W.map Prod.snd).length = c.q := by rw [List.length_map, hW.2.1]
  obtain ⟨h1, h2⟩ := maj_all hb hall (by omega)
  have : majT (W.map Prod.snd) ≥ c.maj := by omega
  simp [this, h1]

/-- No state follows a phase whose votes are all one bit. -/
theorem ValidAt.no_st_after {M : Facts} (hc : c.Ok) (hM : ValidAt c M) {s r b : Nat}
    (hb : b ≤ 1) (hvt : ∀ X v, M (.vt X s r) = some v → v = .bit b) :
    ∀ X v, M (.st X s (r + 1)) = some v → False := by
  have hn := hc.nums
  intro X v h
  obtain ⟨b', rfl, _⟩ := hM.st_bit h
  obtain ⟨_, hs⟩ := hM.2.1 _ _ _ _ h
  simp only [Nat.add_sub_cancel] at hs
  obtain ⟨W, hW, hT, _⟩ := hs
  have hall : ∀ y ∈ W.map Prod.snd, y = b := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    have := hvt _ _ (hW.vt x hx)
    simpa using this
  have hlen : (W.map Prod.snd).length = c.q := by rw [List.length_map, hW.2.1]
  obtain ⟨_, h2⟩ := maj_all hb hall (by omega)
  omega

/-- No vote at a phase `r ≥ 1` without states. -/
theorem ValidAt.no_vt_of_no_st {M : Facts} (hc : c.Ok) (hM : ValidAt c M) {s r : Nat}
    (hr : r ≠ 0) (hst : ∀ X v, M (.st X s r) = some v → False) :
    ∀ X v, M (.vt X s r) = some v → False := by
  have hn := hc.nums
  intro X v h
  obtain ⟨a, rfl, _⟩ := hM.vt_bit h
  have hv := hM.2.2.1 _ _ _ _ h
  simp only [VoteOk, hr, ↓reduceIte] at hv
  obtain ⟨W, hW, _⟩ := hv
  cases hW' : W with
  | nil => have := hW.2.1; rw [hW'] at this; simp at this; omega
  | cons x _ => exact hst _ _ (hW.st x (by rw [hW']; simp))

/-- After a phase whose votes are all one bit, nothing. -/
theorem ValidAt.dead {M : Facts} (hc : c.Ok) (hM : ValidAt c M) {s r b : Nat} (hb : b ≤ 1)
    (hvt : ∀ X v, M (.vt X s r) = some v → v = .bit b) :
    ∀ r', r < r' → (∀ X v, M (.st X s r') = some v → False) ∧
      (∀ X v, M (.vt X s r') = some v → False) := by
  have key : ∀ m, (∀ X v, M (.st X s (r + 1 + m)) = some v → False) ∧
      (∀ X v, M (.vt X s (r + 1 + m)) = some v → False) := by
    intro m
    induction m with
    | zero =>
      have h1 := hM.no_st_after hc hb hvt
      exact ⟨h1, hM.no_vt_of_no_st hc (by omega) h1⟩
    | succ m ih =>
      have h1 := hM.no_st_after hc (b := b) (r := r + 1 + m) hb (fun X v h => (ih.2 X v h).elim)
      exact ⟨h1, hM.no_vt_of_no_st hc (by omega) h1⟩
  intro r' hr'
  have := key (r' - r - 1)
  rwa [show r + 1 + (r' - r - 1) = r' by omega] at this

/-- A non-`?` vote at phase `p ≥ 1` is backed by a majority of states equal to it. -/
theorem ValidAt.vote_holders {M : Facts} (hM : ValidAt c M) {s p X a : Nat}
    (hp : p ≠ 0) (h : M (.vt X s p) = some (.bit a)) (ha : a ≠ 2) :
    ∃ H : List Nat, (H.Nodup ∧ ∀ Y ∈ H, Y < c.n) ∧ H.length ≥ c.maj ∧
      ∀ Y ∈ H, M (.st Y s p) = some (.bit a) := by
  have hv := hM.2.2.1 _ _ _ _ h
  simp only [VoteOk, hp, ↓reduceIte] at hv
  obtain ⟨W, hW, hb⟩ := hv
  by_cases hT : majT (W.map Prod.snd) ≥ c.maj
  · simp only [hT, ↓reduceIte] at hb
    subst hb
    refine ⟨(W.filter (fun x => decide (x.2 = majV (W.map Prod.snd)))).map Prod.fst,
      ⟨?_, ?_⟩, ?_, ?_⟩
    · exact hW.1.1.sublist (List.filter_sublist.map _)
    · intro Y hY
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hY
      exact hW.1.2 x (List.mem_filter.mp hx).1
    · rw [List.length_map, ← count_eq_filter, ← majT_eq]; exact hT
    · intro Y hY
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hY
      obtain ⟨hx1, hx2⟩ := List.mem_filter.mp hx
      have := hW.st x hx1
      simp only [decide_eq_true_eq] at hx2
      rw [← hx2]; exact this
  · simp [hT] at hb; exact absurd hb ha

/-- Vote consistency: the non-`?` votes of a phase agree. -/
theorem ValidAt.vote_cons {M : Facts} (hM : ValidAt c M) {s p j k a b : Nat}
    (hj : M (.vt j s p) = some (.bit a)) (hk : M (.vt k s p) = some (.bit b))
    (ha : a ≠ 2) (hb : b ≠ 2) : a = b := by
  by_cases hp : p = 0
  · subst hp
    have h1 := hM.2.2.1 _ _ _ _ hj
    have h2 := hM.2.2.1 _ _ _ _ hk
    simp only [VoteOk, ↓reduceIte] at h1 h2
    rcases h1 with ⟨rfl, _⟩|⟨rfl, _⟩ <;> rcases h2 with ⟨rfl, _⟩|⟨rfl, _⟩ <;> simp_all
  · obtain ⟨H, hH, hl, hHs⟩ := hM.vote_holders hp hj ha
    obtain ⟨H', hH', hl', hHs'⟩ := hM.vote_holders hp hk hb
    obtain ⟨Y, hY, hY'⟩ := meet_of_length hH.1 hH.2 hH'.1 hH'.2
      (by have := c.two_maj; omega)
    have := (hHs Y hY).symm.trans (hHs' Y hY')
    simpa using this

/-- `f + 1` votes `b` at `P`: the states of `P + 1` are `b`. -/
theorem ValidAt.st_after_fp1 {M : Facts} (hc : c.Ok) (hM : ValidAt c M) {s P b : Nat}
    {L : List Nat} (hL : L.Nodup ∧ ∀ X ∈ L, X < c.n) (hlen : L.length ≥ c.fp1)
    (hLv : ∀ X ∈ L, M (.vt X s P) = some (.bit b)) (hb : b ≤ 1) :
    ∀ X v, M (.st X s (P + 1)) = some v → v = .bit b := by
  have hn := hc.nums
  intro X v h
  obtain ⟨b', rfl, _⟩ := hM.st_bit h
  obtain ⟨_, hs⟩ := hM.2.1 _ _ _ _ h
  simp only [Nat.add_sub_cancel] at hs
  obtain ⟨W, hW, hT, hb'⟩ := hs
  obtain ⟨Y, hY1, hY2⟩ := meet_of_length (A := W.map Prod.fst) (B := L) hW.1.1
    (fun Y hY => by obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hY; exact hW.1.2 x hx) hL.1 hL.2
    (by rw [List.length_map, hW.2.1]; omega)
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hY1
  have hyb : y.2 = b := by
    have := hW.vt y hy; rw [hLv _ hY2] at this; simpa using this.symm
  have hall : ∀ z ∈ W.map Prod.snd, z = b ∨ z = 2 := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
    by_cases h2 : x.2 = 2
    · exact Or.inr h2
    · exact Or.inl (hM.vote_cons (hW.vt x hx) (hLv _ hY2) h2 (by omega))
  have hcnt : (W.map Prod.snd).count b ≥ 1 :=
    List.count_pos_iff.mpr (List.mem_map.mpr ⟨y, hy, hyb⟩)
  obtain ⟨hV, hTT⟩ := maj_b2 hb hall hcnt
  have : majT (W.map Prod.snd) ≥ 1 := by omega
  simp only [this, ↓reduceIte] at hb'
  rw [hb', hV]

/-- `MajorityPlusF` states `b` at `P ≥ 1`: the votes of `P` are `b`. -/
theorem ValidAt.votes_of_mpf_st {M : Facts} (hc : c.Ok) (hM : ValidAt c M) {s P b : Nat}
    {L : List Nat} (hP : P ≠ 0) (hL : L.Nodup ∧ ∀ X ∈ L, X < c.n) (hlen : L.length ≥ c.mpf)
    (hLs : ∀ X ∈ L, M (.st X s P) = some (.bit b)) (hb : b ≤ 1) :
    ∀ X v, M (.vt X s P) = some v → v = .bit b := by
  have hn := hc.nums
  intro X v h
  obtain ⟨a, rfl, _⟩ := hM.vt_bit h
  have hv := hM.2.2.1 _ _ _ _ h
  simp only [VoteOk, hP, ↓reduceIte] at hv
  obtain ⟨W, hW, rfl⟩ := hv
  have hI := inter_count_pairs hW.1.1 hW.1.2 hL.1 hL.2
  have hsub : (W.filter (fun x => decide (x.1 ∈ L))).length ≤
      (W.filter (fun x => decide (x.2 = b))).length := length_filter_mono (by
    intro x hx h1
    simp only [decide_eq_true_eq] at h1 ⊢
    have := hW.st x hx; rw [hLs _ h1] at this; simpa using this.symm)
  rw [← count_eq_filter] at hsub
  have hsum := count01_le (W.map Prod.snd)
  rw [List.length_map, hW.2.1] at hsum
  have hcb : (W.map Prod.snd).count b ≥ c.maj := by have := hW.2.1; omega
  have hco : (W.map Prod.snd).count (1 - b) < c.maj := by
    have : b = 0 ∨ b = 1 := by omega
    rcases this with rfl|rfl <;> simp at hcb ⊢ <;> omega
  obtain ⟨hV, hTT⟩ := maj_of_counts hb hcb hco
  have : majT (W.map Prod.snd) ≥ c.maj := by omega
  simp [this, hV]

/-- `MajorityPlusF` proposals of one object: the votes of phase 0 are `1`. -/
theorem ValidAt.votes_of_mpf_prop {M : Facts} (hc : c.Ok) (hM : ValidAt c M) {s : Nat}
    {id : ObjId} {L : List Nat} (hL : L.Nodup ∧ ∀ X ∈ L, X < c.n) (hlen : L.length ≥ c.mpf)
    (hLp : ∀ X ∈ L, M (.prop X s) = some (.obj id)) :
    ∀ X v, M (.vt X s 0) = some v → v = .bit 1 := by
  have hn := hc.nums
  intro X v h
  obtain ⟨a, rfl, _⟩ := hM.vt_bit h
  have hv := hM.2.2.1 _ _ _ _ h
  simp only [VoteOk, ↓reduceIte] at hv
  rcases hv with ⟨rfl, _⟩ | ⟨rfl, W, hW, hlt⟩
  · rfl
  · exfalso
    have hI := inter_count_pairs hW.1.1 hW.1.2 hL.1 hL.2
    have hsub : (W.filter (fun x => decide (x.1 ∈ L))).length ≤
        (W.filter (fun x => decide (x.2 = id))).length := length_filter_mono (by
      intro x hx h1
      simp only [decide_eq_true_eq] at h1 ⊢
      have := hW.2.2 x hx; rw [hLp _ h1] at this; simpa using this.symm)
    have := hlt id
    have := hW.2.1
    omega

/-- What a piece of evidence at phase `P` for bit `b` says. -/
def EvSum (c : RCfg) (M : Facts) (s : Nat) (d : DVal) (P b : Nat) : Prop :=
  BitDec c M s b d ∧
  (∀ X r v, P < r → M (.st X s r) = some v → v = .bit b) ∧
  (∀ X r v, P < r → M (.vt X s r) = some v → v = .bit b) ∧
  ((∃ X, M (.vt X s P) = some (.bit b)) ∨
   (P ≠ 0 ∧ ∃ L : List Nat, (L.Nodup ∧ ∀ X ∈ L, X < c.n) ∧ L.length ≥ c.mpf ∧
      (∀ X ∈ L, M (.st X s P) = some (.bit b)) ∧ ∀ X v, M (.vt X s P) = some v → v = .bit b) ∨
   (P = 0 ∧ b = 1 ∧ ∀ X v, M (.vt X s 0) = some v → v = .bit 1))

theorem exists_mem_of_length {L : List Nat} {m : Nat} (h : L.length ≥ m) (hm : 1 ≤ m) :
    ∃ X, X ∈ L :=
  List.exists_mem_of_ne_nil L (by intro e; subst e; simp at h; omega)

theorem ValidAt.ev_summary {M : Facts} (hc : c.Ok) (hM : ValidAt c M) {s : Nat} {d : DVal}
    (h : DecEvidence c M s d) : ∃ P b, EvSum c M s d P b := by
  have hn := hc.nums
  rcases h with ⟨p, b, L, hL, hlen, hLv, hbd⟩ | ⟨p, b, L, hp, hL, hlen, hLs, hbd⟩ |
    ⟨id, L, hL, hlen, hLp, rfl⟩
  · have hb := hbd.1
    have hst := hM.st_after_fp1 hc hL hlen hLv hb
    have hvt := hM.votes_of_states hc (r := p + 1) (by omega) hb hst
    have hdead := hM.dead hc hb hvt
    obtain ⟨X, hX⟩ := exists_mem_of_length hlen (by omega)
    refine ⟨p, b, hbd, ?_, ?_, Or.inl ⟨X, hLv X hX⟩⟩
    · intro Y r v hr h
      by_cases e : r = p + 1
      · subst e; exact hst _ _ h
      · exact ((hdead r (by omega)).1 _ _ h).elim
    · intro Y r v hr h
      by_cases e : r = p + 1
      · subst e; exact hvt _ _ h
      · exact ((hdead r (by omega)).2 _ _ h).elim
  · have hb := hbd.1
    have hvt := hM.votes_of_mpf_st hc (by omega) hL hlen hLs hb
    have hdead := hM.dead hc hb hvt
    refine ⟨p, b, hbd, fun Y r v hr h => ((hdead r hr).1 _ _ h).elim,
      fun Y r v hr h => ((hdead r hr).2 _ _ h).elim, Or.inr (Or.inl ⟨by omega, L, hL, hlen, hLs, hvt⟩)⟩
  · have hvt := hM.votes_of_mpf_prop hc hL hlen hLp
    have hdead := hM.dead hc (b := 1) (by omega) hvt
    refine ⟨0, 1, ⟨by omega, by omega, fun _ => ⟨id, rfl, L, hL, by omega, hLp⟩⟩,
      fun Y r v hr h => ((hdead r hr).1 _ _ h).elim,
      fun Y r v hr h => ((hdead r hr).2 _ _ h).elim, Or.inr (Or.inr ⟨rfl, rfl, hvt⟩)⟩

theorem ValidAt.evsum_cmp {M : Facts} (hc : c.Ok) (hM : ValidAt c M) {s : Nat} {d d' : DVal}
    {P b P' b' : Nat} (h : EvSum c M s d P b) (h' : EvSum c M s d' P' b') (hle : P ≤ P') :
    b = b' := by
  have hn := hc.nums
  obtain ⟨hbd, hS, hV, hK⟩ := h
  obtain ⟨hbd', hS', hV', hK'⟩ := h'
  have hb := hbd.1
  have hb' := hbd'.1
  rcases Nat.lt_or_eq_of_le hle with hlt | rfl
  · rcases hK' with ⟨X, hX⟩ | ⟨hP', L', hL', hlen', hLs', _⟩ | ⟨hP', _, _⟩
    · have := hV X P' _ hlt hX; simp at this; omega
    · obtain ⟨X, hX⟩ := exists_mem_of_length hlen' (by omega)
      have := hS X P' _ hlt (hLs' X hX); simp at this; omega
    · omega
  · rcases hK with ⟨X, hX⟩ | ⟨hP, L, hL, hlen, hLs, hall⟩ | ⟨hP, hb1, hall⟩ <;>
    rcases hK' with ⟨X', hX'⟩ | ⟨hP', L', hL', hlen', hLs', hall'⟩ | ⟨hP', hb1', hall'⟩
    · exact hM.vote_cons hX hX' (by omega) (by omega)
    · have := hall' _ _ hX; simpa using this
    · subst hP'; have := hall' _ _ hX; simp at this; omega
    · have := hall _ _ hX'; simp at this; omega
    · obtain ⟨Y, hY, hY'⟩ := meet_of_length hL.1 hL.2 hL'.1 hL'.2 (by omega)
      have := (hLs Y hY).symm.trans (hLs' Y hY'); simpa using this
    · omega
    · subst hP; have := hall _ _ hX'; simp at this; omega
    · omega
    · omega

/-- Every decision rests on evidence. -/
theorem ValidAt.decided_ev {M : Facts} (hM : ValidAt c M) {s : Nat} {d : DVal}
    (h : Decided c M s d) : DecEvidence c M s d := by
  have hdec : M (.dec s) = some (.dval d) → DecEvidence c M s d := fun h => by
    have := hM.1 _ _ h
    simpa only [Justified] using this
  rcases h with h|h|⟨X, h⟩
  · exact h
  · exact hdec h
  · have := hM.1 _ _ h
    simp only [Justified] at this
    rcases this.2 with h|h
    · exact h
    · exact hdec h

theorem majProp_unique' {M : Facts} {s : Nat} {id id' : ObjId}
    (h : MajProp c M s id) (h' : MajProp c M s id') : id = id' := by
  obtain ⟨W, hW, hlen, hWp⟩ := h
  obtain ⟨W', hW', hlen', hWp'⟩ := h'
  obtain ⟨X, hX, hX'⟩ := meet_of_length hW.1 hW.2 hW'.1 hW'.2
    (by have := c.two_maj; omega)
  have := (hWp X hX).symm.trans (hWp' X hX'); simpa using this

/-! ## Helper lemmas: monotonicity of the rules -/

theorem MajProp.mono {M M' : Facts} (hle : M.le M') {s : Nat} {id : ObjId}
    (h : MajProp c M s id) : MajProp c M' s id := by
  obtain ⟨W, hW, hl, hp⟩ := h
  exact ⟨W, hW, hl, fun X hX => hle _ _ (hp X hX)⟩

theorem BitQuorum.mono {M M' : Facts} (hle : M.le M') {s p r : Nat} {W : List (Nat × Nat)}
    (h : BitQuorum c M s p r W) : BitQuorum c M' s p r W :=
  ⟨h.1, h.2.1, fun x hx => hle _ _ (h.2.2 x hx)⟩

theorem PropQuorum.mono {M M' : Facts} (hle : M.le M') {s : Nat} {W : List (Nat × ObjId)}
    (h : PropQuorum c M s W) : PropQuorum c M' s W :=
  ⟨h.1, h.2.1, fun x hx => hle _ _ (h.2.2 x hx)⟩

theorem VoteOk.mono {M M' : Facts} (hle : M.le M') {s p b : Nat}
    (h : VoteOk c M s p b) : VoteOk c M' s p b := by
  unfold VoteOk at *
  by_cases hp : p = 0 <;> simp only [hp, ↓reduceIte] at h ⊢
  · rcases h with ⟨hb, id, hm⟩|⟨hb, W, hW, hlt⟩
    · exact Or.inl ⟨hb, id, hm.mono hle⟩
    · exact Or.inr ⟨hb, W, hW.mono hle, hlt⟩
  · obtain ⟨W, hW, hb⟩ := h
    exact ⟨W, hW.mono hle, hb⟩

theorem StateOk.mono {M M' : Facts} (hle : M.le M') {s p b : Nat}
    (h : StateOk c M s p b) : StateOk c M' s p b := by
  obtain ⟨W, hW, hT, hb⟩ := h
  exact ⟨W, hW.mono hle, hT, hb⟩

theorem BitDec.mono {M M' : Facts} (hle : M.le M') {s b : Nat} {d : DVal}
    (h : BitDec c M s b d) : BitDec c M' s b d := by
  obtain ⟨hb, h0, h1⟩ := h
  refine ⟨hb, h0, fun e => ?_⟩
  obtain ⟨id, hid, hm⟩ := h1 e
  exact ⟨id, hid, hm.mono hle⟩

theorem DecEvidence.mono {M M' : Facts} (hle : M.le M') {s : Nat} {d : DVal}
    (h : DecEvidence c M s d) : DecEvidence c M' s d := by
  rcases h with ⟨p, b, L, hL, hlen, hLv, hbd⟩ | ⟨p, b, L, hp, hL, hlen, hLs, hbd⟩ |
    ⟨id, L, hL, hlen, hLp, hd⟩
  · exact Or.inl ⟨p, b, L, hL, hlen, fun X hX => hle _ _ (hLv X hX), hbd.mono hle⟩
  · exact Or.inr (Or.inl ⟨p, b, L, hp, hL, hlen, fun X hX => hle _ _ (hLs X hX), hbd.mono hle⟩)
  · exact Or.inr (Or.inr ⟨id, L, hL, hlen, fun X hX => hle _ _ (hLp X hX), hd⟩)

theorem PropOk.mono {M M' : Facts} (hle : M.le M') {X t : Nat} {id : ObjId}
    (h : PropOk M X t id) : PropOk M' X t id := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun s hs => ?_, fun s hs hp => ?_⟩
  · obtain ⟨i, d, hp, hd⟩ := h1 s hs
    exact ⟨i, d, hle _ _ hp, hle _ _ hd⟩
  · obtain ⟨i, d, hp', hd⟩ := h1 s hs
    rw [hle _ _ hp'] at hp
    rw [hle _ _ hd]
    have := h2 s hs (by rw [hp', hp])
    rwa [hd] at this

theorem Justified.mono {M M' : Facts} (hle : M.le M') {k : FKey} {v : FVal}
    (h : Justified c M k v) : Justified c M' k v := by
  cases k <;> cases v <;> simp only [Justified] at h ⊢
  case pobj.reqs id rs =>
    obtain ⟨hne, hnd, hX, hr⟩ := h
    refine ⟨hne, hnd, hX, fun r hr' => ?_⟩
    obtain ⟨⟨cm, hcm⟩, h2, h3⟩ := hr r hr'
    exact ⟨⟨cm, hle _ _ hcm⟩, h2, hle _ _ h3⟩
  case robj.obj X r id =>
    obtain ⟨hX, rs, hrs, hr⟩ := h
    exact ⟨hX, rs, hle _ _ hrs, hr⟩
  case prop.obj X s id =>
    obtain ⟨hX, ⟨r, hr⟩, hp⟩ := h
    exact ⟨hX, ⟨r, hle _ _ hr⟩, hp.mono hle⟩
  case mydec.dval X s d =>
    obtain ⟨hX, h|h⟩ := h
    · exact ⟨hX, Or.inl (h.mono hle)⟩
    · exact ⟨hX, Or.inr (hle _ _ h)⟩
  case dec.dval s d => exact h.mono hle
  all_goals exact h

/-- A record whose configuration is `c` and valid at it is valid. -/
theorem Valid.of_cfg {M : Facts} (h : M .cfg = some (.cfgv c)) (hok : c.Ok) (hv : ValidAt c M) :
    Valid M := by
  unfold Valid; rw [h]; exact ⟨hok, hv⟩

theorem foldl_robj_other (X : Nat) (id : ObjId) (l : List ReqId) (N : Facts) (k : FKey)
    (hk : ∀ r ∈ l, k ≠ .robj X r) :
    (l.foldl (fun M' r => M'.set (.robj X r) (.obj id)) N) k = N k := by
  induction l generalizing N with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun r hr => hk r (List.mem_cons_of_mem _ hr))]
    simp [Facts.set, hk a (List.mem_cons_self ..)]

theorem foldl_robj_mem (X : Nat) (id : ObjId) (l : List ReqId) (N : Facts) (r : ReqId)
    (hr : r ∈ l) :
    (l.foldl (fun M' r => M'.set (.robj X r) (.obj id)) N) (.robj X r) = some (.obj id) := by
  induction l generalizing N with
  | nil => cases hr
  | cons a l ih =>
    simp only [List.foldl_cons]
    by_cases hl : r ∈ l
    · exact ih _ hl
    · have e : r = a := by
        rcases List.mem_cons.mp hr with e|e
        · exact e
        · exact absurd e hl
      subst e
      rw [foldl_robj_other _ _ _ _ _ (fun r' hr' h => by cases h; exact hl hr')]
      simp [Facts.set]

/-- Recording the configuration first. -/
theorem Valid.setCfg (c : RCfg) (hc : c.Ok) : Valid (Facts.set (fun _ => none) .cfg (.cfgv c)) := by
  refine Valid.of_cfg (by simp [Facts.set]) hc ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k v h
    simp only [Facts.set] at h
    split at h
    · subst_vars; cases h; simp [Justified]
    · cases h
  · intro X s p b h; simp [Facts.set] at h
  · intro X s p b h; simp [Facts.set] at h
  · intro s h; simp [Facts.set] at h
  · intro X s h; simp [Facts.set] at h
  · intro X s h; simp [Facts.set] at h

/-- **Agreement**: the decisions of a slot (any server's, or the recorded one) are the same. -/
theorem agree (M : Facts) (hc : c.Ok) (hM : ValidAt c M) (s : Nat) (d d' : DVal)
    (h : Decided c M s d) (h' : Decided c M s d') : d = d' := by
  obtain ⟨P, b, hE⟩ := hM.ev_summary hc (hM.decided_ev h)
  obtain ⟨P', b', hE'⟩ := hM.ev_summary hc (hM.decided_ev h')
  have e : b = b' := by
    rcases Nat.le_total P P' with hl|hl
    · exact hM.evsum_cmp hc hE hE' hl
    · exact (hM.evsum_cmp hc hE' hE hl).symm
  subst e
  obtain ⟨⟨hb, h0, h1⟩, _⟩ := hE
  obtain ⟨⟨_, h0', h1'⟩, _⟩ := hE'
  rcases (show b = 0 ∨ b = 1 by omega) with rfl|rfl
  · rw [h0 rfl, h0' rfl]
  · obtain ⟨id, rfl, hm⟩ := h1 rfl
    obtain ⟨id', rfl, hm'⟩ := h1' rfl
    rw [majProp_unique' hm hm']

/-- **At most once**: an object decided at two slots is decided at one slot only. -/
theorem atMostOnce (M : Facts) (hc : c.Ok) (hM : ValidAt c M) (s t : Nat) (id : ObjId)
    (hs : M (.dec s) = some (.dval (.obj id))) (ht : M (.dec t) = some (.dval (.obj id))) :
    s = t := by
  have hmaj : ∀ u, M (.dec u) = some (.dval (.obj id)) → MajProp c M u id := by
    intro u hu
    obtain ⟨P, b, ⟨hb, h0, h1⟩, _⟩ := hM.ev_summary hc (hM.decided_ev (Or.inr (Or.inl hu)))
    rcases (show b = 0 ∨ b = 1 by omega) with rfl|rfl
    · cases h0 rfl
    · obtain ⟨id', e, hm⟩ := h1 rfl
      cases e; exact hm
  have key : ∀ s t, M (.dec s) = some (.dval (.obj id)) → M (.dec t) = some (.dval (.obj id)) →
      ¬ s < t := by
    intro s t hs ht hlt
    obtain ⟨W, hW, hlen, hWp⟩ := hmaj s hs
    obtain ⟨W', hW', hlen', hWp'⟩ := hmaj t ht
    obtain ⟨X, hX, hX'⟩ := meet_of_length hW.1 hW.2 hW'.1 hW'.2
      (by have := c.two_maj; omega)
    have hJ := hM.1 _ _ (hWp' X hX')
    simp only [Justified] at hJ
    obtain ⟨_, _, hP1, hP2⟩ := hJ
    obtain ⟨i, d, _, hd⟩ := hP1 s hlt
    have e := agree M hc hM s d (.obj id) (Or.inr (Or.inr ⟨X, hd⟩)) (Or.inr (Or.inl hs))
    subst e
    exact hP2 s hlt (hWp X hX) hd
  rcases Nat.lt_trichotomy s t with h|h|h
  · exact absurd h (key s t hs ht)
  · exact h
  · exact absurd h (key t s ht hs)

/-- **At most once**, per request: a client request is decided at one slot only. -/
theorem atMostOnceReq (M : Facts) (hc : c.Ok) (hM : ValidAt c M) (s t : Nat) (id id' : ObjId)
    (rs rs' : List ReqId) (r : ReqId)
    (hs : M (.dec s) = some (.dval (.obj id))) (ht : M (.dec t) = some (.dval (.obj id')))
    (hr : M (.pobj id) = some (.reqs rs)) (hr' : M (.pobj id') = some (.reqs rs'))
    (hrs : r ∈ rs) (hrs' : r ∈ rs') : s = t ∧ id = id' := by
  have h1 := hM.1 _ _ hr
  have h2 := hM.1 _ _ hr'
  simp only [Justified] at h1 h2
  obtain ⟨_, e1, o1⟩ := h1.2.2.2 r hrs
  obtain ⟨_, e2, o2⟩ := h2.2.2.2 r hrs'
  rw [e2] at o2
  rw [e1] at o1
  have e : id = id' := by
    have := o1.symm.trans o2
    simpa using this
  subst e
  exact ⟨atMostOnce M hc hM s t id hs ht, rfl⟩

/-- An object with a majority of proposals at a slot is unique. -/
theorem majProp_unique (M : Facts) (s : Nat) (id id' : ObjId)
    (h : MajProp c M s id) (h' : MajProp c M s id') : id = id' := by
  exact majProp_unique' h h'

/-- Adding a fact justified by `M` keeps `M` valid (the rules are monotone), for the facts
recorded alone (not `cfg`, recorded first by `Valid.setCfg`; not `pobj`/`robj`, recorded together
by `Valid.insertObj`; not `mydec`, recorded with or after `dec`). -/
theorem Valid.insert (M : Facts) (hc : CfgOf M c) (hM : Valid M) (k : FKey) (v : FVal)
    (hk : M k = none) (hj : Justified c M k v)
    (hobj : k ≠ .cfg ∧ ∀ id X r, k ≠ .pobj id ∧ k ≠ .robj X r)
    (hst : ∀ X s p b, k = .st X s p → v = .bit b → p ≥ 1 ∧ StateOk c M s (p - 1) b)
    (hvt : ∀ X s p b, k = .vt X s p → v = .bit b → VoteOk c M s p b)
    (hdec : ∀ s, k = .dec (s + 1) → M (.dec s) ≠ none)
    (hmy : ∀ X s, k = .mydec X s → M (.dec s) ≠ none ∧ (s = 0 ∨ M (.mydec X (s - 1)) ≠ none)) :
    Valid (M.set k v) := by
  have hle := Facts.le_insert M k v hk
  obtain ⟨hcOk, hJ, hS, hV, hD, hMy, hMD⟩ := hM.at hc
  have hcfg : (M.set k v) .cfg = some (.cfgv c) := by
    simp only [Facts.set, Ne.symm hobj.1, ↓reduceIte]; exact hc
  refine Valid.of_cfg hcfg hcOk ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k' v' h
    simp only [Facts.set] at h
    split at h
    · cases h; subst_vars; exact hj.mono hle
    · exact (hJ _ _ h).mono hle
  · intro X s p b h
    simp only [Facts.set] at h
    split at h
    · cases h; rename_i e
      obtain ⟨h1, h2⟩ := hst X s p b e.symm rfl
      exact ⟨h1, h2.mono hle⟩
    · obtain ⟨h1, h2⟩ := hS _ _ _ _ h
      exact ⟨h1, h2.mono hle⟩
  · intro X s p b h
    simp only [Facts.set] at h
    split at h
    · cases h; rename_i e
      exact (hvt X s p b e.symm rfl).mono hle
    · exact (hV _ _ _ _ h).mono hle
  · intro s h
    by_cases e : FKey.dec (s + 1) = k
    · exact Facts.le_ne_none hle (hdec s e.symm)
    · simp only [Facts.set, e, ↓reduceIte] at h
      exact Facts.le_ne_none hle (hD s h)
  · intro X s h
    by_cases e : FKey.mydec X (s + 1) = k
    · have := (hmy X (s + 1) e.symm).2
      simp only [Nat.add_sub_cancel, Nat.add_one_ne_zero, false_or] at this
      exact Facts.le_ne_none hle this
    · simp only [Facts.set, e, ↓reduceIte] at h
      exact Facts.le_ne_none hle (hMy X s h)
  · intro X s h
    by_cases e : FKey.mydec X s = k
    · exact Facts.le_ne_none hle (hmy X s e.symm).1
    · simp only [Facts.set, e, ↓reduceIte] at h
      exact Facts.le_ne_none hle (hMD X s h)

/-- Recording a new object `id` of proxy `id.1` carrying the registered requests `rs` (and, for
each, that it is in `id`). -/
theorem Valid.insertObj (M : Facts) (hc : CfgOf M c) (hM : Valid M) (id : ObjId)
    (rs : List ReqId) (hid : M (.pobj id) = none) (hne : rs ≠ []) (hnd : rs.Nodup)
    (hX : id.1 < c.n)
    (hr : ∀ r ∈ rs, M (.robj id.1 r) = none ∧ (∃ cm, M (.reg r) = some (.cmd cm)) ∧
      id.1 = r.1 % c.n) :
    Valid (rs.foldl (fun M' r => M'.set (.robj id.1 r) (.obj id)) (M.set (.pobj id) (.reqs rs))) := by
  obtain ⟨hcOk, hJ, hS, hV, hD, hMy, hMD⟩ := hM.at hc
  have hF1 : ∀ r ∈ rs, (rs.foldl (fun M' r => M'.set (.robj id.1 r) (.obj id))
      (M.set (.pobj id) (.reqs rs))) (.robj id.1 r) = some (.obj id) :=
    fun r h => foldl_robj_mem _ _ _ _ _ h
  have hF2 : ∀ k, (∀ r ∈ rs, k ≠ .robj id.1 r) → k ≠ .pobj id →
      (rs.foldl (fun M' r => M'.set (.robj id.1 r) (.obj id))
        (M.set (.pobj id) (.reqs rs))) k = M k := by
    intro k h1 h2
    rw [foldl_robj_other _ _ _ _ _ h1]
    simp [Facts.set, h2]
  have hF3 : (rs.foldl (fun M' r => M'.set (.robj id.1 r) (.obj id))
      (M.set (.pobj id) (.reqs rs))) (.pobj id) = some (.reqs rs) := by
    rw [foldl_robj_other _ _ _ _ _ (fun r _ h => by cases h)]
    simp [Facts.set]
  generalize rs.foldl (fun M' r => M'.set (.robj id.1 r) (.obj id))
    (M.set (.pobj id) (.reqs rs)) = F at hF1 hF2 hF3 ⊢
  have hle : M.le F := by
    intro k v h
    rw [hF2 k (fun r hr' e => by subst e; rw [(hr r hr').1] at h; cases h)
      (fun e => by subst e; rw [hid] at h; cases h)]
    exact h
  have hsame : ∀ k, (∀ X r, k ≠ .robj X r) → k ≠ .pobj id → F k = M k :=
    fun k h1 h2 => hF2 k (fun r _ => h1 _ r) h2
  refine Valid.of_cfg (c := c)
    (by rw [hsame .cfg (fun _ _ h => by cases h) (fun h => by cases h)]; exact hc) hcOk
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k v h
    by_cases h1 : ∃ r ∈ rs, k = .robj id.1 r
    · obtain ⟨r, hrr, rfl⟩ := h1
      rw [hF1 r hrr] at h; cases h
      simp only [Justified]
      exact ⟨by trivial, rs, hF3, hrr⟩
    · by_cases h2 : k = .pobj id
      · subst h2; rw [hF3] at h; cases h
        simp only [Justified]
        refine ⟨hne, hnd, hX, fun r hrr => ?_⟩
        obtain ⟨_, ⟨cm, hcm⟩, hmod⟩ := hr r hrr
        exact ⟨⟨cm, hle _ _ hcm⟩, hmod, hF1 r hrr⟩
      · rw [hF2 k (fun r hrr e => h1 ⟨r, hrr, e⟩) h2] at h
        exact (hJ _ _ h).mono hle
  · intro X s p b h
    rw [hsame _ (fun _ _ e => by cases e) (fun e => by cases e)] at h
    obtain ⟨h1, h2⟩ := hS _ _ _ _ h
    exact ⟨h1, h2.mono hle⟩
  · intro X s p b h
    rw [hsame _ (fun _ _ e => by cases e) (fun e => by cases e)] at h
    exact (hV _ _ _ _ h).mono hle
  · intro s h
    rw [hsame _ (fun _ _ e => by cases e) (fun e => by cases e)] at h ⊢
    exact hD s h
  · intro X s h
    rw [hsame _ (fun _ _ e => by cases e) (fun e => by cases e)] at h ⊢
    exact hMy X s h
  · intro X s h
    rw [hsame _ (fun _ _ e => by cases e) (fun e => by cases e)] at h ⊢
    exact hMD X s h

end props

end Perennial.rabia.model
