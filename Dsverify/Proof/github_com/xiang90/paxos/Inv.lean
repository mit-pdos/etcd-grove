/-
Ported from dsverify-lab examples/paxos/proof/Paxos/Proof/Inv.lean (lab master 7a84fb35; notes/dsv-paxos.md).

The Paxos hub (stage 1 interface, frozen at `stage1-frozen`): the deployment's agents, the
protocol's ghost state, its invariant (in full), what every message means (`msgOK`), the
client's slots (helping), and the laws every agent's proof uses. Nothing outside this file
unfolds `paxosInv`, `PaxosOK` or the slots; the agents use the laws.

**The model.** For each acceptor `a ∈ {1,2,3}`: its state `AccState` (promised number `p`, the
accepted proposal `(k, w)`, `k = 0` for none: the heap fields `promised`, `accept`), the
proposals it ever accepted (`acc : (a, n) ↦ v`), and the promises it ever made
(`pf : (a, n) ↦ (k, w)`: it promised `n` reporting its accepted `(k, w)`). The issued proposals
(`props : n ↦ w`, one value per number), the registered clients (`reg : c ↦ input`), and the
register's state `d` (the decided value). Numbers are Go `int`s, compared signed (`sint.Z`).

**The invariant** (`PaxosOK`): accepted proposals were issued and are at most the acceptor's
current accepted number, which is at most its promise; a promise of `n` reports the highest
accepted proposal below `n`; every issued proposal `(n, w)` is safe: no other value `v` is
choosable at any `m < n` (`choosable`: some majority each of whose members accepted `(m, v)`
or has not promised past `m`); every issued value is some registered client's input; `d` is
`none` iff nothing is chosen, else a chosen value. Agreement (`chosen_agree`) follows.

**Ownership.** `inv paxosN (paxosInv Γ)` is allocated at the start (`paxos_alloc`). Acceptor `a`
holds `stOwn Γ a s` (the ghost map's element for its state). The client node holds
`own_state Γ d` (half of `dec`; the other half is in the invariant), and per client `c` the
tokens `rtok c` (register once), `ptok (1001 + c)` (issue one proposal) and `dtok c` (take the
slot's receipt once). The invariant holds the tokens of what was done.

**Helping.** Client `c`'s call puts its atomic update in a slot invariant `slotN c`
(`slotContent`) and registers it (`inv_register`); the acceptor step that first makes a value
chosen commits the update of a client whose input it is (`inv_accept`); a client that returns
`(w, true)` commits there, or takes the receipt (`inv_return`).
-/
module

public import Dsverify.Proof.github_com.xiang90.paxos.Net

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace github_com.xiang90.paxos

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## The deployment's agents -/

/-- Acceptor ids (nodes 1..3). -/
def accIds : List w64 := [W64 1, W64 2, W64 3]
/-- Proposer ids (`netProposerId c = 1001 + c`, on node 0). -/
def propIds : List w64 := [W64 1001, W64 1002, W64 1003, W64 1004]
/-- Learner ids (`netLearnerId j = 2001 + j`, nodes 4, 5). -/
def lrnIds : List w64 := [W64 2001, W64 2002]
/-- Client boxes (`netBoxId c = 3001 + c`, on node 0). -/
def boxIds : List w64 := [W64 3001, W64 3002, W64 3003, W64 3004]

/-- The proposer id in a proposal number (`n = lastSeq<<16 | id`, `id < 2^16`). -/
def lowId (n : w64) : w64 := n &&& W64 0xffff

/-! ## The pure model -/

/-- An acceptor's state: promised number, accepted number (0: none), accepted value. -/
structure AccState where
  p : w64
  k : w64
  w : GoString
deriving DecidableEq

instance AccState.countable : Pos.Countable AccState :=
  .ofInjective (fun s => Pos.Countable.encode (s.p, s.k, s.w))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      subst h1 h2 h3; rfl)

/-- An acceptor's initial state (`promised: message{}`, `accept` the zero message). -/
def AccState.init : AccState := ⟨W64 0, W64 0, []⟩

abbrev AccMap := GMap (w64 × w64) GoString
abbrev PfMap := GMap (w64 × w64) (w64 × GoString)
abbrev PropMap := GMap w64 GoString
abbrev RegMap := GMap w64 GoString
abbrev StMap := GMap w64 AccState

/-- Acceptor `a` accepted `(m, v)`, or has not promised past `m` (so it still may). -/
def okFor (acc : AccMap) (st : StMap) (a m : w64) (v : GoString) : Prop :=
  acc !! (a, m) = some v ∨ ∃ s, st !! a = some s ∧ sint.Z s.p ≤ sint.Z m

/-- `(m, v)` is choosable: a majority (two distinct acceptors) each accepted it or still may. -/
def choosable (acc : AccMap) (st : StMap) (m : w64) (v : GoString) : Prop :=
  ∃ a b, a ∈ accIds ∧ b ∈ accIds ∧ a ≠ b ∧ okFor acc st a m v ∧ okFor acc st b m v

/-- `(m, v)` is chosen: a majority accepted it. -/
def chosen (acc : AccMap) (m : w64) (v : GoString) : Prop :=
  ∃ a b, a ∈ accIds ∧ b ∈ accIds ∧ a ≠ b ∧ acc !! (a, m) = some v ∧ acc !! (b, m) = some v

/-- An issued proposal `(n, w)` is safe: no other value is choosable below `n`. -/
def Safe (acc : AccMap) (st : StMap) (n : w64) (w : GoString) : Prop :=
  ∀ m v, sint.Z m < sint.Z n → v ≠ w → ¬ choosable acc st m v

/-- The protocol's invariant on the ghost model. -/
structure PaxosOK (acc : AccMap) (pf : PfMap) (props : PropMap) (reg : RegMap) (st : StMap)
    (d : Option GoString) : Prop where
  st_dom : ∀ a, (st !! a).isSome ↔ a ∈ accIds
  st_wf : ∀ a s, st !! a = some s →
    0 ≤ sint.Z s.k ∧ sint.Z s.k ≤ sint.Z s.p ∧ (s.k ≠ W64 0 → acc !! (a, s.k) = some s.w)
  acc_wf : ∀ a n v, acc !! (a, n) = some v →
    a ∈ accIds ∧ props !! n = some v ∧ 0 < sint.Z n ∧
      ∃ s, st !! a = some s ∧ sint.Z n ≤ sint.Z s.k
  pf_wf : ∀ a n k w, pf !! (a, n) = some (k, w) →
    0 < sint.Z n ∧ 0 ≤ sint.Z k ∧ sint.Z k < sint.Z n ∧
      (∃ s, st !! a = some s ∧ sint.Z n ≤ sint.Z s.p) ∧
      (k ≠ W64 0 → acc !! (a, k) = some w) ∧
      (∀ m v, acc !! (a, m) = some v → sint.Z m < sint.Z n → sint.Z m ≤ sint.Z k)
  props_wf : ∀ n w, props !! n = some w →
    0 < sint.Z n ∧ (∃ c, reg !! c = some w) ∧ Safe acc st n w
  dec_none : d = none → ∀ m v, ¬ chosen acc m v
  dec_some : ∀ x, d = some x → ∃ m, chosen acc m x

/-! ### Pure helpers -/

theorem sintZ_inj {m m' : w64} (h : sint.Z m = sint.Z m') : m = m' := BitVec.toInt_inj.mp h

theorem chosen_choosable {acc : AccMap} {st m v} (h : chosen acc m v) : choosable acc st m v := by
  obtain ⟨a, b, ha, hb, hab, h1, h2⟩ := h
  exact ⟨a, b, ha, hb, hab, .inl h1, .inl h2⟩

/-- Agreement: two chosen proposals have the same value. -/
theorem chosen_agree {acc pf props reg st d} (H : PaxosOK acc pf props reg st d)
    (m m' : w64) (v v' : GoString) (h : chosen acc m v) (h' : chosen acc m' v') : v = v' := by
  have key : ∀ m m' v v', sint.Z m ≤ sint.Z m' → chosen acc m v → chosen acc m' v' → v = v' := by
    intro m m' v v' hle h h'
    obtain ⟨a, b, ha, hb, hab, h1, h2⟩ := h
    obtain ⟨a', b', ha', hb', hab', h1', h2'⟩ := h'
    obtain ⟨-, hp, -, -⟩ := H.acc_wf _ _ _ h1
    obtain ⟨-, hp', -, -⟩ := H.acc_wf _ _ _ h1'
    rcases Int.lt_or_eq_of_le hle with hlt | heq
    · obtain ⟨-, -, hS⟩ := H.props_wf _ _ hp'
      exact Classical.byContradiction fun hne => hS m v hlt hne ⟨a, b, ha, hb, hab, .inl h1, .inl h2⟩
    · rw [sintZ_inj heq] at hp; rw [hp] at hp'; exact Option.some.inj hp'
  rcases Int.le_total (sint.Z m) (sint.Z m') with hle | hle
  · exact key m m' v v' hle h h'
  · exact (key m' m v' v hle h' h).symm

/-! ### Preservation of `PaxosOK` (pure helpers of the laws) -/

theorem Safe_of {acc acc' : AccMap} {st st' : StMap}
    (h : ∀ a m v, okFor acc' st' a m v → okFor acc st a m v) {n w} (hS : Safe acc st n w) :
    Safe acc' st' n w := by
  intro m v hm hv ⟨a, b, ha, hb, hab, h1, h2⟩
  exact hS m v hm hv ⟨a, b, ha, hb, hab, h a m v h1, h b m v h2⟩

theorem PaxosOK_promise {acc pf props reg st d} (H : PaxosOK acc pf props reg st d)
    {a n : w64} {s : AccState} (hs : st !! a = some s) (hn : sint.Z s.p < sint.Z n) :
    pf !! (a, n) = none ∧
    PaxosOK acc (<[(a, n) := (s.k, s.w)]> pf) props reg (<[a := { s with p := n }]> st) d := by
  have hwf := H.st_wf a s hs
  have hstl : ∀ b t, (<[a := { s with p := n }]> st) !! b = some t ↔
      (a = b ∧ { s with p := n } = t) ∨ (a ≠ b ∧ st !! b = some t) :=
    fun b t => GMap.lookup_insert_Some _ _ _ _ _
  constructor
  · cases hp : pf !! (a, n) with
    | none => rfl
    | some kw =>
      obtain ⟨-, -, -, ⟨t, ht, hle⟩, -⟩ := H.pf_wf a n kw.1 kw.2 hp
      rw [hs] at ht; cases ht; omega
  constructor
  · intro b
    rw [← H.st_dom b]
    by_cases hab : a = b
    · subst hab; simp [hs]
    · simp [hab]
  · intro b t ht
    rcases (hstl b t).mp ht with ⟨rfl, rfl⟩ | ⟨-, ht⟩
    · exact ⟨hwf.1, by simp only; omega, hwf.2.2⟩
    · exact H.st_wf b t ht
  · intro b m v hv
    obtain ⟨hb, hp, hm, t, ht, hle⟩ := H.acc_wf b m v hv
    refine ⟨hb, hp, hm, ?_⟩
    by_cases hab : a = b
    · subst hab; rw [hs] at ht; cases ht
      exact ⟨_, (hstl a _).mpr (.inl ⟨rfl, rfl⟩), hle⟩
    · exact ⟨t, (hstl b t).mpr (.inr ⟨hab, ht⟩), hle⟩
  · intro b m k w hp
    rcases GMap.lookup_insert_Some _ _ _ _ _ |>.mp hp with ⟨heq, hkw⟩ | ⟨hne, hp⟩
    · cases heq; cases hkw
      refine ⟨?_, hwf.1, ?_, ⟨_, (hstl a _).mpr (.inl ⟨rfl, rfl⟩), by simp⟩,
        hwf.2.2, ?_⟩
      · omega
      · omega
      intro m v hv _
      obtain ⟨-, -, -, t, ht, hle⟩ := H.acc_wf a m v hv
      rw [hs] at ht; cases ht; exact hle
    · obtain ⟨h1, h2, h3, ⟨t, ht, hle⟩, h5, h6⟩ := H.pf_wf b m k w hp
      refine ⟨h1, h2, h3, ?_, h5, h6⟩
      by_cases hab : a = b
      · subst hab; rw [hs] at ht; cases ht
        exact ⟨_, (hstl a _).mpr (.inl ⟨rfl, rfl⟩), by simp only; omega⟩
      · exact ⟨t, (hstl b t).mpr (.inr ⟨hab, ht⟩), hle⟩
  · intro m w hp
    obtain ⟨h1, h2, h3⟩ := H.props_wf m w hp
    refine ⟨h1, h2, Safe_of ?_ h3⟩
    intro b m v hok
    rcases hok with h | ⟨t, ht, hle⟩
    · exact .inl h
    · right
      rcases (hstl b t).mp ht with ⟨rfl, rfl⟩ | ⟨-, ht⟩
      · exact ⟨s, hs, by simp only at hle; omega⟩
      · exact ⟨t, ht, hle⟩
  · exact H.dec_none
  · exact H.dec_some

theorem chosen_insert {acc : AccMap} {a n m : w64} {v x : GoString}
    (h : chosen (<[(a, n) := v]> acc) m x) : chosen acc m x ∨ (m = n ∧ x = v) := by
  obtain ⟨b, c, hb, hc, hbc, h1, h2⟩ := h
  rcases GMap.lookup_insert_Some _ _ _ _ _ |>.mp h1 with ⟨heq, hx⟩ | ⟨hne1, h1⟩
  · cases heq; exact .inr ⟨rfl, hx.symm⟩
  rcases GMap.lookup_insert_Some _ _ _ _ _ |>.mp h2 with ⟨heq, hx⟩ | ⟨hne2, h2⟩
  · cases heq; exact .inr ⟨rfl, hx.symm⟩
  exact .inl ⟨b, c, hb, hc, hbc, h1, h2⟩

theorem chosen_mono {acc acc' : AccMap} (hm : ∀ k x, acc !! k = some x → acc' !! k = some x)
    {m x} (h : chosen acc m x) : chosen acc' m x := by
  obtain ⟨b, c, hb, hc, hbc, h1, h2⟩ := h
  exact ⟨b, c, hb, hc, hbc, hm _ _ h1, hm _ _ h2⟩

theorem PaxosOK_accept {acc pf props reg st d} (H : PaxosOK acc pf props reg st d)
    {a n : w64} {v : GoString} {s : AccState} (hs : st !! a = some s) (hn : s.p = n)
    (hv : props !! n = some v) (d' : Option GoString)
    (hd1 : d' = none → ∀ m x, ¬ chosen (<[(a, n) := v]> acc) m x)
    (hd2 : ∀ x, d' = some x → ∃ m, chosen (<[(a, n) := v]> acc) m x) :
    PaxosOK (<[(a, n) := v]> acc) pf props reg (<[a := { s with k := n, w := v }]> st) d' := by
  have hwf := H.st_wf a s hs
  have hn' : sint.Z s.p = sint.Z n := by rw [hn]
  have hnpos := (H.props_wf n v hv).1
  have hstl : ∀ b t, (<[a := { s with k := n, w := v }]> st) !! b = some t ↔
      (a = b ∧ { s with k := n, w := v } = t) ∨ (a ≠ b ∧ st !! b = some t) :=
    fun b t => GMap.lookup_insert_Some _ _ _ _ _
  have hmono : ∀ k x, acc !! k = some x → (<[(a, n) := v]> acc) !! k = some x := by
    intro k x hk
    rcases k with ⟨b, m⟩
    by_cases heq : (a, n) = (b, m)
    · cases heq
      obtain ⟨-, hp, -⟩ := H.acc_wf a n x hk
      rw [hv] at hp; cases hp
      exact GMap.lookup_insert_eq _ _ _
    · rw [GMap.lookup_insert_ne _ _ heq]; exact hk
  constructor
  · intro b
    rw [← H.st_dom b]
    by_cases hab : a = b
    · subst hab; simp [hs]
    · simp [hab]
  · intro b t ht
    rcases (hstl b t).mp ht with ⟨rfl, rfl⟩ | ⟨-, ht⟩
    · refine ⟨by simp only; omega, by simp only; omega, fun _ => GMap.lookup_insert_eq _ _ _⟩
    · obtain ⟨h1, h2, h3⟩ := H.st_wf b t ht
      exact ⟨h1, h2, fun h => hmono _ _ (h3 h)⟩
  · intro b m x hx
    rcases GMap.lookup_insert_Some _ _ _ _ _ |>.mp hx with ⟨heq, rfl⟩ | ⟨-, hx⟩
    · cases heq
      exact ⟨(H.st_dom a).mp (by simp [hs]), hv, hnpos,
        _, (hstl a _).mpr (.inl ⟨rfl, rfl⟩), by simp⟩
    obtain ⟨hb, hp, hm, t, ht, hle⟩ := H.acc_wf b m x hx
    refine ⟨hb, hp, hm, ?_⟩
    by_cases hab : a = b
    · subst hab; rw [hs] at ht; cases ht
      exact ⟨_, (hstl a _).mpr (.inl ⟨rfl, rfl⟩), by simp only; omega⟩
    · exact ⟨t, (hstl b t).mpr (.inr ⟨hab, ht⟩), hle⟩
  · intro b m k w hp
    obtain ⟨h1, h2, h3, ⟨t, ht, hle⟩, h5, h6⟩ := H.pf_wf b m k w hp
    refine ⟨h1, h2, h3, ?_, fun h => hmono _ _ (h5 h), ?_⟩
    · by_cases hab : a = b
      · subst hab; rw [hs] at ht; cases ht
        exact ⟨_, (hstl a _).mpr (.inl ⟨rfl, rfl⟩), by simp only; omega⟩
      · exact ⟨t, (hstl b t).mpr (.inr ⟨hab, ht⟩), hle⟩
    · intro m' x hx hlt
      rcases GMap.lookup_insert_Some _ _ _ _ _ |>.mp hx with ⟨heq, -⟩ | ⟨-, hx⟩
      · cases heq; rw [hs] at ht; cases ht; omega
      · exact h6 m' x hx hlt
  · intro m w hp
    obtain ⟨h1, h2, h3⟩ := H.props_wf m w hp
    refine ⟨h1, h2, Safe_of ?_ h3⟩
    intro b m x hok
    rcases hok with h | ⟨t, ht, hle⟩
    · rcases GMap.lookup_insert_Some _ _ _ _ _ |>.mp h with ⟨heq, -⟩ | ⟨-, h⟩
      · cases heq; exact .inr ⟨s, hs, by omega⟩
      · exact .inl h
    · right
      rcases (hstl b t).mp ht with ⟨rfl, rfl⟩ | ⟨-, ht⟩
      · exact ⟨s, hs, by simp only at hle; omega⟩
      · exact ⟨t, ht, hle⟩
  · exact hd1
  · exact hd2

theorem quorum {a b a1 a2 : w64} (ha : a ∈ accIds) (hb : b ∈ accIds) (hab : a ≠ b)
    (ha1 : a1 ∈ accIds) (ha2 : a2 ∈ accIds) (h12 : a1 ≠ a2) :
    ∃ x, (x = a ∨ x = b) ∧ (x = a1 ∨ x = a2) := by
  simp only [accIds, List.mem_cons, List.not_mem_nil, or_false] at ha hb ha1 ha2
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    rcases ha1 with rfl | rfl | rfl <;> rcases ha2 with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hab
    | exact absurd rfl h12
    | exact ⟨_, .inl rfl, .inl rfl⟩
    | exact ⟨_, .inl rfl, .inr rfl⟩
    | exact ⟨_, .inr rfl, .inl rfl⟩
    | exact ⟨_, .inr rfl, .inr rfl⟩

theorem issue_safe {acc pf props reg st d} (H : PaxosOK acc pf props reg st d)
    {n vN a1 a2 k1 k2 : w64} {w w1 w2 : GoString} (ha1 : a1 ∈ accIds) (ha2 : a2 ∈ accIds)
    (h12 : a1 ≠ a2) (hp1 : pf !! (a1, n) = some (k1, w1)) (hp2 : pf !! (a2, n) = some (k2, w2))
    (hk1 : sint.Z k1 ≤ sint.Z vN) (hk2 : sint.Z k2 ≤ sint.Z vN)
    (hw : vN ≠ W64 0 → props !! vN = some w) : Safe acc st n w := by
  intro m v hm hvw ⟨a, b, ha, hb, hab, h1, h2⟩
  obtain ⟨x, hx, hx'⟩ := quorum ha hb hab ha1 ha2 h12
  have hok : okFor acc st x m v := by rcases hx with rfl | rfl <;> assumption
  have hpf : ∃ k w', pf !! (x, n) = some (k, w') ∧ sint.Z k ≤ sint.Z vN := by
    rcases hx' with rfl | rfl
    · exact ⟨_, _, hp1, hk1⟩
    · exact ⟨_, _, hp2, hk2⟩
  obtain ⟨k, w', hp, hk⟩ := hpf
  obtain ⟨-, -, -, ⟨t, ht, hle⟩, -, h6⟩ := H.pf_wf x n k w' hp
  rcases hok with hacc | ⟨t', ht', hle'⟩
  · have hmk := h6 m v hacc hm
    obtain ⟨-, hpm, hmpos, -⟩ := H.acc_wf x m v hacc
    by_cases hv0 : vN = W64 0
    · subst hv0; simp at hk; omega
    · have hpv := hw hv0
      rcases Int.lt_or_eq_of_le (Int.le_trans hmk hk) with hlt | heq
      · obtain ⟨-, -, hS⟩ := H.props_wf vN w hpv
        exact hS m v hlt hvw ⟨a, b, ha, hb, hab, h1, h2⟩
      · rw [sintZ_inj heq, hpv] at hpm; cases hpm; exact hvw rfl
  · rw [ht] at ht'; cases ht'; omega

theorem PaxosOK_issue {acc pf props reg st d} (H : PaxosOK acc pf props reg st d)
    {n : w64} {w : GoString} (hfresh : props !! n = none) (hpos : 0 < sint.Z n)
    (hreg : ∃ c, reg !! c = some w) (hsafe : Safe acc st n w) :
    PaxosOK acc pf (<[n := w]> props) reg st d := by
  refine ⟨H.st_dom, H.st_wf, ?_, H.pf_wf, ?_, H.dec_none, H.dec_some⟩
  · intro b m x hx
    obtain ⟨hb, hp, hrest⟩ := H.acc_wf b m x hx
    refine ⟨hb, ?_, hrest⟩
    have hne : n ≠ m := by rintro rfl; rw [hfresh] at hp; cases hp
    rw [GMap.lookup_insert_ne _ _ hne]; exact hp
  · intro m x hp
    rcases GMap.lookup_insert_Some _ _ _ _ _ |>.mp hp with ⟨rfl, rfl⟩ | ⟨-, hp⟩
    · exact ⟨hpos, hreg, hsafe⟩
    · exact H.props_wf m x hp

theorem PaxosOK_register {acc pf props reg st d} (H : PaxosOK acc pf props reg st d)
    {c : w64} {v : GoString} (hfresh : reg !! c = none) :
    PaxosOK acc pf props (<[c := v]> reg) st d := by
  refine ⟨H.st_dom, H.st_wf, H.acc_wf, H.pf_wf, ?_, H.dec_none, H.dec_some⟩
  intro m x hp
  obtain ⟨h1, ⟨c', hc'⟩, h3⟩ := H.props_wf m x hp
  refine ⟨h1, ⟨c', ?_⟩, h3⟩
  have hne : c ≠ c' := by rintro rfl; rw [hfresh] at hc'; cases hc'
  rw [GMap.lookup_insert_ne _ _ hne]; exact hc'

/-! ## Ghost state -/

/-- The ghost names of the protocol. -/
structure Names where
  /-- `ghost_map (w64 × w64) GoString`: accepted proposals `(a, n) ↦□ v` -/
  acc : GName
  /-- `ghost_map (w64 × w64) (w64 × GoString)`: promises `(a, n) ↦□ (k, w)` -/
  pf : GName
  /-- `ghost_map w64 GoString`: issued proposals `n ↦□ w` -/
  props : GName
  /-- `ghost_map w64 Unit`: proposer tokens, by proposer id -/
  ptok : GName
  /-- `ghost_map w64 GoString`: registered clients `c ↦□ input` -/
  reg : GName
  /-- `ghost_map w64 Unit`: registration tokens, by client -/
  rtok : GName
  /-- `ghost_map w64 Unit`: receipt tokens, by client -/
  dtok : GName
  /-- `ghost_map w64 AccState`: each acceptor's state -/
  st : GName
  /-- `ghostVar (Option GoString)`: the register (halves: invariant, `own_state`) -/
  dec : GName
  /-- `ghost_map Unit GoString`: the decided value, once (`shotW`) -/
  shot : GName

/-- The paxos invariant's namespace, a client slot's (under `slotsN`), disjoint from each other. -/
def paxosN : Namespace := ndot nroot "paxos"
def slotsN : Namespace := ndot nroot "paxos_slot"
def slotN (c : w64) : Namespace := ndot slotsN c

/-- The invariants a client's update may find open when it fires (an acceptor's step, inside the
paxos invariant and a slot's): `remote`'s `RBase.Eop` of the register. -/
def paxosEop : CoPset := ↑paxosN ∪ ↑slotsN

/-- The write-once register's step on input `v` (its state and output): linkv's `PendSpec.step` of
the register, every proposal a write. -/
def woStep (v : GoString) (σ : Option GoString) : Option GoString × GoString :=
  match σ with
  | none => (some v, v)
  | some x => (some x, x)

section ghost

variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF]

/-- The register's abstract state, the half outside the invariant (`remote`'s `RBase.sysState` of
the register, kept by its pending library). -/
def own_state (Γ : Names) (σ : Option GoString) : IProp GF := ghostVar Γ.dec (1 : Qp).half σ

/-- Acceptor `a`'s state (held by its node). -/
def stOwn (Γ : Names) (a : w64) (s : AccState) : IProp GF := a ↪[Γ.st] s

def ptok (Γ : Names) (id : w64) : IProp GF := id ↪[Γ.ptok] ()
def rtok (Γ : Names) (c : w64) : IProp GF := c ↪[Γ.rtok] ()
def dtok (Γ : Names) (c : w64) : IProp GF := c ↪[Γ.dtok] ()

/-- Witnesses (persistent). -/
def accW (Γ : Names) (a n : w64) (v : GoString) : IProp GF := (a, n) ↪[Γ.acc]□ v
def pfW (Γ : Names) (a n k : w64) (w : GoString) : IProp GF := (a, n) ↪[Γ.pf]□ (k, w)
def propW (Γ : Names) (n : w64) (w : GoString) : IProp GF := n ↪[Γ.props]□ w
def regW (Γ : Names) (c : w64) (v : GoString) : IProp GF := c ↪[Γ.reg]□ v
def shotW (Γ : Names) (x : GoString) : IProp GF := () ↪[Γ.shot]□ x

/-- `v` is chosen: two distinct acceptors accepted it at one number. -/
def chosenW (Γ : Names) (v : GoString) : IProp GF :=
  iprop(∃ m a b, ⌜a ∈ accIds ∧ b ∈ accIds ∧ a ≠ b⌝ ∗ accW Γ a m v ∗ accW Γ b m v)

/-- Client `c`'s update for input `v` with the caller's postcondition `Φ` of the output: the
linearization point of `remote` (`remote.lin` of the register, one-shot: a proposal is a write). -/
def opAU (Γ : Names) (v : GoString) (Φ : GoString → IProp GF) : IProp GF :=
  iprop(|={⊤ \ paxosEop, ∅}=> ∃ σ, own_state Γ σ ∗
    (own_state Γ (woStep v σ).1 ={∅, ⊤ \ paxosEop}=∗ Φ (woStep v σ).2))

/-- Client `c`'s slot: its update, pending; or committed (with the decided value `o`) and its
receipt `Φ o`, or the receipt taken (`dtok c`). -/
def slotContent (Γ : Names) (c : w64) (v : GoString) (Φ : GoString → IProp GF) : IProp GF :=
  iprop(opAU Γ v Φ ∨ ∃ o, shotW Γ o ∗ (Φ o ∨ dtok Γ c))

/-- Client `c`'s slot invariant, for some commit postcondition (persistent). -/
def slotReg (Γ : Names) (c : w64) (v : GoString) : IProp GF :=
  iprop(□ ∃ Q, inv (slotN c) (slotContent Γ c v Q))

def shotMap (d : Option GoString) : GMap Unit GoString :=
  match d with
  | none => ∅
  | some x => {[() := x]}

/-- The protocol's invariant. -/
def paxosInv (Γ : Names) : IProp GF :=
  iprop(∃ (acc : AccMap) (pf : PfMap) (props : PropMap) (reg : RegMap) (st : StMap)
      (d : Option GoString),
    ghostMapAuth Γ.acc 1 acc ∗ ghostMapAuth Γ.pf 1 pf ∗ ghostMapAuth Γ.props 1 props ∗
    ghostMapAuth Γ.reg 1 reg ∗ ghostMapAuth Γ.st 1 st ∗ ghostVar Γ.dec (1 : Qp).half d ∗
    ghostMapAuth Γ.shot 1 (shotMap d) ∗
    ([∗map] an ↦ v ∈ acc, accW Γ an.1 an.2 v) ∗
    ([∗map] an ↦ kw ∈ pf, pfW Γ an.1 an.2 kw.1 kw.2) ∗
    ([∗map] n ↦ w ∈ props, propW Γ n w) ∗
    (match d with | some x => shotW Γ x | none => True) ∗
    ([∗map] n ↦ _w ∈ props, ptok Γ (lowId n)) ∗
    ([∗map] c ↦ v ∈ reg, rtok Γ c ∗ slotReg Γ c v) ∗
    ⌜PaxosOK acc pf props reg st d⌝)

/-- The invariant, allocated (persistent). -/
def isPaxos (Γ : Names) : IProp GF := inv paxosN (paxosInv Γ)

instance isPaxos_persistent (Γ : Names) : Persistent (isPaxos (GF := GF) Γ) := by
  unfold isPaxos; infer_instance

/-- What a message means, by its destination (persistent). -/
def msgOK (Γ : Names) (m : message) : IProp GF :=
  if m.to' ∈ accIds then
    iprop(⌜m.typ' = W64 1 ∧ m.from' ∈ propIds⌝ ∨
      (⌜m.typ' = W64 2⌝ ∗ propW Γ m.n' m.value' ∗ ∃ k w, pfW Γ m.to' m.n' k w))
  else if m.to' ∈ propIds then
    iprop(⌜m.typ' = W64 3 ∧ m.from' ∈ accIds⌝ ∗ pfW Γ m.from' m.n' m.prevn' m.value')
  else if m.to' ∈ lrnIds then
    iprop(⌜m.typ' = W64 4 ∧ m.from' ∈ accIds⌝ ∗ accW Γ m.from' m.n' m.value')
  else if m.to' ∈ boxIds then
    iprop(⌜m.typ' = W64 5⌝ ∗ chosenW Γ m.value')
  else iprop(True)

instance msgOK_persistent (Γ : Names) (m : message) : Persistent (msgOK (GF := GF) Γ m) := by
  unfold msgOK chosenW accW pfW propW
  repeat (first | infer_instance | split)

instance own_state_timeless (Γ : Names) (σ : Option GoString) :
    Timeless (own_state (GF := GF) Γ σ) := by
  unfold own_state; infer_instance

instance chosenW_persistent (Γ : Names) (v : GoString) : Persistent (chosenW (GF := GF) Γ v) := by
  unfold chosenW accW; infer_instance

instance slotReg_persistent (Γ : Names) c v : Persistent (slotReg (GF := GF) Γ c v) := by
  unfold slotReg; infer_instance

instance accW_persistent (Γ : Names) a n v : Persistent (accW (GF := GF) Γ a n v) := by
  unfold accW; infer_instance
instance accW_timeless (Γ : Names) a n v : Timeless (accW (GF := GF) Γ a n v) := by
  unfold accW; infer_instance
instance pfW_persistent (Γ : Names) a n k w : Persistent (pfW (GF := GF) Γ a n k w) := by
  unfold pfW; infer_instance
instance pfW_timeless (Γ : Names) a n k w : Timeless (pfW (GF := GF) Γ a n k w) := by
  unfold pfW; infer_instance
instance propW_persistent (Γ : Names) n w : Persistent (propW (GF := GF) Γ n w) := by
  unfold propW; infer_instance
instance propW_timeless (Γ : Names) n w : Timeless (propW (GF := GF) Γ n w) := by
  unfold propW; infer_instance
instance regW_persistent (Γ : Names) c v : Persistent (regW (GF := GF) Γ c v) := by
  unfold regW; infer_instance
instance shotW_persistent (Γ : Names) x : Persistent (shotW (GF := GF) Γ x) := by
  unfold shotW; infer_instance
instance shotW_timeless (Γ : Names) x : Timeless (shotW (GF := GF) Γ x) := by
  unfold shotW; infer_instance
instance ptok_timeless (Γ : Names) i : Timeless (ptok (GF := GF) Γ i) := by
  unfold ptok; infer_instance
instance rtok_timeless (Γ : Names) i : Timeless (rtok (GF := GF) Γ i) := by
  unfold rtok; infer_instance

end ghost

/-! ## The laws -/

section laws

variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF]

/-! ### Helpers: ghost-map access through the witnesses -/

omit G in
theorem bigSepM_gmap_insert {K V : Type} [DecidableEq K] {Φ : K → V → IProp GF} {m : GMap K V}
    {k : K} {v : V} (h : m !! k = none) :
    ([∗map] k' ↦ v' ∈ <[k := v]> m, Φ k' v') ⊣⊢ Φ k v ∗ [∗map] k' ↦ v' ∈ m, Φ k' v' :=
  BigSepM.bigSepM_insert h

theorem accW_lookup (Γ : Names) {acc : AccMap} {a n v} :
    ⊢ (ghostMapAuth Γ.acc 1 acc : IProp GF) -∗ accW Γ a n v -∗ ⌜acc !! (a, n) = some v⌝ := by
  unfold accW; exact ghost_map_lookup

theorem pfW_lookup (Γ : Names) {pf : PfMap} {a n k w} :
    ⊢ (ghostMapAuth Γ.pf 1 pf : IProp GF) -∗ pfW Γ a n k w -∗ ⌜pf !! (a, n) = some (k, w)⌝ := by
  unfold pfW; exact ghost_map_lookup

theorem propW_lookup (Γ : Names) {props : PropMap} {n w} :
    ⊢ (ghostMapAuth Γ.props 1 props : IProp GF) -∗ propW Γ n w -∗ ⌜props !! n = some w⌝ := by
  unfold propW; exact ghost_map_lookup

theorem regW_lookup (Γ : Names) {reg : RegMap} {c v} :
    ⊢ (ghostMapAuth Γ.reg 1 reg : IProp GF) -∗ regW Γ c v -∗ ⌜reg !! c = some v⌝ := by
  unfold regW; exact ghost_map_lookup

theorem stOwn_lookup (Γ : Names) {st : StMap} {a s} :
    ⊢ (ghostMapAuth Γ.st 1 st : IProp GF) -∗ stOwn Γ a s -∗ ⌜st !! a = some s⌝ := by
  unfold stOwn; exact ghost_map_lookup

theorem shotW_lookup (Γ : Names) {d : Option GoString} {x} :
    ⊢ (ghostMapAuth Γ.shot 1 (shotMap d) : IProp GF) -∗ shotW Γ x -∗ ⌜d = some x⌝ := by
  unfold shotW
  iintro Ha Hx
  ihave %h := ghost_map_lookup $$ Ha Hx
  ipureintro
  cases d with
  | none => cases h
  | some y => simp [shotMap] at h; rw [h]

theorem accW_insert (Γ : Names) {acc : AccMap} {a n v} (h : acc !! (a, n) = none) :
    ⊢ (ghostMapAuth Γ.acc 1 acc : IProp GF) ==∗
      ghostMapAuth Γ.acc 1 (<[(a, n) := v]> acc) ∗ accW Γ a n v := by
  unfold accW; exact ghost_map_insert_persist _ _ h

theorem pfW_insert (Γ : Names) {pf : PfMap} {a n k w} (h : pf !! (a, n) = none) :
    ⊢ (ghostMapAuth Γ.pf 1 pf : IProp GF) ==∗
      ghostMapAuth Γ.pf 1 (<[(a, n) := (k, w)]> pf) ∗ pfW Γ a n k w := by
  unfold pfW; exact ghost_map_insert_persist _ _ h

theorem propW_insert (Γ : Names) {props : PropMap} {n w} (h : props !! n = none) :
    ⊢ (ghostMapAuth Γ.props 1 props : IProp GF) ==∗
      ghostMapAuth Γ.props 1 (<[n := w]> props) ∗ propW Γ n w := by
  unfold propW; exact ghost_map_insert_persist _ _ h

theorem regW_insert (Γ : Names) {reg : RegMap} {c v} (h : reg !! c = none) :
    ⊢ (ghostMapAuth Γ.reg 1 reg : IProp GF) ==∗
      ghostMapAuth Γ.reg 1 (<[c := v]> reg) ∗ regW Γ c v := by
  unfold regW; exact ghost_map_insert_persist _ _ h

theorem stOwn_update (Γ : Names) {st : StMap} {a s} (s' : AccState) :
    ⊢ (ghostMapAuth Γ.st 1 st : IProp GF) -∗ stOwn Γ a s ==∗
      ghostMapAuth Γ.st 1 (<[a := s']> st) ∗ stOwn Γ a s' := by
  unfold stOwn; exact ghost_map_update _

omit G in
theorem bigSepM_gmap_insert_2 {K V : Type} [DecidableEq K] {Φ : K → V → IProp GF} {m : GMap K V}
    {k : K} {v : V} (h : m !! k = none) :
    ⊢ Φ k v -∗ ([∗map] k' ↦ v' ∈ m, Φ k' v') -∗ [∗map] k' ↦ v' ∈ <[k := v]> m, Φ k' v' := by
  iintro H1 H2
  iapply (bigSepM_gmap_insert h).2
  iframe

theorem ptok_fresh (Γ : Names) {props : PropMap} {n : w64} :
    ⊢ ([∗map] n ↦ _w ∈ props, ptok (GF := GF) Γ (lowId n)) -∗ ptok Γ (lowId n) -∗
      ⌜props !! n = none⌝ := by
  iintro H Ht
  cases h : props !! n with
  | none => ipureintro; rfl
  | some w =>
    ihave Ht' := BigSepM.bigSepM_lookup (Φ := fun n _w => ptok (GF := GF) Γ (lowId n)) h $$ H
    unfold ptok
    ihave %hne := ghostMapElem_ne $$ Ht Ht'
    exact absurd rfl hne

theorem rtok_fresh (Γ : Names) {reg : RegMap} {c : w64} :
    ⊢ ▷ ([∗map] c ↦ v ∈ reg, rtok (GF := GF) Γ c ∗ slotReg Γ c v) -∗ rtok Γ c -∗
      ◇ (⌜reg !! c = none⌝ ∗ ▷ ([∗map] c ↦ v ∈ reg, rtok (GF := GF) Γ c ∗ slotReg Γ c v) ∗
        rtok Γ c) := by
  iintro H Ht
  cases h : reg !! c with
  | none => imodintro; iframe; ipureintro; rfl
  | some v =>
    ihave H := later_mono (BigSepM.bigSepM_lookup
      (Φ := fun c v => iprop(rtok (GF := GF) Γ c ∗ slotReg Γ c v)) h) $$ H
    icases H with ⟨>Ht', -⟩
    unfold rtok
    ihave %hne := ghostMapElem_ne $$ Ht Ht'
    exact absurd rfl hne

theorem issue_value (Γ : Names) {acc pf props reg st d} (HOK : PaxosOK acc pf props reg st d)
    {vN : w64} {w : GoString} :
    ⊢ (ghostMapAuth Γ.props 1 props : IProp GF) -∗ ghostMapAuth Γ.reg 1 reg -∗
      (if vN = W64 0 then ∃ c, regW Γ c w else propW Γ vN w) -∗
      ⌜(vN ≠ W64 0 → props !! vN = some w) ∧ ∃ c, reg !! c = some w⌝ := by
  iintro Hprops Hreg Hw
  by_cases hv0 : vN = W64 0
  · simp only [hv0, ↓reduceIte]
    icases Hw with ⟨%c, Hc⟩
    ihave %hc := regW_lookup $$ Hreg Hc
    ipureintro; exact ⟨fun h => absurd rfl h, c, hc⟩
  · simp only [hv0, ↓reduceIte]
    ihave %hp := propW_lookup $$ Hprops Hw
    ipureintro; exact ⟨fun _ => hp, (HOK.props_wf vN w hp).2.1⟩

/-! ### Helpers: masks, tokens, the decision -/

omit G in
theorem slot_mask (c : w64) : (↑(slotN c) : CoPset) ⊆ ⊤ \ ↑paxosN := by
  intro p hp
  rw [LawfulSet.mem_diff]
  refine ⟨CoPset.mem_full, fun h' => ?_⟩
  have := ndisj_ndot_eq (ndisj_mem_ndot hp) h'
  exact absurd this (by decide)

omit G in
theorem client_mask (c : w64) : ⊤ \ paxosEop ⊆ (⊤ \ ↑paxosN) \ ↑(slotN c) := by
  intro p hp
  rw [LawfulSet.mem_diff] at hp
  rw [LawfulSet.mem_diff, LawfulSet.mem_diff]
  refine ⟨⟨CoPset.mem_full, fun h' => hp.2 ?_⟩, fun h' => hp.2 ?_⟩
  · exact LawfulSet.mem_union.2 (.inl h')
  · exact LawfulSet.mem_union.2 (.inr (ndisj_mem_ndot h'))

/-- **A client's update fires** (from any mask holding `⊤ ∖ paxosEop`), at the register's state
`d`, the invariant's half of which is given: its new state, and the caller's postcondition of the
step's output. -/
theorem opAU_commit (Γ : Names) (M : CoPset) (hM : ⊤ \ paxosEop ⊆ M) (v : GoString)
    (Φ : GoString → IProp GF) (d : Option GoString) :
    ⊢ opAU Γ v Φ -∗ ghostVar Γ.dec (1 : Qp).half d ={M}=∗
      ghostVar Γ.dec (1 : Qp).half (woStep v d).1 ∗ Φ (woStep v d).2 := by
  iintro HAU Hdec
  unfold opAU
  imod fupd_mask_subseteq (PROP := IProp GF) hM with Hmask
  imod HAU with ⟨%σ, Hown, Hcommit⟩
  unfold own_state
  ihave %hσ := ghostVar_agree $$ Hdec Hown
  subst hσ
  imod ghostVar_update_halves (woStep v d).1 $$ Hdec Hown with ⟨Hdec, Hown⟩
  imod Hcommit $$ Hown with HΦ
  imod Hmask
  imodintro
  iframe Hdec HΦ

theorem dtok_excl (Γ : Names) (c : w64) : ⊢ dtok (GF := GF) Γ c -∗ dtok Γ c -∗ False := by
  unfold dtok
  iintro H1 H2
  ihave %hne := ghostMapElem_ne $$ H1 H2
  exact absurd rfl hne

theorem chosenW_chosen (Γ : Names) {acc : AccMap} {w} :
    ⊢ (ghostMapAuth Γ.acc 1 acc : IProp GF) -∗ chosenW Γ w -∗ ⌜∃ m, chosen acc m w⌝ := by
  unfold chosenW
  iintro Hacc ⟨%m, %a, %b, %hab, Ha, Hb⟩
  ihave %ha := accW_lookup $$ Hacc Ha
  ihave %hb := accW_lookup $$ Hacc Hb
  ipureintro
  exact ⟨m, a, b, hab.1, hab.2.1, hab.2.2, ha, hb⟩

theorem shot_insert (Γ : Names) (v : GoString) :
    ⊢ (ghostMapAuth Γ.shot 1 (shotMap none) : IProp GF) ==∗
      ghostMapAuth Γ.shot 1 (shotMap (some v)) ∗ shotW Γ v := by
  unfold shotW shotMap
  exact ghost_map_insert_persist (m := (∅ : GMap Unit GoString)) () v rfl

omit G in
theorem accept_noop {acc pf props reg st d} (H : PaxosOK acc pf props reg st d)
    {a n : w64} {v v' : GoString} {s : AccState} (hs : st !! a = some s) (hn : s.p = n)
    (hv : props !! n = some v) (hacc : acc !! (a, n) = some v') :
    v' = v ∧ { s with k := n, w := v } = s := by
  obtain ⟨-, hp, hpos, t, ht, hle⟩ := H.acc_wf a n v' hacc
  rw [hv] at hp; cases hp
  rw [hs] at ht; cases ht
  obtain ⟨-, hkp, hkw⟩ := H.st_wf a s hs
  have hn' : sint.Z s.p = sint.Z n := by rw [hn]
  have hk : s.k = n := sintZ_inj (by omega)
  have hk0 : s.k ≠ W64 0 := by
    intro h; rw [h] at hk; subst hk; simp at hpos
  have hw := hkw hk0
  rw [hk, hacc] at hw; cases hw
  refine ⟨rfl, ?_⟩
  cases s; simp only at hk ⊢; rw [hk]

theorem ghost_map_insert_list {K V A : Type} [DecidableEq K] [Pos.Countable K] [Pos.Countable V]
    (γ : GName) (f : A → K) (v : V) :
    ∀ (l : List A) (m : GMap K V), (l.map f).Nodup → (∀ x ∈ l, m !! f x = none) →
    ⊢ (ghostMapAuth γ 1 m : IProp GF) ==∗ ∃ m', ghostMapAuth γ 1 m' ∗
      ⌜∀ k, m' !! k = if k ∈ l.map f then some v else m !! k⌝ ∗ [∗list] x ∈ l, f x ↪[γ] v
  | [], m, _, _ => by
    iintro H
    imodintro
    iexists m
    iframe
    isplit
    · ipureintro; intro k; simp
    · iapply BigSepL.bigSepL_nil.2; iempintro
  | x :: l, m, hnd, hfr => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hx := hfr x (by simp)
    have hfr' : ∀ y ∈ l, (<[f x := v]> m) !! f y = none := by
      intro y hy
      have hne : f x ≠ f y := fun h => hnd.1 (h ▸ List.mem_map_of_mem hy)
      rw [GMap.lookup_insert_ne _ _ hne]; exact hfr y (by simp [hy])
    iintro H
    imod ghost_map_insert (f x) v hx $$ H with ⟨H, Hx⟩
    imod ghost_map_insert_list γ f v l (<[f x := v]> m) hnd.2 hfr' $$ H with ⟨%m', H, %hm', Hl⟩
    imodintro
    iexists m'
    iframe
    ipureintro
    intro k
    rw [hm' k]
    by_cases h1 : k ∈ l.map f
    · simp [h1]
    · by_cases h2 : f x = k
      · subst h2; simp
      · simp [h1, h2, Ne.symm h2]

/-- The start: the invariant, the register's client half at `none`, each acceptor's initial
state, and each client's tokens. -/
theorem paxos_alloc (E : CoPset) :
    ⊢ |={E}=> ∃ Γ : Names, isPaxos (GF := GF) Γ ∗ own_state Γ none ∗
      ([∗list] a ∈ accIds, stOwn Γ a AccState.init) ∗
      [∗list] c ∈ [W64 0, W64 1, W64 2, W64 3],
        rtok Γ c ∗ ptok Γ (W64 1001 + c) ∗ dtok Γ c := by
  imod ghost_map_alloc_empty (GF := GF) (K := w64 × w64) (V := GoString) with ⟨%γacc, Hacc⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w64 × w64) (V := w64 × GoString) with ⟨%γpf, Hpf⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := GoString) with ⟨%γprops, Hprops⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := Unit) with ⟨%γptok, Hptok⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := GoString) with ⟨%γreg, Hreg⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := Unit) with ⟨%γrtok, Hrtok⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := Unit) with ⟨%γdtok, Hdtok⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := AccState) with ⟨%γst, Hst⟩
  imod ghostVar_alloc (GF := GF) (none : Option GoString) with ⟨%γdec, Hdec⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Unit) (V := GoString) with ⟨%γshot, Hshot⟩
  imod ghost_map_insert_list γst (fun x => x) AccState.init accIds ∅ (by decide) (by simp) $$ Hst
    with ⟨%st, Hst, %hst, Hsts⟩
  imod ghost_map_insert_list γptok (W64 1001 + ·) () [W64 0, W64 1, W64 2, W64 3] ∅
    (by decide) (by simp) $$ Hptok with ⟨%_, -, -, Hptoks⟩
  imod ghost_map_insert_list γrtok (fun x => x) () [W64 0, W64 1, W64 2, W64 3] ∅
    (by decide) (by simp) $$ Hrtok with ⟨%_, -, -, Hrtoks⟩
  imod ghost_map_insert_list γdtok (fun x => x) () [W64 0, W64 1, W64 2, W64 3] ∅
    (by decide) (by simp) $$ Hdtok with ⟨%_, -, -, Hdtoks⟩
  icases (ghostVar_split_half γdec 1 (none : Option GoString)).1 $$ Hdec with ⟨Hdec1, Hdec2⟩
  let Γ : Names := ⟨γacc, γpf, γprops, γptok, γreg, γrtok, γdtok, γst, γdec, γshot⟩
  have HOK : PaxosOK ∅ ∅ ∅ ∅ st none := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a; rw [hst a]; simp only [List.map_id']; split <;> simp_all
    · intro a s hs; rw [hst a] at hs; split at hs
      · cases hs; exact ⟨by decide, by decide, fun h => absurd rfl h⟩
      · simp at hs
    · intro a n v h; simp at h
    · intro a n k w h; simp at h
    · intro n w h; simp at h
    · intro _ m v ⟨_, _, _, _, _, h, _⟩; simp at h
    · intro x h; cases h
  imod inv_alloc paxosN E (paxosInv Γ) $$ [Hacc Hpf Hprops Hreg Hst Hdec1 Hshot] with #Hinv
  · inext
    unfold paxosInv
    iexists ∅, ∅, ∅, ∅, st, none
    iframe
    simp only [BigSepM.bigSepM_empty.to_eq]
    ipureintro; exact ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, HOK⟩
  imodintro
  iexists Γ
  unfold isPaxos own_state stOwn rtok ptok dtok
  iframe # ∗
  iapply BigSepL.bigSepL_sep_eqv.2
  iframe
  iapply BigSepL.bigSepL_sep_eqv.2
  iframe

/-- An acceptor promises `n` above its promise: its state moves to `n`, and the promise is
witnessed with its accepted proposal. -/
theorem inv_promise (Γ : Names) (E : CoPset) (a n : w64) (s : AccState)
    (hE : ↑paxosN ⊆ E) (hn : sint.Z s.p < sint.Z n) :
    isPaxos (GF := GF) Γ ⊢ stOwn Γ a s ={E}=∗
      stOwn Γ a { s with p := n } ∗ pfW Γ a n s.k s.w := by
  unfold isPaxos
  iintro #Hinv Hs
  iinv Hinv with Hi Hclose
  unfold paxosInv
  icases Hi with ⟨%acc, %pf, %props, %reg, %st, %d, >Hacc, >Hpf, >Hprops, >Hreg, >Hst, >Hdec,
    >Hshot, >#Haccs, >#Hpfs, >#Hpropss, Hshotw, >Hptoks, Hregs, >%HOK⟩
  ihave %hs := stOwn_lookup $$ Hst Hs
  obtain ⟨hfresh, HOK'⟩ := PaxosOK_promise HOK hs hn
  imod stOwn_update Γ { s with p := n } $$ Hst Hs with ⟨Hst, Hs⟩
  imod pfW_insert Γ (k := s.k) (w := s.w) hfresh $$ Hpf with ⟨Hpf, #Hw⟩
  ihave #Hpfs' := bigSepM_gmap_insert_2 (k := (a, n)) (v := (s.k, s.w))
    (Φ := fun an kw => pfW (GF := GF) Γ an.1 an.2 kw.1 kw.2) hfresh $$ Hw Hpfs
  imod Hclose $$ [Hacc Hpf Hprops Hreg Hst Hdec Hshot Hshotw Hptoks Hregs] with -
  · inext
    iexists acc, <[(a, n) := (s.k, s.w)]> pf, props, reg, <[a := { s with p := n }]> st, d
    iframe # ∗
    ipureintro; exact HOK'
  imodintro
  iframe # ∗

/-- A promise witness bounds the acceptor's current promise. -/
theorem inv_promise_lb (Γ : Names) (E : CoPset) (a n k : w64) (w : GoString) (s : AccState)
    (hE : ↑paxosN ⊆ E) :
    isPaxos (GF := GF) Γ ⊢ stOwn Γ a s -∗ pfW Γ a n k w ={E}=∗
      stOwn Γ a s ∗ ⌜sint.Z n ≤ sint.Z s.p⌝ := by
  unfold isPaxos
  iintro #Hinv Hs Hp
  iinv Hinv with Hi Hclose
  unfold paxosInv
  icases Hi with ⟨%acc, %pf, %props, %reg, %st, %d, >Hacc, >Hpf, >Hprops, >Hreg, >Hst, >Hdec,
    >Hshot, >#Haccs, >#Hpfs, >#Hpropss, Hshotw, >Hptoks, Hregs, >%HOK⟩
  ihave %h := pfW_lookup $$ Hpf Hp
  ihave %hs := stOwn_lookup $$ Hst Hs
  obtain ⟨-, -, -, ⟨t, ht, hle⟩, -⟩ := HOK.pf_wf a n k w h
  rw [hs] at ht; cases ht
  imod Hclose $$ [Hacc Hpf Hprops Hreg Hst Hdec Hshot Hshotw Hptoks Hregs] with -
  · inext
    iexists acc, pf, props, reg, st, d
    iframe # ∗
    ipureintro; exact HOK
  imodintro
  iframe
  ipureintro; exact hle

/-- An acceptor accepts the issued proposal `(n, v)` at its promise `n`: its accepted proposal
becomes `(n, v)`, witnessed. If this makes a value chosen for the first time, the update of a
client whose input it is is committed (helping). -/
theorem inv_accept (Γ : Names) (a n : w64) (v : GoString) (s : AccState) (hn : s.p = n) :
    isPaxos (GF := GF) Γ ⊢ £ 2 -∗ stOwn Γ a s -∗ propW Γ n v ={⊤}=∗
      stOwn Γ a { s with k := n, w := v } ∗ accW Γ a n v := by
  unfold isPaxos
  iintro #Hinv ⟨Hlc1, Hlc2⟩ Hs #Hp
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc1 Hi with Hi
  unfold paxosInv
  icases Hi with ⟨%acc, %pf, %props, %reg, %st, %d, Hacc, Hpf, Hprops, Hreg, Hst, Hdec,
    Hshot, #Haccs, #Hpfs, #Hpropss, Hshotw, Hptoks, Hregs, %HOK⟩
  ihave %hs := stOwn_lookup $$ Hst Hs
  ihave %hv := propW_lookup $$ Hprops Hp
  cases hacc : acc !! (a, n) with
  | some v' =>
    obtain ⟨rfl, hs'⟩ := accept_noop HOK hs hn hv hacc
    rw [hs']
    ihave #Ha := BigSepM.bigSepM_lookup
      (Φ := fun (an : w64 × w64) (v : GoString) => accW (GF := GF) Γ an.1 an.2 v) hacc
      $$ Haccs
    imod Hclose $$ [Hacc Hpf Hprops Hreg Hst Hdec Hshot Hshotw Hptoks Hregs] with -
    · inext
      iexists acc, pf, props, reg, st, d
      iframe # ∗
      ipureintro; exact HOK
    imodintro
    iframe # ∗
  | none =>
    have hmono : ∀ k x, acc !! k = some x → (<[(a, n) := v]> acc) !! k = some x := by
      intro k x hk
      have hne : (a, n) ≠ k := by rintro rfl; rw [hacc] at hk; cases hk
      rw [GMap.lookup_insert_ne _ _ hne]; exact hk
    imod accW_insert Γ (v := v) hacc $$ Hacc with ⟨Hacc, #Ha⟩
    ihave #Haccs' := bigSepM_gmap_insert_2 (k := (a, n)) (v := v)
      (Φ := fun an v => accW (GF := GF) Γ an.1 an.2 v) hacc $$ Ha Haccs
    imod stOwn_update Γ { s with k := n, w := v } $$ Hst Hs with ⟨Hst, Hs⟩
    cases d with
    | some x =>
      have HOK' := PaxosOK_accept HOK hs hn hv (some x) (fun h => nomatch h)
        (fun y hy => by
          cases hy
          obtain ⟨m, hm⟩ := HOK.dec_some x rfl
          exact ⟨m, chosen_mono hmono hm⟩)
      imod Hclose $$ [Hacc Hpf Hprops Hreg Hst Hdec Hshot Hshotw Hptoks Hregs] with -
      · inext
        iexists <[(a, n) := v]> acc, pf, props, reg, <[a := { s with k := n, w := v }]> st, some x
        iframe # ∗
        ipureintro; exact HOK'
      imodintro
      iframe # ∗
    | none =>
      by_cases hch : chosen (<[(a, n) := v]> acc) n v
      · obtain ⟨-, ⟨c, hc⟩, -⟩ := HOK.props_wf n v hv
        ihave ⟨⟨Hrtok, #Hsr⟩, Hregs⟩ := (BigSepM.bigSepM_lookup_acc
          (Φ := fun c v => iprop(rtok (GF := GF) Γ c ∗ slotReg Γ c v)) hc).1 $$ Hregs
        unfold slotReg
        icases Hsr with ⟨%Q, #Hslot⟩
        imod inv_acc (slot_mask c) $$ Hslot with ⟨Hsl, Hsclose⟩
        imod lc_fupd_elim_later $$ Hlc2 Hsl with Hsl
        unfold slotContent
        icases Hsl with (HAU | ⟨%o, #Ho, -⟩)
        · imod opAU_commit Γ _ (client_mask c) v Q none $$ HAU Hdec with ⟨Hdec, HQ⟩
          dsimp only [woStep]
          imod shot_insert Γ v $$ Hshot with ⟨Hshot, #Hsv⟩
          imod Hsclose $$ [HQ] with -
          · inext
            iright
            iexists v
            isplitr
            · iexact Hsv
            ileft
            iexact HQ
          have HOK' := PaxosOK_accept HOK hs hn hv (some v) (fun h => nomatch h)
            (fun y hy => by cases hy; exact ⟨n, hch⟩)
          imod Hclose $$ [Hacc Hpf Hprops Hreg Hst Hdec Hshot Hptoks Hregs Hrtok] with -
          · inext
            iexists <[(a, n) := v]> acc, pf, props, reg, <[a := { s with k := n, w := v }]> st,
              some v
            iframe # ∗
            isplitl [Hregs Hrtok]
            · iapply Hregs
              iframe
              imodintro
              iexists Q
              iexact Hslot
            ipureintro; exact HOK'
          imodintro
          iframe # ∗
        · ihave %ho := shotW_lookup $$ Hshot Ho
          cases ho
      · have HOK' := PaxosOK_accept HOK hs hn hv none
          (fun _ m x hx => by
            rcases chosen_insert hx with h | ⟨rfl, rfl⟩
            · exact HOK.dec_none rfl m x h
            · exact hch hx)
          (fun y hy => nomatch hy)
        imod Hclose $$ [Hacc Hpf Hprops Hreg Hst Hdec Hshot Hshotw Hptoks Hregs] with -
        · inext
          iexists <[(a, n) := v]> acc, pf, props, reg, <[a := { s with k := n, w := v }]> st, none
          iframe # ∗
          ipureintro; exact HOK'
        imodintro
        iframe # ∗

/-- The proposer `id` issues `(n, w)` (its one proposal; `n`'s low bits are `id`), from the
promises of `n` by two distinct acceptors, `vN` at least each one's reported number, and `w`
the value of the issued proposal `vN` (`vN ≠ 0`) or a registered input (`vN = 0`). -/
theorem inv_issue (Γ : Names) (E : CoPset) (id n vN : w64) (w : GoString) (a1 a2 k1 k2 : w64)
    (w1 w2 : GoString) (hE : ↑paxosN ⊆ E) (ha1 : a1 ∈ accIds) (ha2 : a2 ∈ accIds) (h12 : a1 ≠ a2)
    (hid : lowId n = id) (hk1 : sint.Z k1 ≤ sint.Z vN) (hk2 : sint.Z k2 ≤ sint.Z vN) :
    isPaxos (GF := GF) Γ ⊢ ptok Γ id -∗ pfW Γ a1 n k1 w1 -∗ pfW Γ a2 n k2 w2 -∗
      (if vN = W64 0 then ∃ c, regW Γ c w else propW Γ vN w) ={E}=∗ propW Γ n w := by
  subst hid
  unfold isPaxos
  iintro #Hinv Hptok #Hp1 #Hp2 Hw
  iinv Hinv with Hi Hclose
  unfold paxosInv
  icases Hi with ⟨%acc, %pf, %props, %reg, %st, %d, >Hacc, >Hpf, >Hprops, >Hreg, >Hst, >Hdec,
    >Hshot, >#Haccs, >#Hpfs, >#Hpropss, Hshotw, >Hptoks, Hregs, >%HOK⟩
  ihave %h1 := pfW_lookup $$ Hpf Hp1
  ihave %h2 := pfW_lookup $$ Hpf Hp2
  ihave %hfresh := ptok_fresh $$ Hptoks Hptok
  ihave %hv := issue_value Γ HOK $$ Hprops Hreg Hw
  have hpos := (HOK.pf_wf a1 n k1 w1 h1).1
  have HOK' := PaxosOK_issue HOK hfresh hpos hv.2
    (issue_safe HOK ha1 ha2 h12 h1 h2 hk1 hk2 hv.1)
  imod propW_insert Γ (w := w) hfresh $$ Hprops with ⟨Hprops, #Hnw⟩
  ihave #Hpropss' := bigSepM_gmap_insert_2
    (Φ := fun n w => propW (GF := GF) Γ n w) hfresh $$ Hnw Hpropss
  ihave Hptoks' := bigSepM_gmap_insert_2 (v := w)
    (Φ := fun n _w => ptok (GF := GF) Γ (lowId n)) hfresh $$ Hptok Hptoks
  imod Hclose $$ [Hacc Hpf Hprops Hreg Hst Hdec Hshot Hshotw Hptoks' Hregs] with -
  · inext
    iexists acc, pf, <[n := w]> props, reg, st, d
    iframe # ∗
    ipureintro; exact HOK'
  imodintro
  iexact Hnw

/-- A promise reports an issued proposal (if any), at a non-negative number. -/
theorem inv_pf_prop (Γ : Names) (E : CoPset) (a n k : w64) (w : GoString) (hE : ↑paxosN ⊆ E) :
    isPaxos (GF := GF) Γ ⊢ pfW Γ a n k w ={E}=∗
      ⌜0 ≤ sint.Z k⌝ ∗ (if k = W64 0 then True else propW Γ k w) := by
  unfold isPaxos
  iintro #Hinv Hp
  iinv Hinv with Hi Hclose
  unfold paxosInv
  icases Hi with ⟨%acc, %pf, %props, %reg, %st, %d, >Hacc, >Hpf, >Hprops, >Hreg, >Hst, >Hdec,
    >Hshot, >#Haccs, >#Hpfs, >#Hpropss, Hshotw, >Hptoks, Hregs, >%HOK⟩
  ihave %h := pfW_lookup $$ Hpf Hp
  obtain ⟨-, hk, -, -, hacc, -⟩ := HOK.pf_wf a n k w h
  imod Hclose $$ [Hacc Hpf Hprops Hreg Hst Hdec Hshot Hshotw Hptoks Hregs] with -
  · inext
    iexists acc, pf, props, reg, st, d
    iframe # ∗
    ipureintro; exact HOK
  imodintro
  isplitr
  · ipureintro; exact hk
  by_cases hk0 : k = W64 0
  · simp only [hk0, ↓reduceIte]; itrivial
  · simp only [hk0, ↓reduceIte]
    obtain ⟨-, hp, -⟩ := HOK.acc_wf a k w (hacc hk0)
    iapply BigSepM.bigSepM_lookup (Φ := fun n w => propW (GF := GF) Γ n w) hp $$ Hpropss

/-- An issued proposal's number is positive. -/
theorem inv_prop_pos (Γ : Names) (E : CoPset) (n : w64) (w : GoString) (hE : ↑paxosN ⊆ E) :
    isPaxos (GF := GF) Γ ⊢ propW Γ n w ={E}=∗ ⌜0 < sint.Z n⌝ := by
  unfold isPaxos
  iintro #Hinv Hp
  iinv Hinv with Hi Hclose
  unfold paxosInv
  icases Hi with ⟨%acc, %pf, %props, %reg, %st, %d, >Hacc, >Hpf, >Hprops, >Hreg, >Hst, >Hdec,
    >Hshot, >#Haccs, >#Hpfs, >#Hpropss, Hshotw, >Hptoks, Hregs, >%HOK⟩
  ihave %h := propW_lookup $$ Hprops Hp
  imod Hclose $$ [Hacc Hpf Hprops Hreg Hst Hdec Hshot Hshotw Hptoks Hregs] with -
  · inext
    iexists acc, pf, props, reg, st, d
    iframe # ∗
    ipureintro; exact HOK
  imodintro; ipureintro; exact (HOK.props_wf n w h).1

/-- One value per number: two acceptances of number `n` have the same value. -/
theorem inv_acc_agree (Γ : Names) (E : CoPset) (a b n : w64) (v v' : GoString)
    (hE : ↑paxosN ⊆ E) :
    isPaxos (GF := GF) Γ ⊢ accW Γ a n v -∗ accW Γ b n v' ={E}=∗ ⌜v = v'⌝ := by
  unfold isPaxos
  iintro #Hinv Ha Hb
  iinv Hinv with Hi Hclose
  unfold paxosInv
  icases Hi with ⟨%acc, %pf, %props, %reg, %st, %d, >Hacc, >Hpf, >Hprops, >Hreg, >Hst, >Hdec,
    >Hshot, >#Haccs, >#Hpfs, >#Hpropss, Hshotw, >Hptoks, Hregs, >%HOK⟩
  ihave %ha := accW_lookup $$ Hacc Ha
  ihave %hb := accW_lookup $$ Hacc Hb
  obtain ⟨-, hpa, -⟩ := HOK.acc_wf a n v ha
  obtain ⟨-, hpb, -⟩ := HOK.acc_wf b n v' hb
  imod Hclose $$ [Hacc Hpf Hprops Hreg Hst Hdec Hshot Hshotw Hptoks Hregs] with -
  · inext
    iexists acc, pf, props, reg, st, d
    iframe # ∗
    ipureintro; exact HOK
  imodintro
  ipureintro
  rw [hpa] at hpb; cases hpb; rfl

/-- Client `c` registers its input `v` with its slot. -/
theorem inv_register (Γ : Names) (E : CoPset) (c : w64) (v : GoString)
    (Q : GoString → IProp GF) (hE : ↑paxosN ⊆ E) :
    isPaxos (GF := GF) Γ ⊢ rtok Γ c -∗ inv (slotN c) (slotContent Γ c v Q) ={E}=∗ regW Γ c v := by
  unfold isPaxos
  iintro #Hinv Hrtok #Hslot
  iinv Hinv with Hi Hclose
  unfold paxosInv
  icases Hi with ⟨%acc, %pf, %props, %reg, %st, %d, >Hacc, >Hpf, >Hprops, >Hreg, >Hst, >Hdec,
    >Hshot, >#Haccs, >#Hpfs, >#Hpropss, Hshotw, >Hptoks, Hregs, >%HOK⟩
  imod rtok_fresh $$ Hregs Hrtok with ⟨%hfresh, Hregs, Hrtok⟩
  have HOK' := PaxosOK_register (v := v) HOK hfresh
  imod regW_insert Γ (v := v) hfresh $$ Hreg with ⟨Hreg, #Hcv⟩
  imod Hclose $$ [Hacc Hpf Hprops Hreg Hst Hdec Hshot Hshotw Hptoks Hregs Hrtok] with -
  · inext
    iexists acc, pf, props, <[c := v]> reg, st, d
    iframe # ∗
    isplitl [Hregs Hrtok]
    · iapply bigSepM_gmap_insert_2
        (Φ := fun c v => iprop(rtok (GF := GF) Γ c ∗ slotReg Γ c v)) hfresh $$ [Hrtok] Hregs
      iframe
      unfold slotReg
      imodintro
      iexists Q
      iexact Hslot
    ipureintro; exact HOK'
  imodintro
  iexact Hcv

/-- Client `c`, whose slot holds its update with postcondition `Q`, learned that `w` is chosen:
its update is committed (now, or it was by the helping acceptor) with output `w`, and it takes
the receipt. -/
theorem inv_return (Γ : Names) (c : w64) (v w : GoString)
    (Q : GoString → IProp GF) :
    isPaxos (GF := GF) Γ ⊢ £ 2 -∗ inv (slotN c) (slotContent Γ c v Q) -∗ dtok Γ c -∗
      chosenW Γ w ={⊤}=∗ Q w := by
  unfold isPaxos
  iintro #Hinv ⟨Hlc1, Hlc2⟩ #Hslot Hd #Hch
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc1 Hi with Hi
  unfold paxosInv
  icases Hi with ⟨%acc, %pf, %props, %reg, %st, %d, Hacc, Hpf, Hprops, Hreg, Hst, Hdec,
    Hshot, #Haccs, #Hpfs, #Hpropss, Hshotw, Hptoks, Hregs, %HOK⟩
  ihave %hch := chosenW_chosen $$ Hacc Hch
  obtain ⟨m, hm⟩ := hch
  have hd : d = some w := by
    cases d with
    | none => exact absurd hm (HOK.dec_none rfl m w)
    | some x =>
      obtain ⟨m', hm'⟩ := HOK.dec_some x rfl
      rw [chosen_agree HOK m' m x w hm' hm]
  subst hd
  dsimp only
  icases Hshotw with #Hshotw
  imod inv_acc (slot_mask c) $$ Hslot with ⟨Hs, Hsclose⟩
  imod lc_fupd_elim_later $$ Hlc2 Hs with Hs
  unfold slotContent
  icases Hs with (HAU | ⟨%o, #Ho, (HQ | Hd')⟩)
  · imod opAU_commit Γ _ (client_mask c) v Q (some w) $$ HAU Hdec with ⟨Hdec, HQ⟩
    dsimp only [woStep]
    imod Hsclose $$ [Hd] with -
    · inext
      iright
      iexists w
      isplitr
      · iexact Hshotw
      iright; iexact Hd
    imod Hclose $$ [Hacc Hpf Hprops Hreg Hst Hdec Hshot Hshotw Hptoks Hregs] with -
    · inext
      iexists acc, pf, props, reg, st, some w
      iframe # ∗
      ipureintro; exact HOK
    imodintro
    iexact HQ
  · ihave %ho := shotW_lookup $$ Hshot Ho
    cases ho
    imod Hsclose $$ [Hd] with -
    · inext
      iright
      iexists w
      isplitr
      · iexact Ho
      iright; iexact Hd
    imod Hclose $$ [Hacc Hpf Hprops Hreg Hst Hdec Hshot Hshotw Hptoks Hregs] with -
    · inext
      iexists acc, pf, props, reg, st, some w
      iframe # ∗
      ipureintro; exact HOK
    imodintro
    iexact HQ
  · iexfalso
    iapply dtok_excl $$ Hd Hd'

end laws

end github_com.xiang90.paxos

end Perennial
