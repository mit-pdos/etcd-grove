/-
**The client's model of etcd, on the server's log** (pure; the vertical slice's unit V1,
2026-10-13; `notes/STATUS.md`, "The vertical slice: client to server"). Lean-first, no Rocq
counterpart.

The clients' class `EtcdModel` (`cache/v3/EtcdModel.lean`) states its laws over an abstract state
`etcdState rev pfx s` and an abstract step `EtcdStep r0 r1 pfx evs`. The server instantiates them
(`v3rpc/ClientModel.lean`) from its certified log: the state at `rev` restricted to a prefix
(`underPfx pfx (stateAt log rev)`, the history laws' `stateAtPfx`), and the client's events of a
revision (`revEvs`: each change of the revision under the prefix, as the client's `EtcdEv`, a put
with the key-value it writes, `putNv`, a delete with the key and the revision). This file proves
the laws that the history laws (`HistoryLaws.lean`, unit 4) do not already give:

* **Transfer** (`step_transfer`): the state under `pfx` after a revision is the state before with
  the revision's events under `pfx` applied (`underPfx_applyChanges`: `underPfx` of the server's
  changes is the client's `applyEvsState` of the events; a change outside the prefix leaves the
  restriction alone); across revisions with no event under `pfx`, the restriction is unchanged
  (`underPfx_quiet`).
* **Delete present** (`step_delete_present`): each delete event of a revision removes a key present
  when it is applied: the log's `LogWf'` (each delete of the server's model is of a present key).
* **Revisions** (`stateAt_client_revs`): `etcdState_revs` without `NoDupKeysPerRev`, which the server
  does not guarantee (`issues/etcd-txn-delete-then-ignore-put.md`,
  `issues/etcd-txn-check-intervals-sibling.md`: a revision may write a key twice, its version then
  growing by two): a positive create revision (revision 0 is empty), and a positive version from the
  log's size (`LogSmall`: at most `2 ^ 62` changes, the read path's `storeSmall`).
* **Stability** (`revEvs_prefix`): a revision's events are fixed once the revision is in the log.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.HistoryLaws
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.RangeModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace txn

open mvcc

/-! ## `btInsert` and `btDelete` under a filter -/

section bt
variable {V : Type} {less : V → V → Prop} [DecidableRel less]

theorem btInsert_of_lt_all {v : V} (hord : StrictWeakOrder less) :
    ∀ {l : List V}, (∀ x ∈ l, less v x) → btInsert less v l = v :: l
  | [], _ => rfl
  | w :: ws, h => by
    have hvw := h w List.mem_cons_self
    have hwv : ¬ less w v := fun h' => hord.irrefl v (hord.trans _ _ _ hvw h')
    simp only [btInsert, hwv, hvw, ↓reduceIte]

theorem btDelete_of_lt_all {k : V} (hord : StrictWeakOrder less) :
    ∀ {l : List V}, (∀ x ∈ l, less k x) → btDelete less k l = l
  | [], _ => rfl
  | w :: ws, h => by
    have hkw := h w List.mem_cons_self
    have hwk : ¬ less w k := fun h' => hord.irrefl k (hord.trans _ _ _ hkw h')
    simp only [btDelete, hwk, hkw, ↓reduceIte]

/-- `p` gives one answer on items the order does not separate. -/
def RespEquiv (less : V → V → Prop) (p : V → Bool) : Prop :=
  ∀ a b, ¬ less a b → ¬ less b a → p a = p b

theorem filter_btInsert (hord : StrictWeakOrder less) (p : V → Bool) (hp : RespEquiv less p)
    (v : V) : ∀ (l : List V), l.Pairwise less →
      (btInsert less v l).filter p = if p v then btInsert less v (l.filter p) else l.filter p
  | [], _ => by by_cases h : p v <;> simp [btInsert, h]
  | w :: ws, hs => by
    rw [List.pairwise_cons] at hs
    have ih := filter_btInsert hord p hp v ws hs.2
    by_cases h1 : less w v
    · simp only [btInsert, h1, ↓reduceIte, List.filter_cons, ih]
      by_cases hv : p v <;> by_cases hw : p w <;> simp [hv, hw, btInsert, h1]
    · by_cases h2 : less v w
      · simp only [btInsert, h1, h2, ↓reduceIte]
        have hall : ∀ x ∈ (w :: ws).filter p, less v x := by
          intro x hx
          rcases List.mem_cons.1 (List.mem_filter.1 hx).1 with rfl | hx'
          · exact h2
          · exact hord.trans _ _ _ h2 (hs.1 x hx')
        by_cases hv : p v
        · rw [List.filter_cons_of_pos hv, if_pos hv, btInsert_of_lt_all hord hall]
        · rw [List.filter_cons_of_neg hv, if_neg hv]
      · have he := hp v w h2 h1
        simp only [btInsert, h1, h2, ↓reduceIte]
        by_cases hv : p v
        · have hw : p w = true := he ▸ hv
          rw [List.filter_cons_of_pos hv, if_pos hv, List.filter_cons_of_pos hw]
          simp only [btInsert, h1, h2, ↓reduceIte]
        · have hw : ¬ p w = true := by rw [← he]; exact hv
          rw [List.filter_cons_of_neg hv, if_neg hv, List.filter_cons_of_neg hw]

theorem filter_btDelete (hord : StrictWeakOrder less) (p : V → Bool) (hp : RespEquiv less p)
    (k : V) : ∀ (l : List V), l.Pairwise less →
      (btDelete less k l).filter p = if p k then btDelete less k (l.filter p) else l.filter p
  | [], _ => by by_cases h : p k <;> simp [btDelete, h]
  | w :: ws, hs => by
    rw [List.pairwise_cons] at hs
    have ih := filter_btDelete hord p hp k ws hs.2
    by_cases h1 : less w k
    · simp only [btDelete, h1, ↓reduceIte, List.filter_cons, ih]
      by_cases hk : p k <;> by_cases hw : p w <;> simp [hk, hw, btDelete, h1]
    · by_cases h2 : less k w
      · simp only [btDelete, h1, h2, ↓reduceIte]
        have hall : ∀ x ∈ (w :: ws).filter p, less k x := by
          intro x hx
          rcases List.mem_cons.1 (List.mem_filter.1 hx).1 with rfl | hx'
          · exact h2
          · exact hord.trans _ _ _ h2 (hs.1 x hx')
        by_cases hk : p k
        · rw [if_pos hk, btDelete_of_lt_all hord hall]
        · rw [if_neg hk]
      · have he := hp k w h2 h1
        simp only [btDelete, h1, h2, ↓reduceIte]
        by_cases hk : p k
        · have hw : p w = true := he ▸ hk
          rw [if_pos hk, List.filter_cons_of_pos hw]
          simp only [btDelete, h1, h2, ↓reduceIte]
        · have hw : ¬ p w = true := by rw [← he]; exact hk
          rw [if_neg hk, List.filter_cons_of_neg hw]

end bt

/-! ## The state under a prefix -/

/-- The key-values of `s` under the prefix `pfx` (`stateAtPfx`'s filter). -/
def underPfx (pfx : GoString) (s : List EtcdKv) : List EtcdKv :=
  s.filter (fun v => decide (pfx <+: v.key))

theorem underPfx_stateAt (log : Log) (r : Nat) (pfx : GoString) :
    underPfx pfx (stateAt log r) = stateAtPfx log r pfx := rfl

theorem underPfx_sorted {s : List EtcdKv} (hs : s.Pairwise etcdKvLess) (pfx : GoString) :
    (underPfx pfx s).Pairwise etcdKvLess := hs.filter _

theorem mem_underPfx {pfx : GoString} {s : List EtcdKv} {v : EtcdKv} :
    v ∈ underPfx pfx s ↔ v ∈ s ∧ pfx <+: v.key := by
  unfold underPfx; rw [List.mem_filter, decide_eq_true_iff]

theorem etcdKv_key_eq_of_incomp {a b : EtcdKv} (h1 : ¬ etcdKvLess a b) (h2 : ¬ etcdKvLess b a) :
    a.key = b.key := goStringLt_eq_of_not_lt h1 h2

theorem pfx_respEquiv (pfx : GoString) :
    RespEquiv etcdKvLess (fun v : EtcdKv => decide (pfx <+: v.key)) := by
  intro a b h1 h2
  show _ = _
  simp only [etcdKv_key_eq_of_incomp h1 h2]

theorem key_ne_respEquiv (k : GoString) :
    RespEquiv etcdKvLess (fun v : EtcdKv => !decide (v.key = k)) := by
  intro a b h1 h2
  show _ = _
  simp only [etcdKv_key_eq_of_incomp h1 h2]

/-- On a sorted state, removing the key of `x` is `btDelete`. -/
theorem filter_key_ne_eq_btDelete (x : EtcdKv) :
    ∀ (s : List EtcdKv), s.Pairwise etcdKvLess →
      s.filter (fun v => !decide (v.key = x.key)) = btDelete etcdKvLess x s
  | [], _ => rfl
  | w :: ws, hs => by
    rw [List.pairwise_cons] at hs
    by_cases h1 : etcdKvLess w x
    · have hne : w.key ≠ x.key := fun e => goStringLt_irrefl _ (by unfold etcdKvLess at h1; rw [e] at h1; exact h1)
      simp only [List.filter_cons, hne, decide_false, Bool.not_false, ↓reduceIte, btDelete, h1,
        filter_key_ne_eq_btDelete x ws hs.2]
    · by_cases h2 : etcdKvLess x w
      · have hall : ∀ y ∈ w :: ws, y.key ≠ x.key := by
          intro y hy e
          have hxy : etcdKvLess x y := by
            rcases List.mem_cons.1 hy with rfl | hy
            · exact h2
            · exact goStringLt_trans h2 (hs.1 y hy)
          unfold etcdKvLess at hxy; rw [e] at hxy; exact goStringLt_irrefl _ hxy
        rw [List.filter_eq_self.2 (fun y hy => by simp [hall y hy])]
        simp only [btDelete, h1, h2, ↓reduceIte]
      · have he := etcdKv_key_eq_of_incomp h1 h2
        simp only [List.filter_cons, he, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        have hall : ∀ y ∈ ws, y.key ≠ x.key := by
          intro y hy e
          have := hs.1 y hy
          unfold etcdKvLess at this; rw [e, ← he] at this; exact goStringLt_irrefl _ this
        rw [List.filter_eq_self.2 (fun y hy => by simp [hall y hy])]
        simp only [btDelete, h1, h2, ↓reduceIte]

/-! ## The client's events of the server's changes -/

/-- The key-value a put of `k` writes at revision `r` on the state `s` (`putKv`'s new record). -/
def putNv (r : w64) (k val : GoString) (l : w64) (s : List EtcdKv) : EtcdKv :=
  match s.find? (fun v => decide (v.key = k)) with
  | some v => { v with modRev := r, version := v.version + W64 1, value := val, lease := l }
  | none => { key := k, createRev := r, modRev := r, version := W64 1, value := val, lease := l }

theorem putKv_eq (r : w64) (k val : GoString) (l : w64) (s : List EtcdKv) :
    putKv r k val l s = btInsert etcdKvLess (putNv r k val l s) s := by
  unfold putKv putNv; rfl

theorem putNv_key (r : w64) (k val : GoString) (l : w64) (s : List EtcdKv) :
    (putNv r k val l s).key = k := by
  unfold putNv
  cases hf : s.find? (fun v => decide (v.key = k)) with
  | none => rfl
  | some w => simpa using List.find?_some hf

/-- **The client's event of a change** of revision `r` on the state `s` before it: a put with the
key-value it writes (type `0`), a delete with the key and the revision (type `1`: what etcd's
watchable store sends, `mvccpb.KeyValue{Key, ModRevision}`). -/
def changeEv (r : w64) (s : List EtcdKv) : Change → EtcdEv
  | .put k val l => { typ := W32 0, kv := putNv r k val l s }
  | .del k => { typ := W32 1, kv := { zeroKv k with modRev := r } }

theorem changeEv_key (r : w64) (s : List EtcdKv) (c : Change) : (changeEv r s c).kv.key = c.key := by
  cases c with
  | put k val l => exact putNv_key r k val l s
  | del k => rfl

/-- **The client's events of revision `r`'s changes `cs` under `pfx`**, from the state `s`
before them, in order. -/
def evsUnder (pfx : GoString) (r : w64) : List EtcdKv → List Change → List EtcdEv
  | _, [] => []
  | s, c :: cs => (if pfx <+: c.key then [changeEv r s c] else []) ++
      evsUnder pfx r (applyChange r s c) cs

theorem applyEvsState_append (s : List EtcdKv) (a b : List EtcdEv) :
    applyEvsState s (a ++ b) = applyEvsState (applyEvsState s a) b := by
  unfold applyEvsState; rw [List.foldl_append]

theorem filter_comm' {α : Type} (p q : α → Bool) (l : List α) :
    (l.filter p).filter q = (l.filter q).filter p := by
  rw [List.filter_filter, List.filter_filter]
  exact List.filter_congr (fun x _ => Bool.and_comm _ _)

/-- **One change under a prefix**: the restriction after it is the client's event applied to
the restriction before (nothing for a change outside the prefix). -/
theorem underPfx_applyChange (pfx : GoString) (r : w64) (s : List EtcdKv)
    (hs : s.Pairwise etcdKvLess) (c : Change) :
    underPfx pfx (applyChange r s c) =
      applyEvsState (underPfx pfx s) (if pfx <+: c.key then [changeEv r s c] else []) := by
  cases c with
  | put k val l =>
    rw [applyChange_put, putKv_eq]
    unfold underPfx
    rw [filter_btInsert etcdKvLess_swo _ (pfx_respEquiv pfx) _ s hs]
    simp only [putNv_key, Change.key]
    by_cases h : pfx <+: k
    · simp only [h, decide_true, ↓reduceIte, applyEvsState, List.foldl_cons, List.foldl_nil,
        applyEvState, changeEv]
      have : ¬ (W32 0 = W32 1) := by decide
      simp [this]
    · simp [h, applyEvsState]
  | del k =>
    rw [applyChange_del]
    unfold underPfx
    rw [filter_comm']
    simp only [Change.key]
    by_cases h : pfx <+: k
    · simp only [h, ↓reduceIte, applyEvsState, List.foldl_cons, List.foldl_nil, applyEvState,
        changeEv, ↓reduceIte]
      exact filter_key_ne_eq_btDelete { zeroKv k with modRev := r } _ (hs.filter _)
    · simp only [h, ↓reduceIte, applyEvsState, List.foldl_nil]
      apply List.filter_eq_self.2
      intro v hv
      have hv' := (List.mem_filter.1 hv).2
      simp only [decide_eq_true_eq] at hv'
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
      intro e; exact h (e ▸ hv')

/-- **A revision's changes under a prefix** (the commuting lemma): `underPfx` of the server's
changes is the client's `applyEvsState` of their events under the prefix. -/
theorem underPfx_applyChanges (pfx : GoString) (r : w64) :
    ∀ (cs : List Change) (s : List EtcdKv), s.Pairwise etcdKvLess →
      underPfx pfx (applyChanges r s cs) = applyEvsState (underPfx pfx s) (evsUnder pfx r s cs)
  | [], _, _ => rfl
  | c :: cs, s, hs => by
    rw [applyChanges_cons, underPfx_applyChanges pfx r cs _ (applyChange_sorted hs r c)]
    simp only [evsUnder]
    rw [applyEvsState_append, ← underPfx_applyChange pfx r s hs c]

/-! ## The events of a revision of the log -/

/-- **The client's events of revision `x` under `pfx`** in the log. -/
def revEvs (log : Log) (pfx : GoString) (x : Nat) : List EtcdEv :=
  evsUnder pfx (W64 (x : Int)) (stateAt log (x - 1)) (log[x]?.getD [])

/-- A revision's events are fixed once it is in the log. -/
theorem revEvs_prefix {log log' : Log} (h : log <+: log') {x : Nat} (hx : x < log.length)
    (pfx : GoString) : revEvs log' pfx x = revEvs log pfx x := by
  unfold revEvs
  rw [stateAt_of_prefix h (by omega)]
  obtain ⟨t, rfl⟩ := h
  rw [List.getElem?_append_left hx]

theorem underPfx_stateAt_succ (log : Log) (pfx : GoString) (j : Nat) (h : j + 1 < log.length) :
    underPfx pfx (stateAt log (j + 1)) =
      applyEvsState (underPfx pfx (stateAt log j)) (revEvs log pfx (j + 1)) := by
  rw [stateAt_succ log j h, underPfx_applyChanges pfx _ _ _ (stateAt_sorted log j)]
  unfold revEvs
  simp only [Nat.add_sub_cancel, List.getElem?_eq_getElem h, Option.getD_some]

/-- **No event under `pfx` in `(a, b]`**: the restriction at `b` is the one at `a`. -/
theorem underPfx_quiet (log : Log) (pfx : GoString) (a : Nat) :
    ∀ (b : Nat), a ≤ b → b < log.length → (∀ x, a < x → x ≤ b → revEvs log pfx x = []) →
      underPfx pfx (stateAt log b) = underPfx pfx (stateAt log a)
  | 0, hab, _, _ => by rw [Nat.le_zero.1 hab]
  | j + 1, hab, hb, hq => by
    by_cases he : a = j + 1
    · rw [he]
    rw [underPfx_stateAt_succ log pfx j hb, hq (j + 1) (by omega) (Nat.le_refl _)]
    exact underPfx_quiet log pfx a j (by omega) (by omega) (fun x h1 h2 => hq x h1 (by omega))

/-- **Transfer**: no event under `pfx` strictly between `a` and `r1`: the restriction at `r1` is
the one at `a` with `r1`'s events applied. -/
theorem step_transfer (log : Log) (pfx : GoString) (a r1 : Nat) (har : a < r1)
    (h1 : r1 < log.length) (hq : ∀ x, a < x → x < r1 → revEvs log pfx x = []) :
    underPfx pfx (stateAt log r1) =
      applyEvsState (underPfx pfx (stateAt log a)) (revEvs log pfx r1) := by
  obtain ⟨j, rfl⟩ : ∃ j, r1 = j + 1 := ⟨r1 - 1, by omega⟩
  rw [underPfx_stateAt_succ log pfx j h1,
    underPfx_quiet log pfx a j (by omega) (by omega) (fun x h1 h2 => hq x h1 (by omega))]

/-! ## Deletes of present keys -/

theorem findKey_isSome_mem {k : GoString} {s : List EtcdKv} (h : (findKey k s).isSome) :
    ∃ v ∈ s, v.key = k := by
  unfold findKey at h
  cases hf : s.find? (fun v => decide (v.key = k)) with
  | none => rw [hf] at h; cases h
  | some v => exact ⟨v, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩

/-- Each delete event of a revision's changes under `pfx` removes a key present when it is
applied, if each delete of the changes is of a present key. -/
theorem evsUnder_delete_present (pfx : GoString) (r : w64) :
    ∀ (cs : List Change) (s : List EtcdKv), s.Pairwise etcdKvLess →
      (∀ (j : Nat) (k : GoString), cs[j]? = some (.del k) →
        (findKey k (applyChanges r s (cs.take j))).isSome) →
      ∀ (i : Nat) (c : EtcdEv), (evsUnder pfx r s cs)[i]? = some c → c.typ = W32 1 →
        ∃ v ∈ applyEvsState (underPfx pfx s) ((evsUnder pfx r s cs).take i), v.key = c.kv.key
  | [], _, _, _, i, c, hc, _ => by simp [evsUnder] at hc
  | c0 :: cs, s, hs, hdel, i, c, hc, ht => by
    have hs1 := applyChange_sorted hs r c0
    have hdel1 : ∀ (j : Nat) (k : GoString), cs[j]? = some (.del k) →
        (findKey k (applyChanges r (applyChange r s c0) (cs.take j))).isSome := by
      intro j k hj
      have := hdel (j + 1) k (by simpa using hj)
      simpa [List.take_succ_cons, applyChanges_cons] using this
    have hstep := underPfx_applyChange pfx r s hs c0
    simp only [evsUnder] at hc ⊢
    by_cases hu : pfx <+: c0.key
    · simp only [hu, ↓reduceIte, List.singleton_append] at hc hstep ⊢
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
        subst hc
        cases c0 with
        | put k val l => simp [changeEv] at ht
        | del k =>
          obtain ⟨v, hv, hvk⟩ := findKey_isSome_mem (by simpa [applyChanges] using hdel 0 k rfl)
          refine ⟨v, ?_, by rw [hvk]; rfl⟩
          simp only [List.take_zero, applyEvsState, List.foldl_nil]
          exact mem_underPfx.2 ⟨hv, by rw [hvk]; exact hu⟩
      | succ i =>
        simp only [List.getElem?_cons_succ] at hc
        obtain ⟨v, hv, hvk⟩ :=
          evsUnder_delete_present pfx r cs _ hs1 hdel1 i c hc ht
        refine ⟨v, ?_, hvk⟩
        rw [List.take_succ_cons]
        have hcons : ∀ (x : List EtcdKv) (L : List EtcdEv) (e : EtcdEv),
            applyEvsState x (e :: L) = applyEvsState (applyEvsState x [e]) L := fun _ _ _ => rfl
        rw [hcons, ← hstep]
        exact hv
    · simp only [hu, ↓reduceIte, List.nil_append] at hc hstep ⊢
      obtain ⟨v, hv, hvk⟩ := evsUnder_delete_present pfx r cs _ hs1 hdel1 i c hc ht
      refine ⟨v, ?_, hvk⟩
      rw [hstep] at hv
      simpa [applyEvsState] using hv

/-- **Delete present**, on the log: each delete event of revision `r1` under `pfx` removes a key
present when it is applied, from the restriction at any `a < r1` with no event under `pfx`
between them (`LogWf'`: every delete of the log is of a present key). -/
theorem step_delete_present (log : Log) (hwf : LogWf' log) (pfx : GoString) (a r1 : Nat)
    (har : a < r1) (h1 : r1 < log.length) (hq : ∀ x, a < x → x < r1 → revEvs log pfx x = []) :
    ∀ (i : Nat) (c : EtcdEv), (revEvs log pfx r1)[i]? = some c → c.typ = W32 1 →
      ∃ v ∈ applyEvsState (underPfx pfx (stateAt log a)) ((revEvs log pfx r1).take i),
        v.key = c.kv.key := by
  intro i c hc ht
  obtain ⟨j, rfl⟩ : ∃ j, r1 = j + 1 := ⟨r1 - 1, by omega⟩
  have hq' := underPfx_quiet log pfx a j (by omega) (by omega) (fun x h1 h2 => hq x h1 (by omega))
  rw [← hq']
  unfold revEvs at hc ⊢
  simp only [Nat.add_sub_cancel, List.getElem?_eq_getElem h1, Option.getD_some] at hc ⊢
  refine evsUnder_delete_present pfx _ _ _ (stateAt_sorted log j) ?_ i c hc ht
  intro j' k hk
  have := hwf.2 (j + 1) log[j + 1] j' k (List.getElem?_eq_getElem h1) hk
  simpa using this

/-! ## The revisions of the state's records, without `NoDupKeysPerRev` -/

theorem stateAt_createRev_pos (log : Log) (h0 : log[0]? = some []) (hlen : log.length < 2 ^ 63) :
    ∀ r, r < log.length → ∀ v ∈ stateAt log r, 1 ≤ uint.nat v.createRev
  | 0, _, v, hv => by rw [stateAt_zero_nil log h0] at hv; exact absurd hv List.not_mem_nil
  | j + 1, hr, v, hv => by
    rw [stateAt_succ log j hr] at hv
    by_cases hc : v.createRev = W64 ((j + 1 : Nat) : Int)
    · rw [hc, hl_nat_W64 _ (by omega)]; omega
    · obtain ⟨w, hw, -, hwc⟩ := mem_applyChanges_createRev _ _ v hv hc
      rw [← hwc]
      exact stateAt_createRev_pos log h0 hlen j (by omega) w hw

/-- **`etcdState_revs` of the log**, from a small log (`LogSmall`) instead of
`NoDupKeysPerRev`: positive create revision, at most the mod revision, at most `r`, positive
version. -/
theorem stateAt_client_revs (log : Log) (hwf : LogWf' log) (hlen : log.length < 2 ^ 63)
    (hsmall : LogSmall log) (r : Nat) (hr : r < log.length) :
    ∀ v ∈ stateAt log r, 0 < sint.Z v.createRev ∧ sint.Z v.createRev ≤ sint.Z v.modRev ∧
      sint.Z v.modRev ≤ r ∧ 0 < sint.Z v.version := by
  intro v hv
  have hne : log ≠ [] := by intro h; subst h; simp at hr
  have h0 := hwf.1 hne
  have hc1 := stateAt_createRev_pos log h0 hlen r hr v hv
  have hri := stateAt_revInv log hlen r hr v hv
  unfold RevInv at hri
  have hc := logChanges_take log (r + 1)
  have hb := stateBound_stateAfter (log.take (r + 1)) (by simp; omega)
    (by unfold LogSmall at hsmall; omega)
  unfold StateBound at hb
  have hver := (hb.2 v hv).2.2.2.2.1
  rw [hl_sint_eq _ (by omega), hl_sint_eq v.modRev (by omega)]
  omega

end txn
end EtcdGrove
end Perennial
