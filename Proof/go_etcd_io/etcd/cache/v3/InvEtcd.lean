/-
The etcd model: what etcd's cache knows of etcd itself, its trust boundary (Lean-first, no
Rocq counterpart; the Rocq development's `is_etcd_kvs` is the precedent). See `decisions.md`,
"the etcd model".

**etcd's state.** `etcdState rev pfx s` (an axiom, with `etcdState_agree`) says that etcd's
key-value state at revision `rev`, restricted to the keys with prefix `pfx`, is `s`: the
key-values as etcd stores them (`EtcdKv`: key, value, create and mod revisions, version,
lease), by key. It is a fact about the server, which Goose does not model, hence an opaque
predicate. Its one property is **agreement**: etcd has one state per revision. That is all
the cache's proofs need of etcd; everything else is said by the client's statements, which
produce `etcdState` facts.

**Maps.** The cache keeps maps of `(key, *KeyValue)` (`KvMap`, `InvStore.lean`), and a
`*KeyValue` is a fresh allocation in every response, so the model is about contents, not
pointers: `isEtcdKvs rev pfx m` says that the map `m`'s entries are, in order, etcd's state
`s` at `rev` (`□ etcdState rev pfx s`), with each `*KeyValue` holding (read-only) the
corresponding `EtcdKv` (`kvValAt`), keys strictly increasing, all with prefix `pfx`. It is
persistent, and two of them at the same revision have the same keys and contents
(`isEtcdKvs_agree`). It is the store's certificate in the cache (`etcdCert`).

**The client.** `isEtcdKV kv pfx` is the triple of `kv.Get(ctx, key, opts...)` on the
`clientv3.KV` interface value `kv`, for a cache of prefix `pfx`, at the strength of etcd's
documented API: any error is possible; on success the response's header has a revision `r`
at which etcd had a state, and a prefix get (`OpFull.isPrefixGet`: `WithPrefix` on `pfx`, no
revision, limit, sort, filters, keys-only or count-only) lists exactly that state, `r`'s.
It is a definition (as Perennial's `isLocker` is), not an axiom: the cache's specs take it as
a premise, and the client axiom is what a caller will have to assume of `client.KV`.

**Time: what etcd has reached.** `etcdReached r` (persistent, timeless, downward closed, free
for `r ≤ 0`) says that some response from etcd has shown revision `r` to exist. Resources are
obtained causally, so a holder learned it before any call it makes next: a linearizable `Get`
started then returns at least `r` (`isEtcdKV`'s triple takes `etcdReached lo` and returns a
header revision `≥ lo`, with `etcdReached` of it). The watch stream's responses give it of every
revision they report (`watchRespOk`, `etcdStepCertBody`). It is defined over one axiomatized
predicate, `etcdReachedAt` (with its timelessness): `etcdReached r` is `etcdReachedAt r'` for
some `r' ≥ r`, or `r ≤ 0`, so persistence, downward closure and `etcdReached 0` are lemmas.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvDemux
public import Proof.go_etcd_io.etcd.client.v3.InvOp
public import Perennial.Golang.Theory.Chan.Idioms.Spsc
public import Perennial.Ghost.MonoList

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

/-! ## etcd's state -/

/-- A key-value as etcd stores it (`mvccpb.KeyValue`'s fields). -/
structure EtcdKv where
  key : GoString
  createRev : w64
  modRev : w64
  version : w64
  value : GoString
  lease : w64

/-- etcd's key-value state at revision `rev`, restricted to the keys with prefix `pfx`, is `s`
(sorted by key). A fact about the etcd server, which is not modelled: an axiom. -/
axiom etcdState {GF : BundledGFunctors} (rev : w64) (pfx : GoString) (s : List EtcdKv) :
  IProp GF

/-- etcd has one state per revision. -/
axiom etcdState_agree {GF : BundledGFunctors} (rev : w64) (pfx : GoString)
    (s s' : List EtcdKv) :
  etcdState (GF := GF) rev pfx s ∗ etcdState rev pfx s' ⊢ ⌜s = s'⌝

/-- The keys of `s` are strictly increasing and have the prefix `pfx`. -/
def EtcdStateWf (pfx : GoString) (s : List EtcdKv) : Prop :=
  (s.map EtcdKv.key).Pairwise go.GoStringLt ∧ ∀ v ∈ s, pfx <+: v.key

/-! ## Time: the revisions etcd has reached -/

/-- **etcd has reached revision `r`** (an axiom: a fact about the server, as known to a holder):
some response from etcd showed revision `r` to exist. An `IProp`, not a `Prop`, because it is
knowledge obtained at a point in time: holding it means it was learned (from a response) before
whatever the holder does next, which is what makes linearizability statable (`isEtcdKV`). -/
axiom etcdReachedAt {GF : BundledGFunctors} (r : w64) : IProp GF

/-- `etcdReachedAt` is timeless (it carries no resources), so it can sit in invariants opened
without later credits (the demux's certificates, a watcher's publication). -/
axiom etcdReachedAt_timeless {GF : BundledGFunctors} (r : w64) :
  Timeless (etcdReachedAt (GF := GF) r)

attribute [instance] etcdReachedAt_timeless

/-- **etcd has reached revision `r`**, downward closed: etcd reached some `r' ≥ r`, or `r ≤ 0`
(every revision etcd reports is positive, so `0` is free). Persistent and timeless. -/
def etcdReached {GF : BundledGFunctors} (r : w64) : IProp GF :=
  iprop(⌜sint.Z r ≤ 0⌝ ∨ ∃ r' : w64, ⌜sint.Z r ≤ sint.Z r'⌝ ∗ □ etcdReachedAt r')

instance etcdReached_persistent {GF : BundledGFunctors} (r : w64) :
    Persistent (etcdReached (GF := GF) r) := by
  unfold etcdReached; infer_instance

instance etcdReached_timeless {GF : BundledGFunctors} (r : w64) :
    Timeless (etcdReached (GF := GF) r) := by
  unfold etcdReached; infer_instance

/-- Downward closure: etcd has reached every revision below one it has reached. -/
theorem etcdReached_mono {GF : BundledGFunctors} (r r' : w64) (h : sint.Z r' ≤ sint.Z r) :
    etcdReached (GF := GF) r ⊢ etcdReached r' := by
  unfold etcdReached
  iintro (%h0 | ⟨%r1, %h1, #H⟩)
  · ileft; ipureintro; omega
  · iright; iexists r1; iframe H; ipureintro; omega

/-- `etcdReached 0`, for free. -/
theorem etcdReached_zero {GF : BundledGFunctors} : ⊢ etcdReached (GF := GF) (W64 0) := by
  unfold etcdReached
  iintro
  ileft; ipureintro; simp

/-! ## etcd's history: steps (the stream model) -/

/-- An event as etcd stores it (`mvccpb.Event`): its type (`0` put, `1` delete) and its
key-value (for a delete, the key and the revision of the delete). -/
structure EtcdEv where
  typ : w32
  kv : EtcdKv

/-- etcd's order on keys, on key-values. -/
def etcdKvLess (a b : EtcdKv) : Prop := go.GoStringLt a.key b.key

instance etcdKvLess_dec : DecidableRel etcdKvLess := fun a b => go.goStringLt_dec a.key b.key

/-- One event applied to a state (as the store's `applyEv` applies it to a map): a put replaces
or inserts the key-value, a delete removes the key, any other type changes nothing. -/
def applyEvState (s : List EtcdKv) (e : EtcdEv) : List EtcdKv :=
  if e.typ = W32 1 then btDelete etcdKvLess e.kv s
  else if e.typ = W32 0 then btInsert etcdKvLess e.kv s
  else s

/-- Events applied in order. -/
def applyEvsState (s : List EtcdKv) (evs : List EtcdEv) : List EtcdKv :=
  evs.foldl applyEvState s

/-- **A step of etcd's history** (an axiom: a fact about the server). `EtcdStep r0 r1 pfx evs`
says: `r0 ≤ r1`; no event under the prefix `pfx` has a revision strictly between `r0` and
`r1`; and the events under `pfx` at revision `r1` are exactly `evs`, in order (so `r0 < r1` if
`evs ≠ []`; for `evs = []`, nothing under `pfx` changed in `(r0, r1]`). It is what a watch
response tells a watcher whose previous position is `r0`: the events of one revision `r1`
(a batch), or a progress notification at `r1` (`evs = []`). A proposition (etcd's history
is immutable, so the fact is persistent, and it carries no resources, so it is timeless:
it can sit in invariants opened without later credits). Its two properties are
`etcdStep_transfer` and `etcdStep_compose`. -/
axiom EtcdStep (r0 r1 : w64) (pfx : GoString) (evs : List EtcdEv) : Prop

/-- **Transfer.** etcd's state at `r1` is its state at any `a` with `r0 ≤ a < r1` (the same as
at `r0`: nothing changed in between) with the events of the step applied. -/
axiom etcdStep_transfer {GF : BundledGFunctors} (r0 a r1 : w64) (pfx : GoString)
    (s : List EtcdKv) (evs : List EtcdEv) (h : sint.Z r0 ≤ sint.Z a ∧ sint.Z a < sint.Z r1)
    (hstep : EtcdStep r0 r1 pfx evs) :
  etcdState (GF := GF) a pfx s ⊢ etcdState r1 pfx (applyEvsState s evs)

/-- **Composition.** A step with no events (a progress notification) followed by a step: no
event in `(a, b]`, and none in `(b, c)` but `evs` at `c`, is no event in `(a, c)` but `evs` at
`c`. -/
axiom etcdStep_compose (a b c : w64) (pfx : GoString) (evs : List EtcdEv)
    (h1 : EtcdStep a b pfx []) (h2 : EtcdStep b c pfx evs) : EtcdStep a c pfx evs

/-! ### `btInsert`/`btDelete` through a projection -/

section btmap
variable {A B : Type} {lessA : A → A → Prop} {lessB : B → B → Prop} [DecidableRel lessA]
  [DecidableRel lessB]

theorem btInsert_map (f : A → B) (x : A) (l : List A)
    (h : ∀ a ∈ l, (lessB (f a) (f x) ↔ lessA a x) ∧ (lessB (f x) (f a) ↔ lessA x a)) :
    btInsert lessB (f x) (l.map f) = (btInsert lessA x l).map f := by
  induction l with
  | nil => rfl
  | cons a l' ih =>
    have ha := h a List.mem_cons_self
    have ih := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    simp only [List.map_cons, btInsert]
    by_cases h1 : lessA a x
    · simp only [ha.1.2 h1, h1, ↓reduceIte, List.map_cons, ih]
    · have h1' : ¬ lessB (f a) (f x) := fun h' => h1 (ha.1.1 h')
      simp only [h1', h1, ↓reduceIte]
      by_cases h2 : lessA x a
      · simp only [ha.2.2 h2, h2, ↓reduceIte, List.map_cons]
      · have h2' : ¬ lessB (f x) (f a) := fun h' => h2 (ha.2.1 h')
        simp only [h2', h2, ↓reduceIte, List.map_cons]

theorem btDelete_map (f : A → B) (x : A) (l : List A)
    (h : ∀ a ∈ l, (lessB (f a) (f x) ↔ lessA a x) ∧ (lessB (f x) (f a) ↔ lessA x a)) :
    btDelete lessB (f x) (l.map f) = (btDelete lessA x l).map f := by
  induction l with
  | nil => rfl
  | cons a l' ih =>
    have ha := h a List.mem_cons_self
    have ih := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    simp only [List.map_cons, btDelete]
    by_cases h1 : lessA a x
    · simp only [ha.1.2 h1, h1, ↓reduceIte, List.map_cons, ih]
    · have h1' : ¬ lessB (f a) (f x) := fun h' => h1 (ha.1.1 h')
      simp only [h1', h1, ↓reduceIte]
      by_cases h2 : lessA x a
      · simp only [ha.2.2 h2, h2, ↓reduceIte, List.map_cons]
      · have h2' : ¬ lessB (f x) (f a) := fun h' => h2 (ha.2.1 h')
        simp only [h2', h2, ↓reduceIte]

end btmap

/-! ### The store's maps and etcd's states, side by side

A map `m` holding a state `s` (`isEtcdKvs`) is a list of pairs `Z` (map entry, key-value) with
the same key (`PairsOk`), `m = Z.map Prod.fst` and `s = Z.map Prod.snd`; the store's
`applyEv` on `m` and `applyEvState` on `s` act on the same positions. -/

/-- The order of the pairs: by key. -/
def pairLess (a b : KvEntry × EtcdKv) : Prop := go.GoStringLt a.1.1 b.1.1

instance pairLess_dec : DecidableRel pairLess := fun a b => go.goStringLt_dec a.1.1 b.1.1

/-- Every pair has one key. -/
def PairsOk (Z : List (KvEntry × EtcdKv)) : Prop := ∀ z ∈ Z, z.1.1 = z.2.key

theorem etcdKvLess_swo : StrictWeakOrder etcdKvLess where
  irrefl a := goStringLt_irrefl a.key
  trans _ _ _ h1 h2 := goStringLt_trans h1 h2
  incomp_trans a b c h1 h2 h3 h4 := by
    have e1 := goStringLt_eq_of_not_lt h1 h2
    have e2 := goStringLt_eq_of_not_lt h3 h4
    unfold etcdKvLess
    rw [e1, e2]
    exact ⟨goStringLt_irrefl _, goStringLt_irrefl _⟩

/-- One event, on both sides: if the store's `applyEv` succeeds, the pairs after it project to
the new map and to `applyEvState` of the state, and every new pair is an old one or the event's
(its entry `(key, *KeyValue)` and etcd's key-value). -/
theorem pairs_applyEv (Z : List (KvEntry × EtcdKv)) (e : EvModel) (c : EtcdEv) (m' : KvMap)
    (hZ : PairsOk Z) (htyp : e.typ = c.typ) (hkey : e.key = c.kv.key)
    (hm : applyEv (Z.map Prod.fst) e = some m') :
    ∃ Z', Z'.map Prod.fst = m' ∧ Z'.map Prod.snd = applyEvState (Z.map Prod.snd) c ∧
      PairsOk Z' ∧ ∀ z ∈ Z', z ∈ Z ∨ (z = ((e.key, e.kv), c.kv) ∧ c.typ = W32 0) := by
  -- the projections commute with the operations: comparisons are by key on both sides
  have hfst : ∀ (x : KvEntry × EtcdKv), ∀ a ∈ Z,
      (kvLess a.1 x.1 ↔ pairLess a x) ∧ (kvLess x.1 a.1 ↔ pairLess x a) :=
    fun _ _ _ => ⟨Iff.rfl, Iff.rfl⟩
  have hsnd : ∀ (x : KvEntry × EtcdKv), x.1.1 = x.2.key → ∀ a ∈ Z,
      (etcdKvLess a.2 x.2 ↔ pairLess a x) ∧ (etcdKvLess x.2 a.2 ↔ pairLess x a) := by
    intro x hx a ha
    unfold etcdKvLess pairLess
    rw [hZ a ha, hx]
    exact ⟨Iff.rfl, Iff.rfl⟩
  unfold applyEv at hm
  unfold applyEvState
  by_cases h1 : e.typ = W32 1
  · rw [if_pos h1] at hm
    rw [if_pos (htyp ▸ h1)]
    split at hm
    · cases hm
      refine ⟨btDelete pairLess ((e.key, null), c.kv) Z, ?_, ?_, ?_, ?_⟩
      · exact (btDelete_map (lessA := pairLess) (lessB := kvLess) Prod.fst
          ((e.key, null), c.kv) Z (hfst _)).symm
      · rw [← btDelete_map (lessA := pairLess) (lessB := etcdKvLess) Prod.snd
          ((e.key, null), c.kv) Z (hsnd _ hkey)]
      · exact fun z hz => hZ z (btDelete_mem hz)
      · exact fun z hz => Or.inl (btDelete_mem hz)
    · cases hm
  · rw [if_neg h1] at hm
    rw [if_neg (by rw [← htyp]; exact h1)]
    by_cases h0 : e.typ = W32 0
    · rw [if_pos h0] at hm
      rw [if_pos (htyp ▸ h0)]
      cases hm
      refine ⟨btInsert pairLess ((e.key, e.kv), c.kv) Z, ?_, ?_, ?_, ?_⟩
      · exact (btInsert_map (lessA := pairLess) (lessB := kvLess) Prod.fst
          ((e.key, e.kv), c.kv) Z (hfst _)).symm
      · rw [← btInsert_map (lessA := pairLess) (lessB := etcdKvLess) Prod.snd
          ((e.key, e.kv), c.kv) Z (hsnd _ hkey)]
      · intro z hz
        rcases btInsert_mem hz with rfl | hz
        · exact hkey
        · exact hZ z hz
      · intro z hz
        rcases btInsert_mem hz with rfl | hz
        · exact Or.inr ⟨rfl, htyp ▸ h0⟩
        · exact Or.inl hz
    · rw [if_neg h0] at hm
      rw [if_neg (by rw [← htyp]; exact h0)]
      cases hm
      exact ⟨Z, rfl, rfl, hZ, fun z hz => Or.inl hz⟩

/-- A batch of events, on both sides (`applyBatch` succeeding). -/
theorem pairs_applyBatch : ∀ (Z : List (KvEntry × EtcdKv)) (evs : List EvModel)
    (cs : List EtcdEv) (m' : KvMap), PairsOk Z → evs.length = cs.length →
    (∀ (i : Nat) (e : EvModel) (c : EtcdEv), evs[i]? = some e → cs[i]? = some c →
      e.typ = c.typ ∧ e.key = c.kv.key) →
    applyBatch (Z.map Prod.fst) evs = (m', true) →
    ∃ Z', Z'.map Prod.fst = m' ∧ Z'.map Prod.snd = applyEvsState (Z.map Prod.snd) cs ∧
      PairsOk Z' ∧ ∀ z ∈ Z', z ∈ Z ∨ ∃ (i : Nat) (e : EvModel) (c : EtcdEv), evs[i]? = some e ∧
        cs[i]? = some c ∧ z = ((e.key, e.kv), c.kv) ∧ c.typ = W32 0
  | Z, [], [], m', hZ, _, _, h => by
    simp only [applyBatch, Prod.mk.injEq] at h
    exact ⟨Z, h.1, rfl, hZ, fun z hz => Or.inl hz⟩
  | Z, e :: es, c :: cs, m', hZ, hlen, hmatch, h => by
    have ⟨htyp, hkey⟩ := hmatch 0 e c rfl rfl
    simp only [applyBatch] at h
    split at h
    · rename_i m1 hm1
      obtain ⟨Z1, h1f, h1s, hZ1, hZ1m⟩ := pairs_applyEv Z e c m1 hZ htyp hkey hm1
      rw [← h1f] at h
      obtain ⟨Z2, h2f, h2s, hZ2, hZ2m⟩ := pairs_applyBatch Z1 es cs m' hZ1
        (by simpa using hlen) (fun i e' c' he hc => hmatch (i + 1) e' c' he hc) h
      refine ⟨Z2, h2f, ?_, hZ2, ?_⟩
      · rw [h2s, h1s]; rfl
      · intro z hz
        rcases hZ2m z hz with hz | ⟨i, e', c', he, hc, rfl, ht⟩
        · rcases hZ1m z hz with hz | ⟨rfl, ht⟩
          · exact Or.inl hz
          · exact Or.inr ⟨0, e, c, rfl, rfl, rfl, ht⟩
        · exact Or.inr ⟨i + 1, e', c', he, hc, rfl, ht⟩
    · simp at h
  | _, [], _ :: _, _, _, hlen, _, _ => by simp at hlen
  | _, _ :: _, [], _, _, hlen, _, _ => by simp at hlen

theorem applyEvsState_sorted (s : List EtcdKv) (cs : List EtcdEv) (h : s.Pairwise etcdKvLess) :
    (applyEvsState s cs).Pairwise etcdKvLess := by
  induction cs generalizing s with
  | nil => exact h
  | cons c cs ih =>
    apply ih
    unfold applyEvState
    split
    · exact btDelete_sorted h
    · split
      · exact btInsert_sorted etcdKvLess_swo h
      · exact h

theorem applyEvsState_mem (s : List EtcdKv) (cs : List EtcdEv) (v : EtcdKv)
    (h : v ∈ applyEvsState s cs) : v ∈ s ∨ ∃ c ∈ cs, c.typ = W32 0 ∧ v = c.kv := by
  induction cs generalizing s with
  | nil => exact Or.inl h
  | cons c cs ih =>
    rcases ih _ h with h | ⟨c', hc', ht, rfl⟩
    · unfold applyEvState at h
      split at h
      · exact Or.inl (btDelete_mem h)
      · split at h
        · rcases btInsert_mem h with rfl | h
          · exact Or.inr ⟨c, List.mem_cons_self, by assumption, rfl⟩
          · exact Or.inl h
        · exact Or.inl h
    · exact Or.inr ⟨c', List.mem_cons_of_mem _ hc', ht, rfl⟩

theorem pairsOk_zip (m : KvMap) (s : List EtcdKv) (h : m.map Prod.fst = s.map EtcdKv.key) :
    PairsOk (m.zip s) := by
  intro z hz
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hz
  rw [List.getElem?_zip_eq_some] at hi
  have := congrArg (·[i]?) h
  simp only [List.getElem?_map, hi.1, hi.2, Option.map_some, Option.some.injEq] at this
  exact this


section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `l` is a `*mvccpb.KeyValue` whose fields hold `v`, read-only (on the fields, as `kvAt`). -/
def kvValAt (l : Loc) (v : EtcdKv) : IProp GF :=
  iprop(∃ keySl valSl : GoSlice,
    structFieldRef mvccpb.KeyValue go!"Key" l ↦□ keySl ∗ keySl ↦*□ v.key ∗
    structFieldRef mvccpb.KeyValue go!"CreateRevision" l ↦□ v.createRev ∗
    structFieldRef mvccpb.KeyValue go!"ModRevision" l ↦□ v.modRev ∗
    structFieldRef mvccpb.KeyValue go!"Version" l ↦□ v.version ∗
    structFieldRef mvccpb.KeyValue go!"Value" l ↦□ valSl ∗ valSl ↦*□ v.value ∗
    structFieldRef mvccpb.KeyValue go!"Lease" l ↦□ v.lease)

instance kvValAt_persistent (l : Loc) (v : EtcdKv) : Persistent (kvValAt (GF := GF) l v) := by
  unfold kvValAt; infer_instance

/-- The `*KeyValue`s of `m` hold, in order, the key-values `s`. -/
def kvValsAt (m : KvMap) (s : List EtcdKv) : IProp GF :=
  iprop(□ ∀ (i : Nat) (e : KvEntry) (v : EtcdKv), ⌜m[i]? = some e⌝ -∗ ⌜s[i]? = some v⌝ -∗
    kvValAt e.2 v)

instance kvValsAt_persistent (m : KvMap) (s : List EtcdKv) :
    Persistent (kvValsAt (GF := GF) m s) := by
  unfold kvValsAt; infer_instance

/-- The map `m` is etcd's state at revision `rev`, restricted to the prefix `pfx`. -/
def isEtcdKvs (rev : w64) (pfx : GoString) (m : KvMap) : IProp GF :=
  iprop(∃ s : List EtcdKv, □ etcdState rev pfx s ∗ ⌜m.map Prod.fst = s.map EtcdKv.key⌝ ∗
    ⌜EtcdStateWf pfx s⌝ ∗ kvValsAt m s)

instance isEtcdKvs_persistent (rev : w64) (pfx : GoString) (m : KvMap) :
    Persistent (isEtcdKvs (GF := GF) rev pfx m) := by
  unfold isEtcdKvs; infer_instance

/-- Two maps that are etcd's state at the same revision have the same keys and contents. -/
theorem isEtcdKvs_agree (rev : w64) (pfx : GoString) (m m' : KvMap) :
    isEtcdKvs (GF := GF) rev pfx m ∗ isEtcdKvs rev pfx m' ⊢
      ⌜m.map Prod.fst = m'.map Prod.fst⌝ ∗ ∃ s, kvValsAt m s ∗ kvValsAt m' s := by
  unfold isEtcdKvs
  iintro ⟨⟨%s, #Hs, %Hk, %-, #Hv⟩, ⟨%s', #Hs', %Hk', %-, #Hv'⟩⟩
  ihave %Heq := etcdState_agree rev pfx s s' $$ [$Hs $Hs']
  subst Heq
  isplitr
  · ipureintro; rw [Hk, Hk']
  iexists s
  isplitl []
  · iexact Hv
  · iexact Hv'

/-- The events `evs` (as the store reads them) are etcd's events `cs`, pointwise: the same type,
key and revision, and each event's `*KeyValue` holds etcd's key-value (`kvValAt`). -/
def evsMatch (evs : List EvModel) (cs : List EtcdEv) : IProp GF :=
  iprop(⌜evs.length = cs.length ∧ ∀ (i : Nat) (e : EvModel) (c : EtcdEv), evs[i]? = some e →
      cs[i]? = some c → e.typ = c.typ ∧ e.key = c.kv.key ∧ e.rev = c.kv.modRev⌝ ∗
    □ ∀ (i : Nat) (e : EvModel) (c : EtcdEv), ⌜evs[i]? = some e⌝ -∗ ⌜cs[i]? = some c⌝ -∗
      kvValAt e.kv c.kv)

instance evsMatch_persistent (evs : List EvModel) (cs : List EtcdEv) :
    Persistent (evsMatch (GF := GF) evs cs) := by
  unfold evsMatch; infer_instance

/-- **The bridge**: a map that is etcd's state at `Y`, and a step `p → r` with `p ≤ Y < r` whose
events the store's batch `evs` matches, give, when the store applies the batch without failing,
etcd's state at `r` (puts under the prefix keep the map's keys under it). This certifies the
snapshot the store's `Apply` appends for the batch. -/
theorem isEtcdKvs_step (Y p r : w64) (pfx : GoString) (m m' : KvMap) (evs : List EvModel)
    (cs : List EtcdEv) (hY : sint.Z p ≤ sint.Z Y ∧ sint.Z Y < sint.Z r)
    (hstep : EtcdStep p r pfx cs) (hpfx : ∀ c ∈ cs, c.typ = W32 0 → pfx <+: c.kv.key)
    (happ : applyBatch m evs = (m', true)) :
    isEtcdKvs (GF := GF) Y pfx m ∗ evsMatch evs cs ⊢ isEtcdKvs r pfx m' := by
  unfold isEtcdKvs evsMatch
  iintro ⟨⟨%s, #Hs, %Hk, %Hwf, #Hv⟩, ⟨%Hm, #Hkv⟩⟩
  have hlen : m.length = s.length := by
    have := congrArg List.length Hk; simpa using this
  have hm : (m.zip s).map Prod.fst = m := List.map_fst_zip (by omega)
  have hs : (m.zip s).map Prod.snd = s := List.map_snd_zip (by omega)
  rw [← hm] at happ
  obtain ⟨Z', hZf, hZs, hZok, hZm⟩ := pairs_applyBatch (m.zip s) evs cs m' (pairsOk_zip m s Hk)
    Hm.1 (fun i e c he hc => ⟨(Hm.2 i e c he hc).1, (Hm.2 i e c he hc).2.1⟩) happ
  rw [hs] at hZs
  iexists applyEvsState s cs
  isplitl []
  · imodintro
    iapply etcdStep_transfer p Y r pfx s cs hY hstep $$ Hs
  isplitr
  · ipureintro
    rw [← hZf, ← hZs, List.map_map, List.map_map]
    exact List.map_congr_left (fun z hz => hZok z hz)
  isplitr
  · ipureintro
    refine ⟨?_, ?_⟩
    · have h0 : s.Pairwise etcdKvLess := by
        have := (List.pairwise_map (l := s) (f := EtcdKv.key) (R := go.GoStringLt)).1 Hwf.1
        exact this
      have h := applyEvsState_sorted s cs h0
      exact (List.pairwise_map (f := EtcdKv.key) (R := go.GoStringLt)).2 h
    · intro v hv
      rcases applyEvsState_mem s cs v hv with hv | ⟨c, hc, ht, rfl⟩
      · exact Hwf.2 v hv
      · exact hpfx c hc ht
  -- the contents, pair by pair
  unfold kvValsAt
  imodintro
  iintro %i %e %v %He %Hv'
  rw [← hZf, List.getElem?_map] at He
  rw [← hZs, List.getElem?_map] at Hv'
  cases hz : Z'[i]? with
  | none => rw [hz] at He; cases He
  | some z =>
    rw [hz] at He Hv'
    simp only [Option.map_some, Option.some.injEq] at He Hv'
    subst He Hv'
    rcases hZm z (List.mem_of_getElem? hz) with hz' | ⟨k, e', c, he', hc, rfl, -⟩
    · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hz'
      rw [List.getElem?_zip_eq_some] at hj
      iapply Hv $$ %j %z.1 %z.2 %hj.1 %hj.2
    · iapply Hkv $$ %k %e' %c %he' %hc

instance evsMatch_timeless (evs : List EvModel) (cs : List EtcdEv) :
    Timeless (evsMatch (GF := GF) evs cs) := by
  unfold evsMatch kvValAt; infer_instance

/-- The cache's certificate for the demux's batches (the demux's `C`): the batch `b` follows
revision `p` in etcd's history under the prefix `pfx`: its events are etcd's events `cs`
(`evsMatch`), with a step `p → batchRev b` (`EtcdStep`: nothing under the prefix in between),
the puts under the prefix; and etcd has reached the batch's revision (`etcdReached`). What the client's watch stream gives the cache's writer (`isEtcdWatchChan`)
and the demux hands, through `demuxPub`, to each watcher's consumer. -/
def etcdStepCertBody (pfx : GoString) (p : w64) (b : Batch) : IProp GF :=
  iprop(∃ cs : List EtcdEv, evsMatch b cs ∗
    ⌜EtcdStep p (batchRev b) pfx cs ∧ ∀ c ∈ cs, c.typ = W32 0 → pfx <+: c.kv.key⌝ ∗
    etcdReached (batchRev b))

instance etcdStepCertBody_timeless (pfx : GoString) (p : w64) (b : Batch) :
    Timeless (etcdStepCertBody (GF := GF) pfx p b) := by
  unfold etcdStepCertBody; infer_instance

instance etcdStepCertBody_persistent (pfx : GoString) (p : w64) (b : Batch) :
    Persistent (etcdStepCertBody (GF := GF) pfx p b) := by
  unfold etcdStepCertBody; infer_instance

/-- The cache's demux certificate (`DemuxCert`): batches by `etcdStepCertBody`, progress
notifications' revisions by `etcdReached`. -/
def etcdStepCert (pfx : GoString) : DemuxCert GF where
  cert := etcdStepCertBody pfx
  timeless := fun _ _ => inferInstance
  prog := etcdReached
  prog_timeless := fun _ => inferInstance
  prog_mono := etcdReached_mono
  prog_zero := etcdReached_zero
  cert_prog := fun p b => by
    unfold etcdStepCertBody
    iintro ⟨%cs, -, -, H⟩
    iexact H

theorem etcdStepCert_prog (pfx : GoString) :
    (etcdStepCert (GF := GF) pfx).prog = etcdReached := rfl

/-- The cache's store certificate: a snapshot `(r, m)` is etcd's state at `r`, restricted to the
cache's prefix. -/
def etcdCert (pfx : GoString) : w64 → KvMap → IProp GF := fun r m => isEtcdKvs r pfx m

/-! ## The client's `KV.Get` -/

/-- The `*clientv3.GetResponse` `resp` has a header (non-nil) with revision `r`, read-only. -/
def getRespRev (resp : Loc) (r : w64) : IProp GF :=
  iprop(∃ hdr : Loc, structFieldRef go_etcd_io.etcd.client.v3.GetResponse go!"Header" resp ↦□ hdr ∗
    ⌜hdr ≠ null⌝ ∗ structFieldRef etcdserverpb.ResponseHeader go!"Revision" hdr ↦□ r)

instance getRespRev_persistent (resp : Loc) (r : w64) :
    Persistent (getRespRev (GF := GF) resp r) := by
  unfold getRespRev; infer_instance

/-- The `*clientv3.GetResponse` `resp` lists the `*KeyValue`s of `m`, read-only. -/
def getRespKvs (resp : Loc) (m : KvMap) : IProp GF :=
  iprop(∃ sl : GoSlice, structFieldRef go_etcd_io.etcd.client.v3.GetResponse go!"Kvs" resp ↦□ sl ∗
    sl ↦*□ (m.map Prod.snd))

instance getRespKvs_persistent (resp : Loc) (m : KvMap) :
    Persistent (getRespKvs (GF := GF) resp m) := by
  unfold getRespKvs; infer_instance

end defs

/-- A get of every key with the prefix `pfx` at the latest revision: what `WithPrefix()` makes of
`OpGet(pfx)` (from `"\x00"` on for the empty prefix), and no other option that changes the answer
(revision, limit, sort, revision filters, keys-only, count-only; serializable is allowed). -/
def OpFull.isPrefixGet (pfx : GoString) (o : OpFull) : Bool :=
  decide (o.t = W64 1 ∧ o.keysOnly = false ∧ o.base.countOnly = false ∧ o.base.sortSet = false ∧
    o.base.limit = W64 0 ∧ o.base.rev = W64 0 ∧ o.base.minModRev = W64 0 ∧
    o.base.maxModRev = W64 0 ∧ o.base.minCreateRev = W64 0 ∧ o.base.maxCreateRev = W64 0 ∧
    (if pfx = [] then o.key = [W8 0] ∧ o.base.rangeEnd = [W8 0]
     else o.key = pfx ∧ o.base.rangeEnd = prefixRangeEnd pfx))

section client
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- What `kv.Get` returns for the `Op` `o`, on a cache of prefix `pfx`, called with the knowledge
that etcd has reached `lo`: any error; or, on success, a response whose header revision `r` is one
at which etcd had a state, which etcd has reached (`etcdReached r`), below `2 ^ 63 - 1` (etcd's
revisions are; `getWatch` watches from `r + 1`), and at least `lo` unless the request is
serializable (**linearizability**: a linearizable get started after revision `lo` was observed
sees it; a serializable one may be served by a lagging member), and which lists exactly that state
if `o` is a prefix get. -/
def kvGetResult (pfx : GoString) (lo : w64) (o : OpFull) (resp : Loc) (err : GoInterface) :
    IProp GF :=
  iprop(⌜err ≠ GoInterface.nil⌝ ∨
    (⌜err = GoInterface.nil⌝ ∗ ∃ (r : w64) (m : KvMap), getRespRev resp r ∗ isEtcdKvs r pfx m ∗
      etcdReached r ∗
      ⌜(o.base.serializable = false → sint.Z lo ≤ sint.Z r) ∧ sint.Z r < 2 ^ 63 - 1⌝ ∗
      (if o.isPrefixGet pfx then getRespKvs resp m else iprop(True))))

instance kvGetResult_persistent (pfx : GoString) (lo : w64) (o : OpFull) (resp : Loc)
    (err : GoInterface) : Persistent (kvGetResult (GF := GF) pfx lo o resp err) := by
  unfold kvGetResult; split <;> infer_instance

/-- The `clientv3.KV` interface value `kv` talks to etcd, for a cache of prefix `pfx`: the triple
of its `Get(ctx, key, opts...)` (a range request: `OpGet(key, opts...)` must not panic and must
be a range), with any context, options with model transformers `gs`, and any revision `lo` the
caller knows etcd has reached (`etcdReached lo`; `0` is free): the response is
`kvGetResult pfx lo`, at least `lo` unless serializable (linearizability). -/
def isEtcdKV (kv : GoInterfaceOk) (pfx : GoString) : IProp GF :=
  iprop(□ ∀ (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (key : GoString)
      (sl : GoSlice) (gs : List (OpFull → OpFull)) (lo : w64),
    {{ context.isContext ctx cs ∗ optsAt sl gs ∗ etcdReached lo ∗
        ⌜¬ opGetPanics gs ∧ (opGetModel key gs).t = W64 1⌝ }}
      (App (App (App (Val #(methods kv.ty go!"Get" kv.v)) (Val #(GoInterface.ok ctx)))
        (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        kvGetResult pfx lo (opGetModel key gs) resp err }})

instance isEtcdKV_persistent (kv : GoInterfaceOk) (pfx : GoString) :
    Persistent (isEtcdKV (GF := GF) kv pfx) := by
  unfold isEtcdKV; infer_instance

end client

/-! ## The client's `Watcher.Watch` -/

/-- A prefix watch on `pfx` from revision `rev`, as `watchEvents` makes it: `WithPrefix` (from
`"\x00"` for the empty prefix), `WithRev(rev)`, `WithProgressNotify`, `WithCreatedNotify`, and none
of the options that change which events are sent or how (`WithPrevKV`, `WithFragment`, the event
filters). -/
def OpFull.isPrefixWatch (pfx : GoString) (rev : w64) (o : OpFull) : Bool :=
  decide (o.t = W64 1 ∧ o.base.rev = rev ∧ o.base.progressNotify = true ∧
    o.base.createdNotify = true ∧ o.base.prevKV = false ∧ o.base.fragment = false ∧
    o.base.filterPut = false ∧ o.base.filterDelete = false ∧
    (if pfx = [] then o.key = [W8 0] ∧ o.base.rangeEnd = [W8 0]
     else o.key = pfx ∧ o.base.rangeEnd = prefixRangeEnd pfx))

/-- The ghost names of a client watch channel: the channel's (an SPSC channel: the client
produces, the cache's watch loop consumes) and the watch's positions (`cur`: the revision the
stream is at before each response, a monotone list). -/
structure EtcdWatchNames where
  spsc : SpscNames
  cur : GName

section watch
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `resp.Err() != nil` (`WatchResponse.Err`): a close error, a compaction, or a cancel. -/
def watchErr (v : go_etcd_io.etcd.client.v3.WatchResponse) : Prop :=
  v.closeErr' ≠ interface.nil ∨ v.CompactRevision' ≠ W64 0 ∨ v.Canceled' = true

/-- etcd's batches `bs` follow `prev` one by one, exactly: each is the step (`etcdStepCertBody`)
after the previous one's revision (`prev` for the first), and above it. -/
def watchChain (pfx : GoString) : w64 → List Batch → IProp GF
  | _, [] => iprop(True)
  | prev, b :: bs => iprop(etcdStepCertBody pfx prev b ∗ ⌜sint.Z prev < sint.Z (batchRev b)⌝ ∗
      watchChain pfx (batchRev b) bs)

instance watchChain_persistent (pfx : GoString) (prev : w64) (bs : List Batch) :
    Persistent (watchChain (GF := GF) pfx prev bs) := by
  induction bs generalizing prev with
  | nil => unfold watchChain; infer_instance
  | cons b bs ih => unfold watchChain; infer_instance

/-- **etcd's watch contract**, for one response `v` (modelled by `r`) received when the watch is
at revision `c`, after which it is at `c'`. Its header revision is below `2^63 - 1` (etcd's
revisions are), and it is one of:
* an error (`resp.Err() != nil`: a close error, a compaction, a cancel); the position is kept;
* the created notification (no events); the position is kept; etcd has reached its header
  revision (`etcdReached`, free if `0`);
* a progress notification at `p ≥ c`: nothing under the prefix changed in `(c, p]`; the
  position becomes `p`; etcd has reached `p`;
* events, sorted by revision, above `c` and below `2^63 - 1`, grouped by revision into batches,
  each the step after the previous one (`watchChain`, from `c`, which says that etcd has reached
  each batch's revision); the position becomes the last event's revision. -/
def watchRespOk (pfx : GoString) (c c' : w64) (v : go_etcd_io.etcd.client.v3.WatchResponse)
    (r : RespModel) : IProp GF :=
  iprop(⌜sint.Z r.hdrRev < 2 ^ 63 - 1⌝ ∗
    (⌜watchErr v ∧ c' = c⌝ ∨
     (⌜¬ watchErr v ∧ r.created = true ∧ r.events = [] ∧ c' = c⌝ ∗ etcdReached r.hdrRev) ∨
     (⌜¬ watchErr v ∧ r.isProgressNotify = true ∧ sint.Z c ≤ sint.Z r.hdrRev ∧ c' = r.hdrRev ∧
       EtcdStep c r.hdrRev pfx []⌝ ∗ etcdReached r.hdrRev) ∨
     (⌜¬ watchErr v ∧ r.events ≠ [] ∧ EvRevSorted r.events ∧
        (∀ e ∈ r.events, sint.Z c < sint.Z e.rev ∧ sint.Z e.rev < 2 ^ 63 - 1) ∧
        r.events.getLast?.map EvModel.rev = some c'⌝ ∗
      watchChain pfx c (splitBatches r.events))))

instance watchRespOk_persistent (pfx : GoString) (c c' : w64)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) :
    Persistent (watchRespOk (GF := GF) pfx c c' v r) := by
  unfold watchRespOk; infer_instance

/-- The `i`-th response `v` of the channel: modelled by `r`, and etcd's watch contract from the
position before it to the one after it. -/
def etcdWatchElem (γ : EtcdWatchNames) (pfx : GoString) (i : Int)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) : IProp GF :=
  iprop(∃ (r : RespModel) (c c' : w64), respAt v r ∗ monoListIdxOwn γ.cur i.toNat c ∗
    monoListIdxOwn γ.cur (i.toNat + 1) c' ∗ watchRespOk pfx c c' v r)

/-- `ch` is the channel of a client watch on the prefix `pfx` (persistent): every response it
delivers satisfies etcd's watch contract (`etcdWatchElem`). -/
def isEtcdWatchChan (ch : Loc) (γ : EtcdWatchNames) (pfx : GoString) : IProp GF :=
  isSpsc γ.spsc ch (etcdWatchElem γ pfx) (fun _ => iprop(True))

instance isEtcdWatchChan_persistent (ch : Loc) (γ : EtcdWatchNames) (pfx : GoString) :
    Persistent (isEtcdWatchChan (GF := GF) ch γ pfx) := by
  unfold isEtcdWatchChan; infer_instance

/-- The consumer of a client watch channel: it has received `n` responses, and the watch is at
revision `cursor`. -/
def etcdWatchConsumer (γ : EtcdWatchNames) (n : Nat) (cursor : w64) : IProp GF :=
  iprop(∃ vs : List go_etcd_io.etcd.client.v3.WatchResponse, spscConsumer γ.spsc vs ∗
    ⌜vs.length = n⌝ ∗ monoListIdxOwn γ.cur n cursor)

/-- **The client's `Watcher`** `w`, for a cache of prefix `pfx` (a definition, like `isEtcdKV`: the
assumption a caller makes of `client.Watcher`): `w.Watch(ctx, key, opts...)` with the options of a
prefix watch on `pfx` from revision `rev > 0` (`isPrefixWatch`; the options must not make
`OpWatch` panic) returns a channel of etcd's watch responses, starting at revision `rev - 1`. -/
def isEtcdWatcher (w : GoInterfaceOk) (pfx : GoString) : IProp GF :=
  iprop(□ ∀ (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (key : GoString)
      (sl : GoSlice) (gs : List (OpFull → OpFull)) (rev : w64),
    {{ context.isContext ctx cs ∗ optsAt sl gs ∗
        ⌜(opWatchModel key gs).isPrefixWatch pfx rev = true ∧ ¬ opWatchPanics key gs ∧
          0 < sint.Z rev⌝ }}
      (App (App (App (Val #(methods w.ty go!"Watch" w.v)) (Val #(GoInterface.ok ctx)))
        (Val #key)) (Val #sl))
    {{ (ch : Loc) (γ : EtcdWatchNames), RET #ch;
        isEtcdWatchChan ch γ pfx ∗ etcdWatchConsumer γ 0 (rev - W64 1) }})

instance isEtcdWatcher_persistent (w : GoInterfaceOk) (pfx : GoString) :
    Persistent (isEtcdWatcher (GF := GF) w pfx) := by
  unfold isEtcdWatcher; infer_instance

/-- **The client's `RequestProgress`** (`clientv3.Watcher`'s, through the cache's
`progressNotifier` interface): `w.RequestProgress(ctx)` returns some error, with no logical effect.
etcd's progress notification shows up on the watch streams, where it is already modelled (a
progress response of `watchRespOk`). A definition, like `isEtcdWatcher`. -/
def isEtcdProgressNotifier (w : GoInterfaceOk) : IProp GF :=
  iprop(□ ∀ (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)),
    {{ context.isContext ctx cs }}
      (App (Val #(methods w.ty go!"RequestProgress" w.v)) (Val #(GoInterface.ok ctx)))
    {{ (err : GoInterface), RET #err; True }})

instance isEtcdProgressNotifier_persistent (w : GoInterfaceOk) :
    Persistent (isEtcdProgressNotifier (GF := GF) w) := by
  unfold isEtcdProgressNotifier; infer_instance

/-- **Receiving** from a client watch channel (the atomic update of Perennial's channel specs,
for a `select` case): with `ok`, a response `v` modelled by `r` satisfying etcd's watch contract
from the consumer's position `cursor` to a new one `c'`; without, the channel was closed (and the
consumer is done). -/
theorem etcdWatch_recv_au (ch : Loc) (γ : EtcdWatchNames) (pfx : GoString) (n : Nat)
    (cursor : w64) (Φ : go_etcd_io.etcd.client.v3.WatchResponse → Bool → IProp GF) :
    ⊢ isEtcdWatchChan ch γ pfx -∗ £ 1 ∗ £ 1 -∗ etcdWatchConsumer γ n cursor -∗
      ▷ (∀ (v : go_etcd_io.etcd.client.v3.WatchResponse) (ok : Bool),
          (if ok then iprop(∃ (r : RespModel) (c' : w64), respAt v r ∗
              watchRespOk pfx cursor c' v r ∗ etcdWatchConsumer γ (n + 1) c')
           else iprop(⌜v = zero_val go_etcd_io.etcd.client.v3.WatchResponse⌝)) -∗ Φ v ok) -∗
      recvAu γ.spsc.chanName go_etcd_io.etcd.client.v3.WatchResponse Φ := by
  iintro #Hch Hlc Hcons HΦ
  unfold etcdWatchConsumer
  icases Hcons with ⟨%vs, Hcons, %Hlen, #Hcur⟩
  unfold isEtcdWatchChan
  iapply spsc_rcv_au γ.spsc ch (etcdWatchElem γ pfx) (fun _ => iprop(True)) vs Φ $$ Hch Hlc Hcons
  inext
  iintro %v %ok H
  cases ok
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases H with ⟨-, %Hv⟩
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro; exact Hv
  · simp only [↓reduceIte]
    icases H with ⟨HP, Hcons⟩
    unfold etcdWatchElem
    icases HP with ⟨%r, %c0, %c', #Hr, #Hc0, #Hc', #Hok⟩
    have hi : ((vs.length : Int)).toNat = n := by rw [Hlen]; simp
    rw [hi]
    ihave %Heq := mono_list_idx_agree γ.cur n c0 cursor $$ Hc0 Hcur
    subst Heq
    iapply HΦ
    simp only [↓reduceIte]
    iexists r, c'
    iframe Hr Hok
    iexists vs ++ [v]
    iframe Hcons
    iframe Hc'
    ipureintro; simp [Hlen]

end watch

end EtcdGrove
end Perennial
