/-
Lean-first (no Rocq counterpart).

# The bridge: the store's watch stream is the driver's (k8s 7f-6 stage C, Draft D1)

What the store's watch spec promises (`kStreamOk`, `WatchDefs.lean`: over etcd's history `σ` and
the store's objects `DObj`) gives what the driver's check needs (`StreamOkL`, `KWatchStream.lean`:
over the configuration's history and the driver's `Obj`), when the configuration and etcd are
related (`KRelH`, `RefineList.lean`) and etcd's history is the store's (`KHistW`: no compaction,
every value under the prefix decodes, at most one change under the prefix per revision). Plan:
`notes/k8s-7f6c-plan.md`.

- `kToWEv`, `kWEvRel`: a store event as the driver records it;
- `kModeOk`: the request's mode as the driver makes it (`kModeOk_of`);
- **`streamOkL_of_kStreamOk`**: the bridge;
- `histWf_of_krel`: the histories satisfy `HistWf` (the other premise of `watchOkL_of_stream`);
- `kStreamOk_hist`: the stream at a longer state of the history.

The core is one revision at a time (`evAtL_eq`): revision `r`'s watch events in scope are the
driver's change event at `r`, since the revision changes one key under the prefix at most
(`rev_cases`), and a create is a put of a key absent before (`crOk`: every key-value's create
revision is positive and at most its mod revision).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.KWatchStream
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RefineList
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.WatchDefs
public import Proof.go_etcd_io.etcd.client.v3.WatchContent

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open k8s
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item)

section go
variable [GooseExts]

/-! ## The vocabulary -/

/-- **etcd's history, as the bridge reads it** (at the configuration's state): no compaction;
every revision's key-values under the prefix decode, with mod revisions from `1` to the revision
(`kvWfHist` of the driver's store, `CfgD`); at most one change under the prefix per revision (the
store's transactions are single-operation: `KvOne`, `Updates.lean`). -/
structure KHistW (σ : KVState) : Prop where
  comp : σ.compacted = 0
  wf : ∀ r ≤ σ.rev, ∀ v ∈ (σ.at r).kvs, (kpfxD <+: v.key → driverCodec.dec v.value ≠ none) ∧
    0 < uint.nat v.modRev ∧ uint.nat v.modRev ≤ r
  one : ∀ r ≤ σ.rev, ((σ.changesAt r).filter fun ch => decide (kpfxD <+: ch.key)).length ≤ 1

/-- **The request's mode as the driver makes it**: the requested revision; a watch-list
(`SendInit = 2`) asks for the initial events and the initial-events-end bookmark; any other watch
for neither. -/
def kModeOk (x : Input) (req : Nat) (m : KWatchMode) : Prop :=
  m.req = req ∧ (x.SendInit' = W64 2 → m.forceInit = true ∧ m.bmReq = true) ∧
    (x.SendInit' ≠ W64 2 → m.forceInit = false)

/-- `SendInitialEvents` as `watchOptions` sets it (`SendInit`: 2 true, 1 false, else unset). -/
def sieOfL (x : Input) : Option Bool :=
  if x.SendInit' = W64 2 then some true else if x.SendInit' = W64 1 then some false else none

/-- **A store event as the driver records it** (`toWEvent` of the event `wevAt` describes): its
type, and its object at its resource version with its annotation. -/
def kToWEv (e : KWEv DObj) : WEv :=
  ⟨e.t, { e.o.toObj (W64 (e.rv : Int)) with Annotated' := e.ann }⟩

/-- **The driver's record `w` of the store event `e`**: the same type, and for any event but an
Error event (whose object the check drops) `kToWEv`. -/
def kWEvRel (e : KWEv DObj) (w : WEv) : Prop := w.t = e.t ∧ (e.t ≠ 4 → w = kToWEv e)

/-! ## Lists -/

theorem filter_le_one {α : Type} (p : α → Bool) :
    ∀ (l : List α), (l.filter p).length ≤ 1 →
      (∀ a ∈ l, p a = false) ∨
        ∃ pre c post, l = pre ++ c :: post ∧ p c = true ∧ ∀ a ∈ pre ++ post, p a = false
  | [], _ => Or.inl (by simp)
  | a :: l, h => by
    by_cases hp : p a = true
    · right
      rw [List.filter_cons, if_pos hp, List.length_cons] at h
      have hl : l.filter p = [] := List.eq_nil_of_length_eq_zero (by omega)
      refine ⟨[], a, l, rfl, hp, fun b hb => ?_⟩
      simp only [List.nil_append] at hb
      have := List.filter_eq_nil_iff.1 hl b hb
      simpa using this
    · rw [List.filter_cons, if_neg hp] at h
      rcases filter_le_one p l h with h1 | ⟨pre, c, post, rfl, hc, hr⟩
      · left
        intro b hb
        rcases List.mem_cons.1 hb with rfl | hb
        · simpa using hp
        · exact h1 b hb
      · right
        refine ⟨a :: pre, c, post, rfl, hc, fun b hb => ?_⟩
        rcases List.mem_cons.1 hb with rfl | hb
        · simpa using hp
        · exact hr b hb

/-! ## etcd's history, one revision at a time -/

/-- The store at revision `r` (no compaction, `1 ≤ r ≤ rev`) is revision `r`'s changes applied
to the store before. -/
theorem at_succ_kvs (σ : KVState) (h0 : σ.compacted = 0) (r : Nat) (h1 : 1 ≤ r)
    (hr : r ≤ σ.rev) :
    (σ.at r).kvs = mvcc.applyChanges (W64 (r : Int)) (σ.at (r - 1)).kvs (σ.changesAt r) := by
  have hl : r - 1 < σ.changes.length := by unfold KVState.rev at hr; omega
  rw [KVState.at_kvs σ r (by omega), KVState.at_kvs σ (r - 1) (by omega)]
  unfold KVState.changesAt
  rw [if_neg (by omega), h0]
  rw [show r - 0 = (r - 1) + 1 by omega, List.take_add_one, List.getElem?_eq_getElem hl,
    Option.toList_some, runFrom_append, List.length_take, Nat.min_eq_left (by omega),
    show r - 1 + 1 - 1 = r - 1 by omega, List.getElem?_eq_getElem hl, Option.getD_some,
    show 0 + (r - 1) + 1 = r by omega, Nat.sub_zero]

theorem kvs_sorted_at (σ : KVState) (r : Nat) : (σ.at r).kvs.Pairwise etcdKvLess :=
  KVStore.kvs_sorted _

/-- A key-value's revisions: a create revision from `1` to its mod revision, at most `r`. -/
def CrLe (r : Nat) (s : List EtcdKv) : Prop :=
  ∀ v ∈ s, 1 ≤ uint.nat v.createRev ∧ uint.nat v.createRev ≤ uint.nat v.modRev ∧
    uint.nat v.modRev ≤ r

theorem crLe_applyChange (r : Nat) (h1 : 1 ≤ r) (hr : r < 2 ^ 64) (s : List EtcdKv)
    (hs : CrLe r s) (c : mvcc.Change) : CrLe r (mvcc.applyChange (W64 (r : Int)) s c) := by
  have hR : uint.nat (W64 (r : Int)) = r := by
    simp only [W64, uint.nat, BitVec.toNat_ofInt]; omega
  cases c with
  | put k val l =>
    intro v hv
    rcases txn.mem_putKv hv with hv | ⟨-, hm, hc⟩
    · exact hs v hv
    · rcases hc with ⟨w, hw, -, hcr, -⟩ | ⟨hcr, -⟩
      · have := hs w hw
        rw [hcr, hm, hR]; omega
      · rw [hcr, hm, hR]; omega
  | del k =>
    intro v hv
    exact hs v (txn.mem_applyChange_del hv).1

theorem crLe_applyChanges (r : Nat) (h1 : 1 ≤ r) (hr : r < 2 ^ 64) :
    ∀ (cs : List mvcc.Change) (s : List EtcdKv), CrLe r s →
      CrLe r (mvcc.applyChanges (W64 (r : Int)) s cs)
  | [], _, hs => hs
  | c :: cs, s, hs =>
    crLe_applyChanges r h1 hr cs _ (crLe_applyChange r h1 hr s hs c)

theorem crLe_mono {r r' : Nat} (h : r ≤ r') {s : List EtcdKv} (hs : CrLe r s) : CrLe r' s :=
  fun v hv => by have := hs v hv; omega

/-- **Every key-value of the history has a create revision from `1` to its mod revision.** -/
theorem crOk (σ : KVState) (hw : KHistW σ) (hrev : σ.rev < 2 ^ 63) :
    ∀ r ≤ σ.rev, CrLe r (σ.at r).kvs
  | 0, _ => by
    intro v hv
    have := (hw.wf 0 (Nat.zero_le _) v hv).2
    omega
  | r + 1, hr => by
    rw [at_succ_kvs σ hw.comp (r + 1) (by omega) hr]
    apply crLe_applyChanges (r + 1) (by omega) (by omega)
    exact crLe_mono (by omega) (crOk σ hw hrev r (by omega))

theorem evsOfRevM_append (m : Nat) :
    ∀ (xs ys : List mvcc.Change) (b : List EtcdKv), b.Pairwise etcdKvLess →
      mvcc.evsOfRevM m b (xs ++ ys) =
        mvcc.evsOfRevM m b xs ++ mvcc.evsOfRevM m (mvcc.applyChanges (W64 (m : Int)) b xs) ys
  | [], ys, b, _ => by rw [List.nil_append]; rfl
  | c :: xs, ys, b, hb => by
    rw [List.cons_append, v3rpc.evsOfRevM_cons m b hb, v3rpc.evsOfRevM_cons m b hb,
      evsOfRevM_append m xs ys _ (mvcc.applyChange_sorted hb _ c)]
    rfl

theorem evOfKv_key (m : Nat) (kv : EtcdKv) : (mvcc.evOfKv m kv).kv.key = kv.key := by
  unfold mvcc.evOfKv; split <;> rfl

/-- An event of a revision's changes is at one of their keys. -/
theorem evsOfRevM_keys (m : Nat) :
    ∀ (xs : List mvcc.Change) (b : List EtcdKv), b.Pairwise etcdKvLess →
      ∀ ev ∈ mvcc.evsOfRevM m b xs, ev.kv.key ∈ xs.map mvcc.Change.key
  | [], b, _, ev, h => by simp [mvcc.evsOfRevM] at h
  | c :: xs, b, hb, ev, h => by
    rw [v3rpc.evsOfRevM_cons m b hb] at h
    rcases List.mem_cons.1 h with rfl | h
    · rw [evOfKv_key, v3rpc.chKv_key]; simp
    · have := evsOfRevM_keys m xs _ (mvcc.applyChange_sorted hb _ c) ev h
      simp only [List.map_cons, List.mem_cons]; exact Or.inr this

theorem findKey_filter_other (s : List EtcdKv) (k k' : GoString) (hne : k' ≠ k) :
    mvcc.findKey k' (s.filter fun x => !decide (x.key = k)) = mvcc.findKey k' s := by
  unfold mvcc.findKey
  induction s with
  | nil => rfl
  | cons v s ih =>
    rw [List.filter_cons]
    by_cases hv : v.key = k
    · have : v.key ≠ k' := fun e => hne (e ▸ hv)
      simp [hv, ih, Ne.symm hne]
    · simp only [hv, decide_false, Bool.not_false, ↓reduceIte, List.find?_cons]
      split <;> simp_all

theorem findKey_del_self (s : List EtcdKv) (k : GoString) :
    mvcc.findKey k (s.filter fun x => !decide (x.key = k)) = none := by
  cases h : mvcc.findKey k (s.filter fun x => !decide (x.key = k)) with
  | none => rfl
  | some v =>
    have hk := findKey_key h
    have hm := (List.mem_filter.1 (mvcc.findKey_mem h)).2
    simp [hk] at hm

theorem putNv_facts (r : w64) (k v : GoString) (l : w64) (s : List EtcdKv)
    (hs : s.Pairwise etcdKvLess) :
    mvcc.findKey k (mvcc.applyChange r s (.put k v l)) = some (txn.putNv r k v l s) ∧
      (txn.putNv r k v l s).modRev = r ∧
      (txn.putNv r k v l s).createRev = ((mvcc.findKey k s).map EtcdKv.createRev).getD r := by
  have hf := mvcc.findKey_putKv_self_eq hs r k v l
  unfold mvcc.findKey at hf ⊢
  unfold txn.putNv
  cases h : s.find? (fun x => decide (x.key = k)) with
  | none => rw [h] at hf; exact ⟨hf, rfl, rfl⟩
  | some w => rw [h] at hf; exact ⟨hf, rfl, rfl⟩

/-- **etcd's revision `r` under the prefix** (`1 ≤ r ≤ rev`, the history `KHistW`): no change
under the prefix (the stores agree there, no event under it), or one change, at a key `K`: the
stores agree at every other key under the prefix, and the revision's one event under the prefix is
`K`'s delete (`K` absent after) or put (`K`'s key-value after, at `r`, created at `r` if `K` was
absent before, else when it was created). -/
theorem rev_cases (σ : KVState) (hw : KHistW σ) (hrev : σ.rev < 2 ^ 63) (r : Nat) (h1 : 1 ≤ r)
    (hr : r ≤ σ.rev) :
    ((∀ K, kpfxD <+: K → mvcc.findKey K (σ.at r).kvs = mvcc.findKey K (σ.at (r - 1)).kvs) ∧
      ∀ ev ∈ σ.revEvents r, ¬ kpfxD <+: ev.kv.key) ∨
    ∃ (K : GoString) (ev : mvcc.EvM), kpfxD <+: K ∧ ev.kv.key = K ∧
      (∀ K', kpfxD <+: K' → K' ≠ K →
        mvcc.findKey K' (σ.at r).kvs = mvcc.findKey K' (σ.at (r - 1)).kvs) ∧
      (σ.revEvents r).filter (fun ev => decide (kpfxD <+: ev.kv.key)) = [ev] ∧
      ((ev.del = true ∧ ev.kv.modRev = W64 (r : Int) ∧ mvcc.findKey K (σ.at r).kvs = none) ∨
       (ev.del = false ∧ mvcc.findKey K (σ.at r).kvs = some ev.kv ∧ ev.kv.modRev = W64 (r : Int) ∧
         ev.kv.createRev = ((mvcc.findKey K (σ.at (r - 1)).kvs).map EtcdKv.createRev).getD
           (W64 (r : Int)))) := by
  have hA := kvs_sorted_at σ (r - 1)
  have hB := at_succ_kvs σ hw.comp r h1 hr
  have hcr := crOk σ hw hrev (r - 1) (by omega)
  have hev : σ.revEvents r = mvcc.evsOfRevM r (σ.at (r - 1)).kvs (σ.changesAt r) := rfl
  generalize hAe : (σ.at (r - 1)).kvs = A at hA hB hcr hev
  generalize hcs : σ.changesAt r = cs at hB hev
  have hone := hw.one r hr
  rw [hcs] at hone
  rw [hB, hev]
  rcases filter_le_one _ cs hone with hno | ⟨pre, c, post, rfl, hc, hpp⟩
  · left
    refine ⟨fun K hK => client.findKey_applyChanges_other _ K cs A hA ?_, fun ev he hp => ?_⟩
    · intro hm
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hm
      have := hno c hc
      simp [hK] at this
    · obtain ⟨c, hc, he'⟩ := List.mem_map.1 (evsOfRevM_keys r cs A hA ev he)
      have := hno c hc
      rw [he'] at this
      simp [hp] at this
  · right
    simp only [decide_eq_true_eq] at hc
    have hnp : ∀ a ∈ pre ++ post, ¬ kpfxD <+: a.key := fun a ha h => by
      have := hpp a ha; simp [h] at this
    have hA1 := mvcc.applyChanges_sorted (W64 (r : Int)) pre hA
    have hRne : W64 (r : Int) ≠ W64 0 := by
      intro e
      have := congrArg (fun w : w64 => w.toNat) e
      simp only [W64, BitVec.toNat_ofInt] at this; omega
    have hRn : uint.nat (W64 (r : Int)) = r := by
      simp only [W64, uint.nat, BitVec.toNat_ofInt]; omega
    -- the stores
    have hst : mvcc.applyChanges (W64 (r : Int)) A (pre ++ c :: post) =
        mvcc.applyChanges (W64 (r : Int))
          (mvcc.applyChange (W64 (r : Int)) (mvcc.applyChanges (W64 (r : Int)) A pre) c) post := by
      rw [txn.applyChanges_append]; rfl
    have hpost : ∀ K, kpfxD <+: K → K ∉ post.map mvcc.Change.key := fun K hK hm => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hm
      exact hnp a (List.mem_append_right _ ha) hK
    have hpre : ∀ K, kpfxD <+: K → K ∉ pre.map mvcc.Change.key := fun K hK hm => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hm
      exact hnp a (List.mem_append_left _ ha) hK
    have hK1 : ∀ K, kpfxD <+: K →
        mvcc.findKey K (mvcc.applyChanges (W64 (r : Int)) A pre) = mvcc.findKey K A :=
      fun K hK => client.findKey_applyChanges_other _ K pre A hA (hpre K hK)
    have hKB : ∀ K, kpfxD <+: K → mvcc.findKey K (mvcc.applyChanges (W64 (r : Int)) A (pre ++ c :: post)) =
        mvcc.findKey K (mvcc.applyChange (W64 (r : Int)) (mvcc.applyChanges (W64 (r : Int)) A pre) c) :=
      fun K hK => by
        rw [hst]
        exact client.findKey_applyChanges_other _ K post _ (mvcc.applyChange_sorted hA1 _ c) (hpost K hK)
    -- the events
    have hevs : (mvcc.evsOfRevM r A (pre ++ c :: post)).filter (fun ev => decide (kpfxD <+: ev.kv.key)) =
        [mvcc.evOfKv r (v3rpc.chKv (W64 (r : Int)) (mvcc.applyChanges (W64 (r : Int)) A pre) c)] := by
      rw [evsOfRevM_append r pre (c :: post) A hA, v3rpc.evsOfRevM_cons r _ hA1, List.filter_append,
        List.filter_cons]
      have hf1 : (mvcc.evsOfRevM r A pre).filter (fun ev => decide (kpfxD <+: ev.kv.key)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro ev he
        obtain ⟨a, ha, he'⟩ := List.mem_map.1 (evsOfRevM_keys r pre A hA ev he)
        simpa [← he'] using hnp a (List.mem_append_left _ ha)
      have hf2 : (mvcc.evsOfRevM r (mvcc.applyChange (W64 (r : Int))
          (mvcc.applyChanges (W64 (r : Int)) A pre) c) post).filter
            (fun ev => decide (kpfxD <+: ev.kv.key)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro ev he
        obtain ⟨a, ha, he'⟩ := List.mem_map.1
          (evsOfRevM_keys r post _ (mvcc.applyChange_sorted hA1 _ c) ev he)
        simpa [← he'] using hnp a (List.mem_append_right _ ha)
      rw [hf1, hf2, evOfKv_key, v3rpc.chKv_key]
      simp [hc]
    refine ⟨c.key, _, hc, by rw [evOfKv_key, v3rpc.chKv_key], fun K' hK' hne => ?_, hevs, ?_⟩
    · rw [hKB K' hK', ← hK1 K' hK']
      cases c with
      | put k v l => exact mvcc.findKey_putKv_other hA1 _ K' k v l (Ne.symm hne)
      | del k =>
        show mvcc.findKey K' (List.filter _ _) = _
        exact findKey_filter_other _ k K' hne
    · rw [hKB c.key hc]
      cases c with
      | del k =>
        left
        refine ⟨?_, ?_, findKey_del_self _ k⟩ <;> simp [mvcc.evOfKv, v3rpc.chKv, zeroKv]
      | put k v l =>
        right
        have hk : mvcc.Change.key (.put k v l) = k := rfl
        rw [hk] at hc ⊢
        obtain ⟨hf, hm, hc'⟩ := putNv_facts (W64 (r : Int)) k v l _ hA1
        rw [hK1 k hc] at hc'
        have hcrne : (v3rpc.chKv (W64 (r : Int)) (mvcc.applyChanges (W64 (r : Int)) A pre)
            (.put k v l)).createRev ≠ W64 0 := by
          show (txn.putNv (W64 (r : Int)) k v l (mvcc.applyChanges (W64 (r : Int)) A pre)).createRev ≠ _
          rw [hc']
          cases hfa : mvcc.findKey k A with
          | none => exact hRne
          | some w =>
            simp only [Option.map_some, Option.getD_some]
            intro e
            have := (hcr w (mvcc.findKey_mem hfa)).1
            rw [e] at this; simp at this
        have hevk : mvcc.evOfKv r (v3rpc.chKv (W64 (r : Int)) (mvcc.applyChanges (W64 (r : Int)) A pre)
            (.put k v l)) = ⟨false, txn.putNv (W64 (r : Int)) k v l
              (mvcc.applyChanges (W64 (r : Int)) A pre), none⟩ := by
          unfold mvcc.evOfKv; rw [if_neg hcrne]; rfl
        rw [hevk]
        exact ⟨rfl, hf, hm, hc'⟩

/-! ## The driver's stores -/

/-- The item of the name `n` in an item list. -/
def fI (its : List item) (n : GoString) : Option item := its.find? fun it => decide (it.key' = n)

theorem fI_cons (a : item) (its : List item) (n : GoString) :
    fI (a :: its) n = if a.key' = n then some a else fI its n := by
  unfold fI; rw [List.find?_cons]; by_cases h : a.key' = n <;> simp [h]

theorem fI_none_of_lt (its : List item) (k : GoString)
    (h : ∀ it ∈ its, go.GoStringLt k it.key') : fI its k = none := by
  unfold fI
  rw [List.find?_eq_none]
  intro it hit he
  simp only [decide_eq_true_eq] at he
  have := h it hit
  rw [he] at this
  exact go.goStringLt_irrefl _ this

theorem fI_key {its : List item} {n : GoString} {it : item} (h : fI its n = some it) :
    it.key' = n := by
  have := List.find?_some h; simpa using this

theorem sortedI_cons' {a : item} {its : List item} (h : SortedI (a :: its)) :
    SortedI its ∧ ∀ it ∈ its, go.GoStringLt a.key' it.key' := by
  unfold SortedI at h ⊢
  simp only [List.map_cons, List.pairwise_cons, List.mem_map] at h
  exact ⟨h.2, fun it hit => h.1 it.key' ⟨it, hit, rfl⟩⟩

/-- The change of the name `n` between its items `a` (before) and `b` (after). -/
def chgL (n : GoString) (a b : Option item) (r : Nat) : Option Chg :=
  match a, b with
  | none, none => none
  | some p, none => some ⟨n, some p.obj', none, r⟩
  | none, some q => some ⟨n, none, some q.obj', r⟩
  | some p, some q => if p = q then none else some ⟨n, some p.obj', some q.obj', r⟩

/-- **Two sorted stores that agree at every name but `n` change at `n` only** (`changeAtL`). -/
theorem changeAtL_one (n : GoString) (r : Nat) :
    ∀ (p q : List item), SortedI p → SortedI q → (∀ k, k ≠ n → fI p k = fI q k) →
      changeAtL p q r = chgL n (fI p n) (fI q n) r
  | [], [], _, _, _ => rfl
  | a :: ps, [], _, _, h => by
    have ha : a.key' = n := by
      by_cases hne : a.key' = n
      · exact hne
      · have := h a.key' hne
        rw [fI_cons, if_pos rfl] at this
        cases this
    simp only [changeAtL, fI_cons, ha, ↓reduceIte, chgL]
    rfl
  | [], b :: qs, _, _, h => by
    have hb : b.key' = n := by
      by_cases hne : b.key' = n
      · exact hne
      · have := h b.key' hne
        rw [fI_cons, if_pos rfl] at this
        cases this
    simp only [changeAtL, fI_cons, hb, ↓reduceIte, chgL]
    rfl
  | a :: ps, b :: qs, hp, hq, h => by
    obtain ⟨hps, hpa⟩ := sortedI_cons' hp
    obtain ⟨hqs, hqb⟩ := sortedI_cons' hq
    by_cases hab : go.GoStringLt a.key' b.key'
    · have hnq : fI (b :: qs) a.key' = none :=
        fI_none_of_lt _ _ (fun it hit => by
          rcases List.mem_cons.1 hit with rfl | hit
          · exact hab
          · exact go.goStringLt_trans hab (hqb it hit))
      have ha : a.key' = n := by
        by_cases hne : a.key' = n
        · exact hne
        · have := h a.key' hne
          rw [hnq, fI_cons, if_pos rfl] at this
          cases this
      have hnq' := hnq
      rw [ha] at hnq'
      rw [show changeAtL (a :: ps) (b :: qs) r = some ⟨a.key', some a.obj', none, r⟩ by
        simp [changeAtL, hab]]
      rw [fI_cons, if_pos ha, hnq']
      simp [chgL, ha]
    by_cases hba : go.GoStringLt b.key' a.key'
    · have hnp : fI (a :: ps) b.key' = none :=
        fI_none_of_lt _ _ (fun it hit => by
          rcases List.mem_cons.1 hit with rfl | hit
          · exact hba
          · exact go.goStringLt_trans hba (hpa it hit))
      have hb : b.key' = n := by
        by_cases hne : b.key' = n
        · exact hne
        · have := h b.key' hne
          rw [hnp, fI_cons, if_pos rfl] at this
          cases this
      have hnp' := hnp
      rw [hb] at hnp'
      rw [show changeAtL (a :: ps) (b :: qs) r = some ⟨b.key', none, some b.obj', r⟩ by
        simp [changeAtL, hab, hba]]
      rw [hnp', fI_cons, if_pos hb]
      simp [chgL, hb]
    have hk : a.key' = b.key' := go.goStringLt_eq_of_not_lt hab hba
    by_cases he : a = b
    · subst he
      have ih := changeAtL_one n r ps qs hps hqs (fun k hk' => by
        by_cases hka : k = a.key'
        · subst hka
          rw [fI_none_of_lt ps _ hpa, fI_none_of_lt qs _ hqb]
        · have := h k hk'
          rw [fI_cons, fI_cons, if_neg (Ne.symm hka), if_neg (Ne.symm hka)] at this
          exact this)
      simp only [changeAtL, hab, decide_false, Bool.false_eq_true, ↓reduceIte, decide_true]
      rw [ih, fI_cons, fI_cons]
      by_cases hn : a.key' = n
      · subst hn
        rw [fI_none_of_lt ps _ hpa, fI_none_of_lt qs _ hqb]
        simp [chgL]
      · simp only [hn, ↓reduceIte]
    · have hn : a.key' = n := by
        by_cases hne : a.key' = n
        · exact hne
        · have := h a.key' hne
          rw [fI_cons, fI_cons, if_pos rfl, if_pos hk.symm] at this
          exact absurd (Option.some.inj this) he
      rw [show changeAtL (a :: ps) (b :: qs) r = some ⟨a.key', some a.obj', some b.obj', r⟩ by
        simp [changeAtL, hab, hba, he]]
      rw [fI_cons, fI_cons, if_pos hn, if_pos (hk ▸ hn)]
      simp [chgL, he, hn]
termination_by p q => p.length + q.length

/-- The driver's item of a name in a store related to etcd's: the name's key-value, decoded, at its
mod revision. -/
def itemK (s : KVStore) (n : GoString) : Option item :=
  (mvcc.findKey (mkeyL n) s.kvs).bind fun v =>
    (driverCodec.dec v.value).map fun oc => ⟨n, oc.1.toObj v.modRev, oc.2⟩

theorem fI_of_krelS {s : KVStore} {rv : Nat} {g : GSt} (hS : KRelS s rv g) (n : GoString) :
    fI g.items n = itemK s n := by
  have hr := hS.2.2 n
  rw [absK_mkeyL] at hr
  unfold itemK
  have hl : lookupL g.items n = match fI g.items n with
      | some it => (it, true) | none => (zItem, false) := rfl
  rw [hl] at hr
  cases hf : fI g.items n with
  | none =>
    rw [hf] at hr
    cases hk : mvcc.findKey (mkeyL n) s.kvs with
    | none => rfl
    | some v =>
      rw [hk] at hr
      cases hd : driverCodec.dec v.value with
      | none => simp [hd]
      | some oc => simp [hd, PairRelH] at hr
  | some it =>
    rw [hf] at hr
    have hik := fI_key hf
    cases hk : mvcc.findKey (mkeyL n) s.kvs with
    | none => rw [hk] at hr; exact hr.elim
    | some v =>
      rw [hk] at hr
      cases hd : driverCodec.dec v.value with
      | none => simp [hd, PairRelH] at hr
      | some oc =>
        simp only [Option.bind_some, hd, Option.map_some, PairRelH, ItemRelH] at hr
        obtain ⟨ho, hc⟩ := hr
        simp only [Option.bind_some]
        cases it
        simp only at hik ho hc ⊢
        rw [hd, hik, ho, ← hc, W64_uint_nat]; rfl

theorem chgL_self (n : GoString) (a : Option item) (r : Nat) : chgL n a a r = none := by
  cases a <;> simp [chgL]

theorem changeAtL_self (r : Nat) : ∀ p : List item, changeAtL p p r = none
  | [] => rfl
  | a :: ps => by
    simp only [changeAtL, go.goStringLt_irrefl, decide_false, Bool.false_eq_true, ↓reduceIte,
      decide_true]
    exact changeAtL_self r ps

theorem selOkL_toObj (x : Input) (o : DObj) (a : w64) : selOkL x (o.toObj a) = selD x o := rfl

theorem W64_nat_lt (r : Nat) (h : r < 2 ^ 64) : uint.nat (W64 (r : Int)) = r := by
  simp only [W64, uint.nat, BitVec.toNat_ofInt]; omega

theorem sint_nat_W64 (r : Nat) (h : r < 2 ^ 63) : sint.nat (W64 (r : Int)) = r := by
  rw [sint_nat_of_lt _ (by simp only [uint.Z, W64, BitVec.toNat_ofInt]; omega), W64_nat_lt r (by omega)]

theorem histN_eq (hs : List GSt) (r : Nat) (h : r < 2 ^ 64) : histN hs r = histAtL hs (W64 (r : Int)) := by
  unfold histN histAtL; rw [W64_nat_lt r h]

/-- `KRelH`'s history, at a natural revision. -/
theorem krelS_at {h : HSt} {σ : KVState} (hrel : KRelH h σ) (r : Nat) (h1 : 1 ≤ r) (hr : r ≤ σ.rev) :
    KRelS (σ.at r) r (histN h.hist r) := by
  rw [histN_eq _ _ (by have := hrel.1; omega)]
  exact hrel.2.2.1 r h1 hr

/-- The previous record's object (`kEvOfL`'s `prev`), from the key-values. -/
theorem prev_eq (σ : KVState) (ev : mvcc.EvM) :
    (kPrevAt σ ev).bind (fun p => kDecObj driverCodec.dec p.value) =
      (mvcc.findKey ev.kv.key (σ.at (sint.nat ev.kv.modRev - 1)).kvs).bind
        (fun v => kDecObj driverCodec.dec v.value) := by
  unfold kPrevAt
  rw [findKey_kvs]
  cases (σ.at (sint.nat ev.kv.modRev - 1)).lookup ev.kv.key <;> rfl

/-- The watch's scope: under the prefix, at a name's key (`"/objs/"` prefix of the watched key). -/
theorem scope_name (x : Input) (k : GoString) (hk : prepareKeyM go!"/objs" x.WKey' x.Recursive' = some k)
    (hlk : go!"/objs/" <+: x.WKey') (K : GoString)
    (h : kInScope (go!"/registry" ++ k) x.Recursive' K = true) : ∃ n, K = mkeyL n := by
  have hobj := prepareKeyM_objs _ _ _ hk hlk
  have hpre : go!"/registry/objs/" <+: K :=
    (List.prefix_append_right_inj go!"/registry").2 hobj |>.trans (kInScope_registry k K _ h)
  obtain ⟨n, hn⟩ := hpre
  exact ⟨n, by rw [← hn]; rfl⟩

theorem mkeyL_pfx (n : GoString) : kpfxD <+: mkeyL n := ⟨go!"/" ++ n, rfl⟩

theorem mkeyL_inj {n n' : GoString} (h : mkeyL n = mkeyL n') : n = n' := by
  unfold mkeyL storeKeyL at h
  simpa using h

/-- **One revision's watch events are the driver's event there** (`2 ≤ r ≤ rev`): etcd's events of
revision `r` in the watch's scope, through `transform`, as the driver records them, are the change
event the driver's check computes at `r` (`evAtL`). -/
theorem evAtL_eq (x : Input) (h : HSt) (σ : KVState) (k : GoString) (sel : DObj → Bool) (emp : Bool)
    (hrel : KRelH h σ) (hw : KHistW σ)
    (hk : prepareKeyM go!"/objs" x.WKey' x.Recursive' = some k) (hlk : go!"/objs/" <+: x.WKey')
    (hsel : ∀ o, sel o = selD x o) (hemp : emp = true → ∀ o, sel o = true)
    (r : Nat) (h2 : 2 ≤ r) (hr : r ≤ σ.rev) :
    (kEventsInL driverCodec.dec sel emp σ (kInScope (go!"/registry" ++ k) x.Recursive') r (r + 1)).map
      kToWEv = (evAtL x h.hist r).toList := by
  have hrev : σ.rev < 2 ^ 63 := hrel.1
  have hSA := krelS_at hrel (r - 1) (by omega) (by omega)
  have hSB := krelS_at hrel r (by omega) hr
  have hfA := fI_of_krelS hSA
  have hfB := fI_of_krelS hSB
  have hRn := W64_nat_lt r (by omega)
  have hRs := sint_nat_W64 r (by omega)
  have hscope : ∀ n, kInScope (go!"/registry" ++ k) x.Recursive' (mkeyL n) =
      keyInScopeL x.WKey' x.Recursive' (storeKeyL n) := fun n => prepareKeyM_scope _ _ _ hk (storeKeyL n)
  have hev : kEventsInL driverCodec.dec sel emp σ (kInScope (go!"/registry" ++ k) x.Recursive') r (r + 1) =
      (((σ.revEvents r).filter (fun ev => decide (kpfxD <+: ev.kv.key))).filter
        (fun ev => kInScope (go!"/registry" ++ k) x.Recursive' ev.kv.key)).filterMap
        (kEvOfL driverCodec.dec sel emp σ) := by
    unfold kEventsInL kRangeEvsL
    rw [show r + 1 - r = 1 by omega, List.filter_filter]
    simp only [List.range'_one, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil]
    congr 1
    apply List.filter_congr
    intro ev _
    by_cases hs : kInScope (go!"/registry" ++ k) x.Recursive' ev.kv.key = true
    · obtain ⟨n, hn⟩ := scope_name x k hk hlk _ hs
      have hp : decide (kpfxD <+: ev.kv.key) = true := by rw [hn]; simp [mkeyL_pfx]
      simp only [hs, hp, Bool.and_true]
    · simp only [Bool.eq_false_iff.mpr hs, Bool.false_and]
  have hevA : evAtL x h.hist r = (changeAtL (histN h.hist (r - 1)).items (histN h.hist r).items r).bind
      fun ch => if keyInScopeL x.WKey' x.Recursive' (storeKeyL ch.key) then toEventL x ch else none := by
    unfold evAtL; rw [if_pos h2]
  rw [hev, hevA]
  rcases rev_cases σ hw hrev r (by omega) hr with ⟨hsame, hnone⟩ | ⟨K, ev, hKp, hevK, hoth, hfil, hcase⟩
  · -- no change under the prefix
    have hfil : (σ.revEvents r).filter (fun ev => decide (kpfxD <+: ev.kv.key)) = [] := by
      rw [List.filter_eq_nil_iff]; intro ev he; simpa using hnone ev he
    have hall : ∀ n, fI (histN h.hist (r - 1)).items n = fI (histN h.hist r).items n := by
      intro n
      rw [hfA, hfB]; unfold itemK; rw [hsame _ (mkeyL_pfx n)]
    rw [hfil, changeAtL_one [] r _ _ hSA.1 hSB.1 (fun n _ => hall n), hall, chgL_self]
    rfl
  · rw [hfil]
    by_cases hin : kInScope (go!"/registry" ++ k) x.Recursive' K = true
    · obtain ⟨n, rfl⟩ := scope_name x k hk hlk _ hin
      have hagree : ∀ n', n' ≠ n → fI (histN h.hist (r - 1)).items n' = fI (histN h.hist r).items n' := by
        intro n' hne
        rw [hfA, hfB]; unfold itemK
        rw [hoth _ (mkeyL_pfx n') (fun e => hne (mkeyL_inj e))]
      rw [changeAtL_one n r _ _ hSA.1 hSB.1 hagree, hfA, hfB]
      simp only [List.filter_cons, hevK, hin, ↓reduceIte, List.filter_nil, List.filterMap_cons,
        List.filterMap_nil]
      have hdec : ∀ r' ≤ σ.rev, ∀ v ∈ (σ.at r').kvs, v.key = mkeyL n →
          ∃ o cb, driverCodec.dec v.value = some (o, cb) := by
        intro r' hr' v hv hvk
        have := (hw.wf r' hr' v hv).1 (by rw [hvk]; exact mkeyL_pfx n)
        cases hd : driverCodec.dec v.value with
        | none => exact absurd hd this
        | some p => exact ⟨p.1, p.2, rfl⟩
      rcases hcase with ⟨hdel, hmod, hB⟩ | ⟨hdel, hB, hmod, hcr⟩
      · -- a delete
        have hprev := prev_eq σ ev
        rw [hmod, hRs, hevK] at hprev
        have hprev' : (kPrevAt σ ev).bind (fun p => Option.map Prod.fst (driverCodec.dec p.value)) =
            (mvcc.findKey (mkeyL n) (σ.at (r - 1)).kvs).bind
              (fun v => Option.map Prod.fst (driverCodec.dec v.value)) := hprev
        unfold itemK
        rw [hB]
        simp only [kEvOfL, kDecObj, hdel, ↓reduceIte, hprev', hmod, hRs]
        cases hfa : mvcc.findKey (mkeyL n) (σ.at (r - 1)).kvs with
        | none => rfl
        | some w =>
          obtain ⟨o, cb, hd⟩ := hdec (r - 1) (by omega) w (mvcc.findKey_mem hfa) (findKey_key hfa)
          simp only [Option.bind_some, Option.bind_none, hd, Option.map_some, chgL]
          simp only [← hscope n, hin, ↓reduceIte, toEventL, Option.any_none, Option.any_some, selOkL_toObj, ← hsel,
            Bool.false_eq_true]
          cases hs : sel o <;> rfl
      · -- a put
        obtain ⟨o, cb, hd⟩ := hdec r hr ev.kv (mvcc.findKey_mem hB) (findKey_key hB)
        have hprev := prev_eq σ ev
        rw [hmod, hRs, hevK] at hprev
        have hprev' : (kPrevAt σ ev).bind (fun p => Option.map Prod.fst (driverCodec.dec p.value)) =
            (mvcc.findKey (mkeyL n) (σ.at (r - 1)).kvs).bind
              (fun v => Option.map Prod.fst (driverCodec.dec v.value)) := hprev
        unfold itemK
        rw [hB]
        simp only [Option.bind_some, hd, Option.map_some, hmod]
        simp only [kEvOfL, kDecObj, hdel, Bool.false_eq_true, ↓reduceIte, hprev', hd,
          Option.map_some, Option.bind_some, hmod, hRs]
        cases hfa : mvcc.findKey (mkeyL n) (σ.at (r - 1)).kvs with
        | none =>
          rw [hfa] at hcr
          simp only [Option.map_none, Option.getD_none] at hcr
          simp only [hcr, decide_true, ↓reduceIte, Option.bind_none, Option.bind_some, chgL]
          simp only [← hscope n, hin, ↓reduceIte, toEventL, Option.any_none, Option.any_some, selOkL_toObj, ← hsel,
            Bool.and_false, Option.map_some]
          cases hs : sel o <;> rfl
        | some w =>
          rw [hfa] at hcr
          simp only [Option.map_some, Option.getD_some] at hcr
          obtain ⟨o', cb', hd'⟩ := hdec (r - 1) (by omega) w (mvcc.findKey_mem hfa) (findKey_key hfa)
          have hcrw := crOk σ hw hrev (r - 1) (by omega) w (mvcc.findKey_mem hfa)
          have hne : w.createRev ≠ W64 (r : Int) := by
            intro e; rw [e, hRn] at hcrw; omega
          have hne2 : w.modRev ≠ W64 (r : Int) := by
            intro e; rw [e, hRn] at hcrw; omega
          rw [hcr]
          simp only [hne, decide_false, Bool.false_eq_true, ↓reduceIte, Option.bind_some, hd',
            Option.map_some, chgL]
          have hitne : (⟨n, o'.toObj w.modRev, cb'⟩ : item) ≠
              ⟨n, o.toObj (W64 (r : Int)), cb⟩ := by
            intro e
            simp only [item.mk.injEq] at e
            have := congrArg Obj.ResourceVersion' e.2.1
            exact hne2 this
          simp only [hitne, ↓reduceIte, Option.bind_some]
          simp only [← hscope n, hin, ↓reduceIte, toEventL, Option.any_some, selOkL_toObj, ← hsel]
          cases he : emp
          · simp only [Bool.false_eq_true, ↓reduceIte]
            cases hs : sel o <;> cases hs' : sel o' <;> rfl
          · have h1 := hemp he o
            have h2 := hemp he o'
            simp only [↓reduceIte, h1, h2, Bool.and_self, Option.map_some]
            rfl
    · -- the change is out of scope
      simp only [List.filter_cons, hevK, hin, Bool.false_eq_true, ↓reduceIte, List.filter_nil,
        List.filterMap_nil, List.map_nil]
      by_cases hKn : ∃ n, K = mkeyL n
      · obtain ⟨n, rfl⟩ := hKn
        have hagree : ∀ n', n' ≠ n → fI (histN h.hist (r - 1)).items n' = fI (histN h.hist r).items n' := by
          intro n' hne
          rw [hfA, hfB]; unfold itemK
          rw [hoth _ (mkeyL_pfx n') (fun e => hne (mkeyL_inj e))]
        rw [changeAtL_one n r _ _ hSA.1 hSB.1 hagree]
        cases hc : chgL n (fI (histN h.hist (r - 1)).items n) (fI (histN h.hist r).items n) r with
        | none => rfl
        | some ch =>
          have hck : ch.key = n := by
            revert hc
            cases fI (histN h.hist (r - 1)).items n <;> cases fI (histN h.hist r).items n <;>
              simp only [chgL] <;> (try split) <;> intro hc <;> cases hc <;> rfl
          simp only [Option.bind_some, hck, ← hscope, hin, Bool.false_eq_true, ↓reduceIte]
          rfl
      · have hall : ∀ n, fI (histN h.hist (r - 1)).items n = fI (histN h.hist r).items n := by
          intro n
          rw [hfA, hfB]; unfold itemK
          rw [hoth _ (mkeyL_pfx n) (fun e => hKn ⟨n, e.symm⟩)]
        rw [changeAtL_one [] r _ _ hSA.1 hSB.1 (fun n _ => hall n), hall, chgL_self]
        rfl

/-! ## Ranges of revisions -/

theorem kRangeEvsL_split (σ : KVState) (inS : GoString → Bool) (lo m hi : Nat) (h1 : lo ≤ m)
    (h2 : m ≤ hi) : kRangeEvsL σ inS lo hi = kRangeEvsL σ inS lo m ++ kRangeEvsL σ inS m hi := by
  unfold kRangeEvsL
  rw [← List.filter_append, ← List.flatten_append, ← List.map_append]
  congr 3
  have := @List.range'_append_1 lo (m - lo) (hi - m)
  rw [show lo + (m - lo) = m by omega, show m - lo + (hi - m) = hi - lo by omega] at this
  exact this.symm

theorem kEventsInL_split {Obj : Type} (dec : Dec Obj) (sel : Obj → Bool) (emp : Bool) (σ : KVState)
    (inS : GoString → Bool) (lo m hi : Nat) (h1 : lo ≤ m) (h2 : m ≤ hi) :
    kEventsInL dec sel emp σ inS lo hi =
      kEventsInL dec sel emp σ inS lo m ++ kEventsInL dec sel emp σ inS m hi := by
  unfold kEventsInL; rw [kRangeEvsL_split σ inS lo m hi h1 h2, List.filterMap_append]

section bridge
variable (x : Input) (h : HSt) (σ : KVState) (k : GoString) (sel : DObj → Bool) (emp : Bool)

/-- **The watch events of revisions `[lo, hi)` are the driver's** (`2 ≤ lo`, `hi ≤ rev + 1`). -/
theorem kEvents_eq (hrel : KRelH h σ) (hw : KHistW σ)
    (hk : prepareKeyM go!"/objs" x.WKey' x.Recursive' = some k) (hlk : go!"/objs/" <+: x.WKey')
    (hsel : ∀ o, sel o = selD x o) (hemp : emp = true → ∀ o, sel o = true) :
    ∀ d lo, 2 ≤ lo → lo + d ≤ σ.rev + 1 →
      (kEventsInL driverCodec.dec sel emp σ (kInScope (go!"/registry" ++ k) x.Recursive') lo
        (lo + d)).map kToWEv = eventsInL x h.hist lo (lo + d)
  | 0, lo, _, _ => by
    unfold kEventsInL kRangeEvsL eventsInL; simp
  | d + 1, lo, h2, hd => by
    rw [show lo + (d + 1) = lo + d + 1 by omega]
    rw [kEventsInL_split _ _ _ _ _ lo (lo + 1) (lo + d + 1) (by omega) (by omega),
      eventsInL_split x h.hist lo (lo + 1) (lo + d + 1) (by omega) (by omega), List.map_append,
      evAtL_eq x h σ k sel emp hrel hw hk hlk hsel hemp lo h2 (by omega), eventsInL_one,
      show lo + d + 1 = (lo + 1) + d by omega,
      kEvents_eq hrel hw hk hlk hsel hemp d (lo + 1) (by omega) (by omega)]

end bridge

/-! ## Tails -/

section tails
variable {x : Input} {hs : List GSt}

/-- A tail from the next revision, with no event there, is one from the cursor. -/
theorem tailOk_lower {c : Nat} {L : List WEv} (ht : TailOk x hs (c + 1) L)
    (hn : evAtL x hs (c + 1) = none) : TailOk x hs c L := by
  cases ht with
  | nil => exact TailOk.nil c
  | ev _ r e rest hcr hr hgap hev ht =>
    refine TailOk.ev c r e rest (by omega) hr (fun r' h1 h2 => ?_) hev ht
    by_cases e1 : r' = c + 1
    · rw [e1]; exact hn
    · exact hgap r' (by omega) h2
  | bm _ p o rest hcp hp hrv hgap ht =>
    refine TailOk.bm c p o rest (by omega) hp hrv (fun r' h1 h2 => ?_) ht
    by_cases e1 : r' = c + 1
    · rw [e1]; exact hn
    · exact hgap r' (by omega) h2

/-- **The driver's events of the revisions past the cursor, then a tail, are a tail.** -/
theorem tailOk_events (rest : List WEv) :
    ∀ d c, c + d ≤ hs.length → TailOk x hs (c + d) rest →
      TailOk x hs c (eventsInL x hs (c + 1) (c + d + 1) ++ rest)
  | 0, c, _, ht => by
    unfold eventsInL; simpa using ht
  | d + 1, c, hd, ht => by
    have ih := tailOk_events rest d (c + 1) (by omega) (by rw [show c + 1 + d = c + (d + 1) by omega]; exact ht)
    rw [eventsInL_split x hs (c + 1) (c + 2) (c + (d + 1) + 1) (by omega) (by omega), eventsInL_one,
      List.append_assoc, show c + (d + 1) + 1 = c + 1 + d + 1 by omega]
    cases he : evAtL x hs (c + 1) with
    | none => exact tailOk_lower ih he
    | some e =>
      exact TailOk.ev c (c + 1) e _ (by omega) (by omega) (fun r' h1 h2 => by omega) he ih

/-- **A tail's prefix is a tail.** -/
theorem tailOk_prefix {c : Nat} {L : List WEv} (ht : TailOk x hs c L) :
    ∀ L', L' <+: L → TailOk x hs c L' := by
  induction ht with
  | nil c =>
    intro L' hp
    rw [List.prefix_nil.1 hp]; exact TailOk.nil c
  | ev c r e rest hcr hr hgap hev _ ih =>
    intro L' hp
    cases L' with
    | nil => exact TailOk.nil c
    | cons e' L'' =>
      rw [List.cons_prefix_cons] at hp
      obtain ⟨rfl, hp⟩ := hp
      exact TailOk.ev c r e' L'' hcr hr hgap hev (ih L'' hp)
  | bm c p o rest hcp hp hrv hgap _ ih =>
    intro L' hpre
    cases L' with
    | nil => exact TailOk.nil c
    | cons e' L'' =>
      rw [List.cons_prefix_cons] at hpre
      obtain ⟨rfl, hpre⟩ := hpre
      exact TailOk.bm c p o L'' hcp hp hrv hgap (ih L'' hpre)

end tails

theorem kEvOfL_rv_ann {Obj : Type} (dec : Dec Obj) (sel : Obj → Bool) (emp : Bool) (σ : KVState)
    (ev : mvcc.EvM) (e : KWEv Obj) (h : kEvOfL dec sel emp σ ev = some e) :
    e.rv = sint.nat ev.kv.modRev ∧ e.ann = false := by
  simp only [kEvOfL] at h
  split at h
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨o, -, h⟩ := h
    split at h
    · cases h; exact ⟨rfl, rfl⟩
    · cases h
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨o, -, h⟩ := h
    split at h
    · split at h
      · cases h; exact ⟨rfl, rfl⟩
      · cases h
    · split at h
      · cases h; exact ⟨rfl, rfl⟩
      · simp only [Option.bind_eq_some_iff] at h
        obtain ⟨o', -, h⟩ := h
        split at h
        · cases h; exact ⟨rfl, rfl⟩
        · split at h
          · cases h; exact ⟨rfl, rfl⟩
          · split at h
            · cases h; exact ⟨rfl, rfl⟩
            · cases h

/-- A tail's events carry no annotation. -/
theorem kTail_ann {Obj : Type} {dec : Dec Obj} {sel : Obj → Bool} {emp : Bool} {z : Obj}
    {σ : KVState} {inS : GoString → Bool} {c : Nat} {full : List (KWEv Obj)}
    (ht : KTail dec sel emp z σ inS c full) : ∀ e ∈ full, e.ann = false := by
  induction ht with
  | nil => intro e he; cases he
  | chg c r rest _ _ _ ih =>
    intro e he
    rcases List.mem_append.1 he with he | he
    · obtain ⟨ev, -, hev⟩ := List.mem_filterMap.1 he
      exact (kEvOfL_rv_ann dec sel emp σ ev e hev).2
    · exact ih e he
  | bm c p rest _ _ _ _ ih =>
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · rfl
    · exact ih e he

section bridge2
variable (x : Input) (h : HSt) (σ : KVState) (k : GoString) (sel : DObj → Bool) (emp : Bool)
  (z : DObj)

/-- **A store tail from a positive cursor is a driver tail**, without annotations. -/
theorem tailOk_of_kTail (hrel : KRelH h σ) (hlen : h.hist.length = σ.rev) (hw : KHistW σ)
    (hk : prepareKeyM go!"/objs" x.WKey' x.Recursive' = some k) (hlk : go!"/objs/" <+: x.WKey')
    (hsel : ∀ o, sel o = selD x o) (hemp : emp = true → ∀ o, sel o = true)
    {c : Nat} {full : List (KWEv DObj)}
    (ht : KTail driverCodec.dec sel emp z σ (kInScope (go!"/registry" ++ k) x.Recursive') c full)
    (hc : 1 ≤ c) : TailOk x h.hist c (full.map kToWEv) := by
  induction ht with
  | nil c => exact TailOk.nil c
  | chg c r rest hcr hr _ ih =>
    rw [List.map_append]
    have he := kEvents_eq x h σ k sel emp hrel hw hk hlk hsel hemp (r - c) (c + 1) (by omega) (by omega)
    rw [show c + 1 + (r - c) = r + 1 by omega] at he
    rw [he]
    have := tailOk_events (x := x) (hs := h.hist) (rest.map kToWEv) (r - c) c (by omega)
      (by rw [show c + (r - c) = r by omega]; exact ih (by omega))
    rwa [show c + (r - c) + 1 = r + 1 by omega] at this
  | bm c p rest hcp hp hnone _ ih =>
    refine TailOk.bm c p _ _ hcp (by omega) ?_ (fun r' h1 h2 => ?_) (ih (by omega))
    · show uint.nat (W64 (p : Int)) = p
      exact W64_nat_lt p (by have := hrel.1; omega)
    · have hsplit := kRangeEvsL_split σ (kInScope (go!"/registry" ++ k) x.Recursive') (c + 1) r' (p + 1)
        (by omega) (by omega)
      rw [kRangeEvsL_split σ _ r' (r' + 1) (p + 1) (by omega) (by omega)] at hsplit
      rw [hnone] at hsplit
      have h0 : kRangeEvsL σ (kInScope (go!"/registry" ++ k) x.Recursive') r' (r' + 1) = [] := by
        have := congrArg List.length hsplit
        simp only [List.length_nil, List.length_append] at this
        exact List.eq_nil_of_length_eq_zero (by omega)
      have he := evAtL_eq x h σ k sel emp hrel hw hk hlk hsel hemp r' (by omega) (by omega)
      unfold kEventsInL at he
      rw [h0] at he
      cases hv : evAtL x h.hist r' with
      | none => rfl
      | some e => rw [hv] at he; simp at he

end bridge2

/-! ## The initial events -/

theorem initialEventsL_scopeL (x : Input) (its : List item) :
    initialEventsL x ⟨its, W64 0⟩ = ((scopeL { x with ListKey' := x.WKey' } its).filter
      (fun e => selOkL x e.2)).map (fun e => (⟨0, e.2⟩ : WEv)) := by
  unfold initialEventsL scopeL
  simp only
  induction its with
  | nil => rfl
  | cons it its ih =>
    by_cases h1 : keyInScopeL x.WKey' x.Recursive' (storeKeyL it.key') = true <;>
      by_cases h2 : selOkL x it.obj' = true <;>
      simp_all

theorem initialEventsL_items (x : Input) (st : GSt) :
    initialEventsL x st = initialEventsL x ⟨st.items, W64 0⟩ := rfl

theorem kInitial_drv (x : Input) (sel : DObj → Bool) (hsel : ∀ o, sel o = selD x o) :
    ∀ (L : List EtcdKv),
      (L.filterMap fun v => (kDecObj driverCodec.dec v.value).bind fun o =>
          if sel o then some (⟨0, o, sint.nat v.modRev, false⟩ : KWEv DObj) else none).map kToWEv =
        (((L.filterMap fun v => (driverCodec.dec v.value).map fun d =>
            (v.key, (d.1, sint.nat v.modRev))).map toDrv).filter (fun e => selOkL x e.2)).map
          (fun e => (⟨0, e.2⟩ : WEv))
  | [] => rfl
  | v :: L => by
    have ih := kInitial_drv x sel hsel L
    cases hd : driverCodec.dec v.value with
    | none =>
      have hk : kDecObj driverCodec.dec v.value = none := by simp [kDecObj, hd]
      simp only [List.filterMap_cons, hk, hd, Option.bind_none, Option.map_none]
      exact ih
    | some d =>
      have hk : kDecObj driverCodec.dec v.value = some d.1 := by simp [kDecObj, hd]
      have hs : selOkL x (toDrv (v.key, d.1, sint.nat v.modRev)).2 = sel d.1 := by
        show selOkL x (d.1.toObj _) = _
        rw [selOkL_toObj, hsel]
      simp only [List.filterMap_cons, hk, hd, Option.bind_some, Option.map_some, List.map_cons,
        List.filter_cons, hs]
      cases hsd : sel d.1
      · simp only [Bool.false_eq_true, ↓reduceIte]; exact ih
      · simp only [↓reduceIte, List.map_cons]; rw [ih]; rfl

/-- **The initial events are the driver's** at a revision of the history. -/
theorem initial_eq (x : Input) (h : HSt) (σ : KVState) (k : GoString) (sel : DObj → Bool)
    (hrel : KRelH h σ) (hk : prepareKeyM go!"/objs" x.WKey' x.Recursive' = some k)
    (hlk : go!"/objs/" <+: x.WKey') (hsel : ∀ o, sel o = selD x o) (r : Nat) (h1 : 1 ≤ r)
    (hr : r ≤ σ.rev) :
    (kInitialL driverCodec.dec sel (kInScope (go!"/registry" ++ k) x.Recursive') (σ.at r)).map kToWEv =
      initialEventsL x (histN h.hist r) := by
  have hS := krelS_at hrel r h1 hr
  have hsc := scopeL_eq { x with ListKey' := x.WKey' } k (histN h.hist r) (σ.at r) r hS
    (hrel.2.2.2 r hr) (by simpa using hk) (by simpa using hlk)
  rw [initialEventsL_items, initialEventsL_scopeL, hsc]
  unfold kInitialL storeScope
  exact kInitial_drv x sel hsel _

/-! ## The bridge -/

theorem nonErr_rel : ∀ {evs : List (KWEv DObj)} {ws : List WEv}, List.Forall₂ kWEvRel evs ws →
    nonErr ws = (kNonErr evs).map kToWEv
  | [], [], .nil => rfl
  | e :: evs, w :: ws, .cons ⟨ht, hw⟩ hr => by
    have ih := nonErr_rel hr
    unfold nonErr kNonErr at ih ⊢
    rw [List.filter_cons, List.filter_cons]
    by_cases he : e.t = 4
    · have hw4 : w.t = 4 := ht ▸ he
      simp only [he, hw4, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact ih
    · rw [hw he]
      have h4 : (kToWEv e).t ≠ 4 := he
      simp only [he, h4, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, List.map_cons]
      rw [ih]

theorem rel_t : ∀ {evs : List (KWEv DObj)} {ws : List WEv}, List.Forall₂ kWEvRel evs ws →
    (∀ e ∈ evs, e.t ≤ 4) → ∀ w ∈ ws, w.t ≤ 4
  | [], [], .nil, _ => by simp
  | e :: evs, w :: ws, .cons ⟨ht, _⟩ hr, h => by
    intro w' hw'
    rcases List.mem_cons.1 hw' with rfl | hw'
    · rw [ht]; exact h e (by simp)
    · exact rel_t hr (fun e' he' => h e' (by simp [he'])) w' hw'

/-- A prefix of `I ++ b :: F` is a prefix of `I`, or `I`, `b` and a prefix of `F`. -/
theorem prefix_append_cons {α : Type} {P I F : List α} {b : α} (h : P <+: I ++ b :: F) :
    P <+: I ∨ ∃ F', P = I ++ b :: F' ∧ F' <+: F := by
  by_cases hl : P.length ≤ I.length
  · exact Or.inl (List.prefix_of_prefix_length_le h (List.prefix_append I _) hl)
  · right
    obtain ⟨t, ht⟩ := h
    have hI : I <+: P := List.prefix_of_prefix_length_le (List.prefix_append I _) ⟨t, ht⟩ (by omega)
    obtain ⟨u, rfl⟩ := hI
    rw [List.append_assoc, List.append_cancel_left_eq] at ht
    cases u with
    | nil => simp at hl
    | cons b' F' =>
      simp only [List.cons_append, List.cons.injEq] at ht
      obtain ⟨rfl, ht⟩ := ht
      exact ⟨F', rfl, ⟨t, ht⟩⟩

theorem noAnn_map {full : List (KWEv DObj)} (h : ∀ e ∈ full, e.ann = false) :
    NoAnn (full.map kToWEv) := by
  intro w hw _
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hw
  exact h e he

theorem noAnn_prefix {L L' : List WEv} (h : NoAnn L) (hp : L' <+: L) : NoAnn L' :=
  fun e he => h e (hp.subset he)

/-- **The bridge** (Draft D1; plan §1): what the store's watch delivered while live
(`kStreamOk`, from a start point `kStartOk` ties to a state its read update fired at), at etcd's
history related to the configuration's (`KRelH`, `KHistW`), recorded by the driver (`kWEvRel`), is
what the driver's check accepts (`StreamOkL`, the premise of `watchOkL_of_stream`). -/
theorem streamOkL_of_kStreamOk (x : Input) (h : HSt) (σ σ0 : KVState) (k : GoString) (reqw : w64)
    (m : KWatchMode) (sel : DObj → Bool) (emp : Bool) (z : DObj) (st : Nat)
    (evs : List (KWEv DObj)) (ws : List WEv)
    (hrel : KRelH h σ) (hlen : h.hist.length = σ.rev) (hw : KHistW σ)
    (hk : prepareKeyM go!"/objs" x.WKey' x.Recursive' = some k) (hlk : go!"/objs/" <+: x.WKey')
    (hsel : ∀ o, sel o = selD x o) (hemp : emp = true → ∀ o, sel o = true)
    (hm : kModeOk x (uint.nat reqw) m) (h0 : 1 ≤ σ0.rev) (hstart : kStartOk m σ0 st)
    (hs : kStreamOk driverCodec.dec sel emp z (kInScope (go!"/registry" ++ k) x.Recursive') m σ st
      evs)
    (hws : List.Forall₂ kWEvRel evs ws) :
    StreamOkL x (uint.nat reqw) h.hist ws := by
  obtain ⟨ht4, hstle, full, htail, hpre⟩ := hs
  have hne := nonErr_rel hws
  refine ⟨rel_t hws ht4, ?_⟩
  obtain ⟨hreq, hwl, hnwl⟩ := hm
  have hann := kTail_ann htail
  by_cases hsi : x.SendInit' = W64 2
  · rw [if_pos hsi]
    obtain ⟨hfi, hbm⟩ := hwl hsi
    unfold kStartOk at hstart
    rw [if_pos hfi] at hstart
    obtain ⟨hst0, hreqst⟩ := hstart
    have hst1 : 1 ≤ st := by omega
    have hstr := hstle hfi
    unfold kIdealL at hpre
    rw [if_pos hfi, if_pos hbm] at hpre
    have hT := tailOk_of_kTail x h σ k sel emp z hrel hlen hw hk hlk hsel hemp htail hst1
    have hI := initial_eq x h σ k sel hrel hk hlk hsel st hst1 hstr
    refine ⟨st, by omega, by omega, ?_⟩
    rw [hne]
    rw [List.singleton_append] at hpre
    rcases prefix_append_cons hpre with hp | ⟨F', hF, hpF⟩
    · left
      rw [← hI]; exact hp.map _
    · right
      refine ⟨(kToWEv ⟨3, z, st, true⟩).o, (F'.map kToWEv), ?_, rfl, ?_, ?_, ?_⟩
      · show uint.nat (W64 (st : Int)) = st
        exact W64_nat_lt st (by have := hrel.1; omega)
      · rw [hF, List.map_append, List.map_cons, hI]; rfl
      · exact tailOk_prefix hT _ (hpF.map _)
      · exact noAnn_prefix (noAnn_map hann) (hpF.map _)
  · rw [if_neg hsi]
    have hfi := hnwl hsi
    unfold kStartOk at hstart
    rw [if_neg (by simp [hfi])] at hstart
    unfold kIdealL at hpre
    rw [if_neg (by simp [hfi])] at hpre
    have hst1 : 1 ≤ st := by
      split at hstart <;> omega
    have hT := tailOk_of_kTail x h σ k sel emp z hrel hlen hw hk hlk hsel hemp htail hst1
    refine ⟨st, fun hr => ?_, ?_, ?_⟩
    · rw [if_pos (by omega)] at hstart; omega
    · rw [hne]; exact tailOk_prefix hT _ (hpre.map _)
    · rw [hne]; exact noAnn_prefix (noAnn_map hann) (hpre.map _)

/-! ## The histories' facts, the stream at a longer state, the mode -/

/-- **The configuration's history satisfies `HistWf`** (`watchOkL_of_stream`'s premise). -/
theorem histWf_of_krel (x : Input) (h : HSt) (σ : KVState) (k : GoString) (hrel : KRelH h σ)
    (hlen : h.hist.length = σ.rev) (hw : KHistW σ)
    (hk : prepareKeyM go!"/objs" x.WKey' x.Recursive' = some k) (hlk : go!"/objs/" <+: x.WKey') :
    HistWf x h.hist := by
  have hrev := hrel.1
  refine ⟨by omega, fun r it hr hit => ?_, fun r e he => ?_⟩
  · rcases Nat.eq_zero_or_pos r with rfl | h1
    · simp [histN, zSt] at hit
    have hS := krelS_at hrel r h1 (by omega)
    have hf := fI_of_krelS hS it.key'
    have hfi : fI (histN h.hist r).items it.key' = some it := by
      unfold fI
      have hsort := hS.1
      have := lookupL_mem _ hsort it hit
      unfold lookupL at this
      split at this
      · rename_i it' he
        simp only [Prod.mk.injEq] at this
        have e := this.1
        subst e
        exact he
      · simp at this
    rw [hfi] at hf
    unfold itemK at hf
    cases hfk : mvcc.findKey (mkeyL it.key') (σ.at r).kvs with
    | none => rw [hfk] at hf; cases hf
    | some v =>
      rw [hfk] at hf
      cases hd : driverCodec.dec v.value with
      | none => simp [hd] at hf
      | some oc =>
        simp only [Option.bind_some, hd, Option.map_some, Option.some.injEq] at hf
        have hv := (hw.wf r (by omega) v (mvcc.findKey_mem hfk)).2
        rw [hf]
        exact ⟨hv.1, hv.2, rfl⟩
  · -- an event: at a revision of the history (else no change), carrying it
    by_cases h2 : 2 ≤ r
    · by_cases hr : r ≤ σ.rev
      · have hq := evAtL_eq x h σ k (selD x) false hrel hw hk hlk (fun _ => rfl) (by simp) r h2 hr
        rw [he] at hq
        have hm : e ∈ (kEventsInL driverCodec.dec (selD x) false σ
            (kInScope (go!"/registry" ++ k) x.Recursive') r (r + 1)).map kToWEv := by
          rw [hq]; simp
        obtain ⟨e', he', rfl⟩ := List.mem_map.1 hm
        obtain ⟨ev, hev, hk'⟩ := List.mem_filterMap.1 he'
        obtain ⟨-, r'', h1, h2', hmod⟩ := kRangeEvsL_mem hev
        obtain ⟨hrv, hann⟩ := kEvOfL_rv_ann _ _ _ _ _ _ hk'
        have hr'' : r'' = r := by omega
        subst hr''
        rw [hmod, sint_nat_W64 r'' (by omega)] at hrv
        refine ⟨?_, ?_⟩
        · show uint.nat (W64 (e'.rv : Int)) = r''
          rw [hrv]; exact W64_nat_lt r'' (by omega)
        · exact hann
      · exfalso
        have hsame : histN h.hist r = histN h.hist (r - 1) := by
          unfold histN
          rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
        unfold evAtL at he
        rw [if_pos h2, hsame, changeAtL_self] at he
        cases he
    · unfold evAtL at he; rw [if_neg h2] at he; cases he

/-- **The stream at a longer state of the history** (where the read update fired, to the
configuration's state at the linearization point). -/
theorem kStreamRel_hist {Obj : Type} {R : List (KWEv Obj) → List (KWEv Obj) → Prop} {dec : Dec Obj}
    {sel : Obj → Bool} {emp : Bool} {z : Obj} {inS : GoString → Bool} {m : KWatchMode}
    {σ σ' : KVState} {st : Nat} {evs : List (KWEv Obj)} (hh : kvSameHist σ σ') (hle : σ.rev ≤ σ'.rev)
    (hs : kStreamRel R dec sel emp z inS m σ st evs) : kStreamRel R dec sel emp z inS m σ' st evs := by
  obtain ⟨ht, hst, full, htail, hr⟩ := hs
  have hT : ∀ c full, KTail dec sel emp z σ inS c full → KTail dec sel emp z σ' inS c full := by
    intro c full ht
    induction ht with
    | nil c => exact KTail.nil c
    | chg c r rest hcr hr _ ih =>
      have he : kEventsInL dec sel emp σ inS (c + 1) (r + 1) = kEventsInL dec sel emp σ' inS (c + 1) (r + 1) := by
        unfold kEventsInL
        have := kRawToEv_filterMap_hist dec sel emp z σ σ' hh hle _
          (kRawEvs_revOk (σ := σ) (inS := inS) (lo := c + 1) (hi := r + 1) (by omega))
        rw [List.filterMap_map, List.filterMap_map] at this
        rw [← kRangeEvsL_hist σ σ' inS _ _ hh (by omega) (by omega)]
        exact this
      rw [he]
      exact KTail.chg c r rest hcr (by omega) ih
    | bm c p rest hcp hp hnone _ ih =>
      refine KTail.bm c p rest hcp (by omega) ?_ ih
      rw [← kRangeEvsL_hist σ σ' inS _ _ hh (by omega) (by omega)]; exact hnone
  refine ⟨ht, fun h => by have := hst h; omega, full, hT st full htail, ?_⟩
  have hI : kIdealL dec sel inS z m σ st full = kIdealL dec sel inS z m σ' st full := by
    unfold kIdealL
    split
    · rename_i hf
      rw [kvSameHist_at σ σ' st hh (hst hf) (by have := hst hf; omega)]
    · rfl
  rw [← hI]; exact hr

theorem kStreamOk_hist {Obj : Type} {dec : Dec Obj} {sel : Obj → Bool} {emp : Bool} {z : Obj}
    {inS : GoString → Bool} {m : KWatchMode} {σ σ' : KVState} {st : Nat} {evs : List (KWEv Obj)}
    (hh : kvSameHist σ σ') (hle : σ.rev ≤ σ'.rev) (hs : kStreamOk dec sel emp z inS m σ st evs) :
    kStreamOk dec sel emp z inS m σ' st evs :=
  kStreamRel_hist hh hle hs

/-- **The driver's watch options give its mode** (`genWatchFrom`: a watch-list asks for bookmarks;
any other watch with RV 0 sets `SendInitialEvents = false`). -/
theorem kModeOk_of (x : Input) (reqw : w64) (hb : x.SendInit' = W64 2 → x.Bookmarks' = true)
    (h1 : x.SendInit' ≠ W64 2 → x.SendInit' = W64 1 ∨ 0 < uint.nat reqw) :
    kModeOk x (uint.nat reqw) (kModeOf (sieOfL x) x.Bookmarks' reqw) := by
  refine ⟨rfl, fun hs => ?_, fun hs => ?_⟩
  · simp [kModeOf, sieOfL, hs, hb hs]
  · unfold kModeOf sieOfL
    simp only [decide_eq_false_iff_not]
    rw [if_neg hs]
    rintro (⟨h3, h4⟩ | h3)
    · split at h3
      · cases h3
      · rename_i hn1
        rcases h1 hs with h | h
        · exact hn1 h
        · omega
    · split at h3 <;> cases h3

end go

end k8s_etcd3
end EtcdGrove
end Perennial
