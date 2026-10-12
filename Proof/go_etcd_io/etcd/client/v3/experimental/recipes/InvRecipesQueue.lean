/-
`client/v3/experimental/recipes`' queues (`queue.go`, `priority_queue.go`): the vocabulary of their
specs and the lemmas their proofs share. Lean-first (no Rocq counterpart); see `decisions.md`,
"Recipes: the client contracts reused, the queue's claim, two prefixes as one", and "Units 1b, 2
and 3".

**The queues** (`isQueue q client kp`, `isPriorityQueue q client key`, persistent): their fields,
read-only, and the client's contracts: the queue's at its prefix `kp`; the priority queue's at the
empty prefix (its items are under `key ++ "/"`, and `newSequentialKV` also writes the bookkeeping
key `"__" ++ key ++ "/" ++ ...`: two disjoint prefixes, so the contracts are taken at `""`).

**A dequeued item** (`dequeuedAt pfx kp it r`): the key-value `it`, under the queue's prefix
`kp`, was in etcd's state at `r - 1` and was claimed at `r` (`deleteRevKey`'s `revKeyDeleted`),
with the token of the revision `r` (exclusive: `etcdRevToken`). So an item is dequeued at most
once (`dequeuedAt_once`: two claims of one `(key, mod revision)` would share a revision).

**The order** (`dequeueOrder pfx kp le it r`): at the revision `r0 < r` of `Dequeue`'s last get,
either the item was there and first among the items under `kp` for `le` (mod revision for the
queue, `modRevLe`; key for the priority queue, `keyLe`): **the get path**; or every item under
`kp` then was gone at some revision in `[r0, r]` and the item was put at or after `r0`: **the
wait path** (`WaitPrefixEvents` from `r0`; the watch's contract says its events are real, not that
none is skipped, so nothing is said of the items put between `r0` and the event).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.InvRecipesClaim
public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.InvRecipesLemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3
open concurrency

/-! ## The gets (pure) -/

/-- `OpGet(kp, WithFirstRev()...)`: the queue's get, the item under `kp` with the least mod
revision. -/
abbrev firstRevOp (kp : GoString) : OpFull := opGetModel kp (withTopM (W64 3) (W64 1))

/-- `OpGet(kp, WithFirstKey()...)`: the priority queue's get, the item under `kp` with the least
key. -/
abbrev firstKeyOp (kp : GoString) : OpFull := opGetModel kp (withTopM (W64 0) (W64 1))

/-- The queue's order: by mod revision. -/
def modRevLe (a b : EtcdKv) : Prop := sint.Z a.modRev ≤ sint.Z b.modRev

/-- The priority queue's order: by key. -/
def keyLe (a b : EtcdKv) : Prop := go.GoStringLe a.key b.key

theorem firstRevOp_fields (kp : GoString) (hp : kp ≠ []) :
    (firstRevOp kp).t = W64 1 ∧ (firstRevOp kp).key = kp ∧
    (firstRevOp kp).base.rangeEnd = prefixRangeEnd kp ∧ (firstRevOp kp).base.rev = W64 0 ∧
    (firstRevOp kp).base.serializable = false ∧
    (firstRevOp kp).effSortOrder = W64 1 ∧ (firstRevOp kp).sortTarget = W64 3 ∧
    (firstRevOp kp).base.limit = W64 1 ∧ (firstRevOp kp).base.countOnly = false ∧
    (firstRevOp kp).keysOnly = false ∧ (firstRevOp kp).base.minModRev = W64 0 ∧
    (firstRevOp kp).base.maxModRev = W64 0 ∧ (firstRevOp kp).base.minCreateRev = W64 0 ∧
    (firstRevOp kp).base.maxCreateRev = W64 0 := by
  simp [firstRevOp, opGetModel, opFold, withTopM, withPrefixM, withSortM, withLimitM,
    OpFull.getInit, OpFull.newOp, OpModel.zero, hp, OpFull.effSortOrder]

theorem firstKeyOp_fields (kp : GoString) (hp : kp ≠ []) :
    (firstKeyOp kp).t = W64 1 ∧ (firstKeyOp kp).key = kp ∧
    (firstKeyOp kp).base.rangeEnd = prefixRangeEnd kp ∧ (firstKeyOp kp).base.rev = W64 0 ∧
    (firstKeyOp kp).base.serializable = false ∧
    (firstKeyOp kp).effSortOrder = W64 0 ∧
    (firstKeyOp kp).base.limit = W64 1 ∧ (firstKeyOp kp).base.countOnly = false ∧
    (firstKeyOp kp).keysOnly = false ∧ (firstKeyOp kp).base.minModRev = W64 0 ∧
    (firstKeyOp kp).base.maxModRev = W64 0 ∧ (firstKeyOp kp).base.minCreateRev = W64 0 ∧
    (firstKeyOp kp).base.maxCreateRev = W64 0 := by
  simp [firstKeyOp, opGetModel, opFold, withTopM, withPrefixM, withSortM, withLimitM,
    OpFull.getInit, OpFull.newOp, OpModel.zero, hp, OpFull.effSortOrder]

theorem firstRevOp_not_panics : ¬ opGetPanics (withTopM (W64 3) (W64 1)) := by
  simp [opGetModel, opFold, withTopM, withPrefixM, withSortM, withLimitM, OpFull.getInit,
    OpFull.newOp, OpModel.zero, opGetPanics]

theorem firstKeyOp_not_panics : ¬ opGetPanics (withTopM (W64 0) (W64 1)) := by
  simp [opGetModel, opFold, withTopM, withPrefixM, withSortM, withLimitM, OpFull.getInit,
    OpFull.newOp, OpModel.zero, opGetPanics]

/-- A prefix get with no revision filter selects the keys with the prefix. -/
theorem prefixGet_sel_mem (kp : GoString) (o : OpFull) (s : List EtcdKv) (hp : kp ≠ [])
    (hk : o.key = kp) (he : o.base.rangeEnd = prefixRangeEnd kp)
    (h1 : o.base.minModRev = W64 0) (h2 : o.base.maxModRev = W64 0)
    (h3 : o.base.minCreateRev = W64 0) (h4 : o.base.maxCreateRev = W64 0) (v : EtcdKv) :
    v ∈ rangeSel s o ↔ v ∈ s ∧ kp <+: v.key := by
  unfold rangeSel rangeIn
  rw [List.mem_filter, List.mem_filter, hk, he, inRange_prefix kp v.key hp,
    kvFilterOk_zero o v h1 h2 h3 h4]
  simp

/-- The first of a sorted reordering `l` of `sel`, as a get with limit `1` returns it
(`l.take 1`): none only if `sel` is empty, otherwise one of `sel`, first for `le`; and if `sel`
has at most one item, every item of `sel` is returned. -/
theorem take1_first (l sel : List EtcdKv) (le : EtcdKv → EtcdKv → Prop)
    (hperm : l.Perm sel) (hs : l.Pairwise le) (hrefl : ∀ x, le x x) :
    (l.take 1).length ≤ 1 ∧ (l.take 1 = [] → sel = []) ∧
    (∀ w, l.take 1 = [w] → w ∈ sel ∧ ∀ v ∈ sel, le w v) ∧
    (sel.length ≤ 1 → ∀ v ∈ sel, v ∈ l.take 1) := by
  cases l with
  | nil =>
    have := hperm.symm.eq_nil
    subst this
    simp
  | cons x l' =>
    refine ⟨by simp, by simp, ?_, ?_⟩
    · intro w hw
      simp only [List.take_succ_cons, List.take_zero, List.cons.injEq, and_true] at hw
      subst hw
      refine ⟨hperm.subset (by simp), ?_⟩
      intro v hv
      rcases List.mem_cons.1 (hperm.symm.subset hv) with rfl | hv'
      · exact hrefl _
      · exact (List.pairwise_cons.1 hs).1 v hv'
    · intro hl v hv
      have hlen := hperm.length_eq
      have : l' = [] := by
        rw [List.length_cons] at hlen
        exact List.length_eq_zero_iff.1 (by omega)
      subst this
      simpa using hperm.symm.subset hv

/-- **The queue's get** (`WithFirstRev`, limit `1`) on its selection `sel`: at most one item; none
only if `sel` is empty; the one it returns is in `sel`, with the least mod revision; and if `sel`
has at most one item (`More` is false), every item of `sel` is returned. -/
theorem firstRevOp_kvs (kp : GoString) (hp : kp ≠ []) (sel kvs : List EtcdKv)
    (h : rangeKvsOk (firstRevOp kp) sel kvs) :
    kvs.length ≤ 1 ∧ (kvs = [] → sel = []) ∧ (∀ w, kvs = [w] → w ∈ sel ∧ ∀ v ∈ sel, modRevLe w v) ∧
    (sel.length ≤ 1 → ∀ v ∈ sel, v ∈ kvs) := by
  obtain ⟨-, -, -, -, -, hso, hst, hl, hc, hko, -⟩ := firstRevOp_fields kp hp
  obtain ⟨l, hperm, -, hsorted, -, rfl⟩ := h
  have hsorted := hsorted hso
  rw [hst] at hsorted
  have hs' : l.Pairwise modRevLe := hsorted.imp (fun h => by simpa [kvLeBy, modRevLe] using h)
  simp only [hc, hl, hko, Bool.false_eq_true, ↓reduceIte, List.map_id']
  have := take1_first l sel modRevLe hperm hs' (fun x => Int.le_refl _)
  simpa using this

/-- **The priority queue's get** (`WithFirstKey`, limit `1`) on its selection `sel` (in key order):
as `firstRevOp_kvs`, the one it returns having the least key. -/
theorem firstKeyOp_kvs (kp : GoString) (hp : kp ≠ []) (sel kvs : List EtcdKv)
    (hsel : (sel.map EtcdKv.key).Pairwise go.GoStringLt)
    (h : rangeKvsOk (firstKeyOp kp) sel kvs) :
    kvs.length ≤ 1 ∧ (kvs = [] → sel = []) ∧ (∀ w, kvs = [w] → w ∈ sel ∧ ∀ v ∈ sel, keyLe w v) ∧
    (sel.length ≤ 1 → ∀ v ∈ sel, v ∈ kvs) := by
  obtain ⟨-, -, -, -, -, hso, hl, hc, hko, -⟩ := firstKeyOp_fields kp hp
  obtain ⟨l, hperm, hl0, -, -, rfl⟩ := h
  have hl0 := hl0 hso
  subst hl0
  have hs' : l.Pairwise keyLe :=
    ((List.pairwise_map (f := EtcdKv.key) (R := go.GoStringLt)).1 hsel).imp
      (fun h => Or.inr h)
  simp only [hc, hl, hko, Bool.false_eq_true, ↓reduceIte, List.map_id']
  have := take1_first l l keyLe (List.Perm.refl l) hs' (fun x => Or.inl rfl)
  simpa using this

/-- etcd's `More` for a get with limit `1`, not count-only: more than one item selected. -/
theorem more_limit1 (o : OpFull) (sel : List EtcdKv) (more : Bool) (hl : o.base.limit = W64 1)
    (hc : o.base.countOnly = false)
    (h : more = (!o.base.countOnly && decide (0 < sint.Z o.base.limit) &&
      decide (sint.Z o.base.limit < (sel.length : Int)))) (hm : more = false) :
    sel.length ≤ 1 := by
  rw [hl, hc] at h
  rw [hm] at h
  have h1 : sint.Z (W64 1) = 1 := by decide
  simp only [h1, Bool.not_false, Bool.true_and, decide_eq_true_eq] at h
  have := (Bool.and_eq_false_iff.1 h.symm)
  rcases this with h' | h'
  · simp at h'
  · simp only [decide_eq_false_iff_not] at h'; omega

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

/-! ## The queues -/

/-- **A `*Queue`** `q` on the prefix `kp` (non-empty; persistent): its fields, read-only (the
client, `context.TODO()`, the prefix), and the client's contracts at `kp`. -/
def isQueue (q client : Loc) (kp : GoString) : IProp GF :=
  iprop(structFieldRef Queue go!"client" q ↦□ client ∗
    structFieldRef Queue go!"ctx" q ↦□ GoInterface.ok todoCtxVal ∗
    structFieldRef Queue go!"keyPrefix" q ↦□ kp ∗ ⌜kp ≠ []⌝ ∗ isEtcdRecipesClient client kp)

instance isQueue_persistent (q client : Loc) (kp : GoString) :
    Persistent (isQueue (GF := GF) q client kp) := by
  unfold isQueue; infer_instance

/-- **A `*PriorityQueue`** `q` on the key `key` (persistent): its fields, read-only (the client,
`context.TODO()`, the prefix `key ++ "/"`), and the client's contracts at the empty prefix (see
the module docstring). -/
def isPriorityQueue (q client : Loc) (key : GoString) : IProp GF :=
  iprop(structFieldRef PriorityQueue go!"client" q ↦□ client ∗
    structFieldRef PriorityQueue go!"ctx" q ↦□ GoInterface.ok todoCtxVal ∗
    structFieldRef PriorityQueue go!"key" q ↦□ (key ++ go!"/") ∗ isEtcdRecipesClient client [])

instance isPriorityQueue_persistent (q client : Loc) (key : GoString) :
    Persistent (isPriorityQueue (GF := GF) q client key) := by
  unfold isPriorityQueue; infer_instance

/-- **The item `it` was dequeued at `r`** from the queue on `kp` (contracts at `pfx`): `it` is
under `kp`, in etcd's state at `r - 1` (its key, value, revisions: what was enqueued), claimed at
`r` (`revKeyDeleted`: absent at `r`), and the revision `r` is the claim's own (`etcdRevToken`,
exclusive). -/
def dequeuedAt (pfx kp : GoString) (it : EtcdKv) (r : w64) : IProp GF :=
  iprop(revKeyDeleted pfx it.key it.modRev r ∗ etcdRevToken r ∗
    (∃ s : List EtcdKv, □ etcdState (r - W64 1) pfx s ∗ ⌜it ∈ s⌝) ∗ ⌜kp <+: it.key⌝)

/-- **The order of a dequeue** of `it` at `r` from the queue on `kp` (contracts at `pfx`; `le`:
the queue's order) (persistent): at the revision `r0 < r` of the last get, etcd's state `s0`
had `it`, first under `kp` for `le` (the get path); or every item under `kp` in `s0` was gone
(`revKeyGone`) at some revision in `[r0, r]` etcd has reached, and `it` was put at or after `r0`
(the wait path). -/
def dequeueOrder (pfx kp : GoString) (le : EtcdKv → EtcdKv → Prop) (it : EtcdKv) (r : w64) :
    IProp GF :=
  iprop(∃ (r0 : w64) (s0 : List EtcdKv), □ etcdState r0 pfx s0 ∗ ⌜sint.Z r0 < sint.Z r⌝ ∗
    (⌜it ∈ s0 ∧ ∀ w ∈ s0, kp <+: w.key → le it w⌝ ∨
     (⌜sint.Z r0 ≤ sint.Z it.modRev⌝ ∗ □ ∀ w : EtcdKv, ⌜w ∈ s0 ∧ kp <+: w.key⌝ -∗
        ∃ r' : w64, etcdReached r' ∗ revKeyGone pfx w.key w.modRev r' ∗
          ⌜sint.Z r0 ≤ sint.Z r' ∧ sint.Z r' ≤ sint.Z r⌝)))

instance dequeueOrder_persistent (pfx kp : GoString) (le : EtcdKv → EtcdKv → Prop) (it : EtcdKv)
    (r : w64) : Persistent (dequeueOrder (GF := GF) pfx kp le it r) := by
  unfold dequeueOrder; infer_instance

end defs

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

open Iris.ProofMode

/-- A get response has one header revision. -/
theorem getRespRev_agree (resp : Loc) (r1 r2 : w64) :
    getRespRev (GF := GF) resp r1 ∗ getRespRev resp r2 ⊢ ⌜r1 = r2⌝ := by
  unfold getRespRev
  iintro ⟨⟨%h1, #H1, -, #R1⟩, ⟨%h2, #H2, -, #R2⟩⟩
  icombine H1 H2 gives %Hh
  subst Hh
  icombine R1 R2 gives %Hr
  ipureintro; exact Hr

/-- **A claimed item**: a claim (`revKeyDeleted`, with its token) of the key and mod revision of
a key-value `it` seen in some state of etcd is a dequeue of `it` (the record at a mod revision is
determined: `etcdState_modrev_det`). -/
theorem dequeuedAt_intro (pfx kp : GoString) (it : EtcdKv) (a r : w64) (s : List EtcdKv)
    (hit : it ∈ s) (hk : kp <+: it.key) :
    □ etcdState (GF := GF) a pfx s ∗ revKeyDeleted pfx it.key it.modRev r ∗ etcdRevToken r ⊢
      dequeuedAt pfx kp it r := by
  iintro ⟨#Hs, #Hd, Ht⟩
  unfold dequeuedAt
  iframe Hd Ht
  ihave #Hd' := Hd
  iunfold revKeyDeleted at Hd'
  icases Hd' with ⟨%s1, %s1', #Hs1, -, %Hp⟩
  obtain ⟨-, ⟨v, hv, hvk, hvm⟩, -⟩ := Hp
  ihave %Hdet := etcdState_modrev_det a (r - W64 1) pfx s s1 $$ [$Hs $Hs1]
  have heq : it = v := Hdet it hit v hv hvk.symm hvm.symm
  subst heq
  isplitl
  · iexists s1
    iframe Hs1
    ipureintro; exact hv
  ipureintro; exact hk

/-- A dequeued item was in etcd's state at `r - 1`, so `r - 1` is at least its mod revision. -/
theorem dequeuedAt_modRev_lt (pfx kp : GoString) (it : EtcdKv) (r : w64) :
    dequeuedAt (GF := GF) pfx kp it r ⊢ ⌜sint.Z it.modRev < sint.Z r⌝ := by
  unfold dequeuedAt
  iintro ⟨#Hd, -, ⟨%s, #Hs, %Hit⟩, -⟩
  iunfold revKeyDeleted at Hd
  icases Hd with ⟨%s0, %s0', -, -, %Hp⟩
  ihave %Hrv := etcdState_revs (r - W64 1) pfx s $$ Hs
  ipureintro
  have := (Hrv it Hit).2.2.1
  have hr := Hp.1
  have e : sint.Z (r - W64 1) = sint.Z r - 1 := by word
  omega

/-- A claimed item was in etcd's state at `a`, and is not at `r` (`revKeyDeleted`): `a ≠ r`. -/
theorem dequeuedAt_ne (pfx kp : GoString) (it : EtcdKv) (a r : w64) (s : List EtcdKv)
    (hit : it ∈ s) :
    □ etcdState (GF := GF) a pfx s ∗ dequeuedAt pfx kp it r ⊢ ⌜a ≠ r⌝ := by
  unfold dequeuedAt
  iintro ⟨#Hs, #Hd, -, -, -⟩
  iunfold revKeyDeleted at Hd
  icases Hd with ⟨%s1, %s', -, #Hs', %Hp⟩
  iintro %hra
  subst hra
  ihave %Heq := etcdState_agree a pfx s s' $$ [$Hs $Hs']
  subst Heq
  ipureintro
  exact Hp.2.2 it hit rfl

/-- **Dequeued at most once**: two dequeues (each with its claim's token) of items with the same
key and mod revision are impossible (`revKeyDeleted_once`). -/
theorem dequeuedAt_once (pfx kp : GoString) (it1 it2 : EtcdKv) (r1 r2 : w64)
    (hk : it1.key = it2.key) (hm : it1.modRev = it2.modRev) :
    dequeuedAt (GF := GF) pfx kp it1 r1 ∗ dequeuedAt pfx kp it2 r2 ⊢ False := by
  unfold dequeuedAt
  rw [← hk, ← hm]
  iintro ⟨⟨#H1, T1, -, -⟩, ⟨#H2, T2, -, -⟩⟩
  iapply revKeyDeleted_once pfx it1.key it1.modRev r1 r2
  isplitl [T1]
  · iframe T1 H1
  · iframe T2 H2

/-- **The get's items were all claimed by others** (`claimFirstKey` returned no item, having found
each of the get's items `vs` gone, `claimedBefore`, at revisions at least `R`): if the get listed
every item under `kp` in `s` (`More` false), each was gone at some revision in `[R, rd]`, for a
revision `rd ≥ R` etcd has reached (the last of them). -/
theorem drained_intro (pfx kp : GoString) (R : w64) (vs s : List EtcdKv)
    (hlen : vs.length ≤ 1) (hsub : ∀ w ∈ s, kp <+: w.key → w ∈ vs) :
    etcdReached (GF := GF) R ∗ claimedBefore pfx R vs vs.length ⊢
      ∃ rd : w64, etcdReached rd ∗ ⌜sint.Z R ≤ sint.Z rd⌝ ∗
        □ ∀ w : EtcdKv, ⌜w ∈ s ∧ kp <+: w.key⌝ -∗
          ∃ r' : w64, etcdReached r' ∗ revKeyGone pfx w.key w.modRev r' ∗
            ⌜sint.Z R ≤ sint.Z r' ∧ sint.Z r' ≤ sint.Z rd⌝ := by
  iintro ⟨#HR, #Hcb⟩
  match vs, hlen, hsub with
  | [], _, hsub =>
    iexists R
    iframe HR
    isplitr
    · ipureintro; exact Int.le_refl _
    imodintro
    iintro %w %Hw
    exact absurd (hsub w Hw.1 Hw.2) (by simp)
  | [v], _, hsub =>
    unfold claimedBefore
    icases Hcb with ⟨-, #Hcb⟩
    ihave ⟨%r', #Hr', #Hg, %Hr'R⟩ := Hcb $$ %0 %v [] 
    · ipureintro; exact ⟨by simp, rfl⟩
    iexists r'
    iframe Hr'
    isplitr
    · ipureintro; exact Hr'R
    imodintro
    iintro %w %Hw
    have hwv : w = v := by simpa using hsub w Hw.1 Hw.2
    subst hwv
    iexists r'
    iframe Hr' Hg
    ipureintro; exact ⟨Hr'R, Int.le_refl _⟩

/-- The order of a dequeue on **the get path**: `it` was in the get's state `s0` at `r0 < r`,
first under `kp` for `le`. -/
theorem dequeueOrder_get (pfx kp : GoString) (le : EtcdKv → EtcdKv → Prop) (it : EtcdKv)
    (r0 r : w64) (s0 : List EtcdKv) (hit : it ∈ s0) (hmin : ∀ w ∈ s0, kp <+: w.key → le it w)
    (hlt : sint.Z r0 < sint.Z r) :
    □ etcdState (GF := GF) r0 pfx s0 ⊢ dequeueOrder pfx kp le it r := by
  iintro #Hs
  unfold dequeueOrder
  iexists r0, s0
  iframe Hs
  isplitr
  · ipureintro; exact hlt
  ileft
  ipureintro; exact ⟨hit, hmin⟩

/-- The order of a dequeue on **the wait path**: the items under `kp` in the get's state `s0` at
`r0 < r` were all gone by `rd ≤ r`, and `it` was put at or after `r0`. -/
theorem dequeueOrder_wait (pfx kp : GoString) (le : EtcdKv → EtcdKv → Prop) (it : EtcdKv)
    (r0 rd r : w64) (s0 : List EtcdKv) (hput : sint.Z r0 ≤ sint.Z it.modRev)
    (hrd : sint.Z rd ≤ sint.Z r) (hlt : sint.Z r0 < sint.Z r) :
    □ etcdState (GF := GF) r0 pfx s0 ∗
      (□ ∀ w : EtcdKv, ⌜w ∈ s0 ∧ kp <+: w.key⌝ -∗
        ∃ r' : w64, etcdReached r' ∗ revKeyGone pfx w.key w.modRev r' ∗
          ⌜sint.Z r0 ≤ sint.Z r' ∧ sint.Z r' ≤ sint.Z rd⌝) ⊢
      dequeueOrder pfx kp le it r := by
  iintro ⟨#Hs, #Hd⟩
  unfold dequeueOrder
  iexists r0, s0
  iframe Hs
  isplitr
  · ipureintro; exact hlt
  iright
  isplitr
  · ipureintro; exact hput
  imodintro
  iintro %w %Hw
  ihave ⟨%r', #Hr', #Hg, %Hb⟩ := Hd $$ %w %Hw
  iexists r'
  iframe Hr' Hg
  ipureintro; exact ⟨Hb.1, Int.le_trans Hb.2 hrd⟩

end lemmas

end recipes
end EtcdGrove
end Perennial
