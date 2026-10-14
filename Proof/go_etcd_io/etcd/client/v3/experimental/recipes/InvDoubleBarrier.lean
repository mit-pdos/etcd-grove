/-
`client/v3/experimental/recipes`' `DoubleBarrier` (`double_barrier.go`): the vocabulary of
`Spec/go_etcd_io/etcd/client/v3/experimental/recipes/{NewDoubleBarrier,DoubleBarrier__*}.lean`.
Lean-first (no Rocq counterpart). See `decisions.md`, "Recipes", "Units 1b, 2 and 3".

**The protocol.** A double barrier on `key` for `count` processes keeps its entrants' ephemeral keys
under `key/waiters/` and a `key/ready` key. `Enter` fails (`ErrTooManyClients`) if `count` keys
are under `key/waiters` already; otherwise it creates its key (at `ek.rev`), lists the waiters again
sorted by create revision and, with at least `count` of them, either is too late (its key created
after the `count`-th: it deletes it, ignoring `Delete`'s error, and fails), or is the `count`-th
(it puts `key/ready`), or waits like the others for a put of `key/ready` from `ek.rev` on. `Leave`
lists the waiters: none left, done; the only one left and it is the caller, it deletes `key/ready`
and its key; the lowest (by mod revision) waits for the highest's deletion and retries; any other
deletes its key, waits for the lowest's deletion and retries.

**`count > 0`** is a precondition (`isDoubleBarrier`): with `count ≤ 0` `Enter`'s first check
always fails, and the code's `Kvs[count-1]` would be out of range.

**What `Enter` promises** (`enterReady`): on its direct path (the `count`-th waiter) its second get
saw at least `count` keys with the prefix `key/waiters` (`waitersSeen`); on its waiting path, only
that `key/ready` was written at a revision at least its key's creation (`readyPut`): who wrote it,
and after seeing what, is another process's business, outside the code. The protocol's premise
`readyPutsCounted` (every write of `key/ready` is preceded by a state with `count` waiters: true
if only `Enter`s of barriers on `key` for `count` write it, by the direct path's fact) makes both
paths say `waitersSeen` (`enterReady_counted`).

**The barrier** (`isDoubleBarrier b s γ client id key count`, persistent) and its **key**
(`dbMyKey b pfx o`, exclusive, as the RWMutex's `rwMyKey`).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.InvRWMutex

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3
open concurrency

/-! ## The waiters (pure) -/

/-- The number of keys of `s` with the prefix `wp`. -/
def waiterCount (wp : GoString) (s : List EtcdKv) : Nat :=
  (s.filter (fun v => decide (wp <+: v.key))).length

/-- `enteredClients`' get `OpGet(wp, WithPrefix(), WithSort(SortByCreateRevision, SortAscend))`. -/
def waitersOp (wp : GoString) : OpFull := opGetModel wp [withPrefixM, withSortM (W64 2) (W64 1)]

/-- `Leave`'s get `OpGet(wp, WithPrefix())`. -/
def leaveOp (wp : GoString) : OpFull := opGetModel wp [withPrefixM]

theorem waitersOp_fields (wp : GoString) (hp : wp ≠ []) :
    (waitersOp wp).key = wp ∧ (waitersOp wp).base.rangeEnd = prefixRangeEnd wp ∧
    (waitersOp wp).effSortOrder = W64 1 ∧ (waitersOp wp).sortTarget = W64 2 ∧
    (waitersOp wp).base.limit = W64 0 ∧ (waitersOp wp).base.countOnly = false ∧
    (waitersOp wp).keysOnly = false ∧ (waitersOp wp).base.minModRev = W64 0 ∧
    (waitersOp wp).base.maxModRev = W64 0 ∧ (waitersOp wp).base.minCreateRev = W64 0 ∧
    (waitersOp wp).base.maxCreateRev = W64 0 := by
  simp [waitersOp, opGetModel, opFold, withPrefixM, withSortM, OpFull.getInit, OpFull.newOp,
    OpModel.zero, hp, OpFull.effSortOrder]

theorem leaveOp_fields (wp : GoString) (hp : wp ≠ []) :
    (leaveOp wp).key = wp ∧ (leaveOp wp).base.rangeEnd = prefixRangeEnd wp ∧
    (leaveOp wp).effSortOrder = W64 0 ∧
    (leaveOp wp).base.limit = W64 0 ∧ (leaveOp wp).base.countOnly = false ∧
    (leaveOp wp).keysOnly = false ∧ (leaveOp wp).base.minModRev = W64 0 ∧
    (leaveOp wp).base.maxModRev = W64 0 ∧ (leaveOp wp).base.minCreateRev = W64 0 ∧
    (leaveOp wp).base.maxCreateRev = W64 0 := by
  simp [leaveOp, opGetModel, opFold, withPrefixM, OpFull.getInit, OpFull.newOp, OpModel.zero,
    hp, OpFull.effSortOrder]

theorem waitersOp_t (wp : GoString) : (waitersOp wp).t = W64 1 ∧ (leaveOp wp).t = W64 1 := by
  by_cases h : wp = [] <;> simp [waitersOp, leaveOp, opGetModel, opFold, withPrefixM, withSortM,
    OpFull.getInit, OpFull.newOp, OpModel.zero, h]

theorem waitersOp_rev (pfx wp : GoString) (hne : wp ≠ pfx) (hw : wp ≠ []) (hp : pfx ≠ []) :
    (waitersOp wp).base.rev = W64 0 ∧ (waitersOp wp).base.serializable = false ∧
      (waitersOp wp).isPrefixGet pfx = false ∧
    (leaveOp wp).base.rev = W64 0 ∧ (leaveOp wp).base.serializable = false ∧
      (leaveOp wp).isPrefixGet pfx = false := by
  simp [waitersOp, leaveOp, opGetModel, opFold, withPrefixM, withSortM, OpFull.getInit,
    OpFull.newOp, OpModel.zero, hw, hp, OpFull.isPrefixGet, hne]

theorem waitersOp_not_panics :
    ¬ opGetPanics [withPrefixM, withSortM (W64 2) (W64 1)] ∧ ¬ opGetPanics [withPrefixM] := by
  constructor <;> simp [opFold, withPrefixM, withSortM, OpFull.newOp, OpModel.zero, opGetPanics]

theorem waitersOp_under (pfx wp : GoString) (hp : wp ≠ []) (h : pfx <+: wp) :
    KeyRangeUnder pfx (waitersOp wp).key (waitersOp wp).base.rangeEnd ∧
      KeyRangeUnder pfx (leaveOp wp).key (leaveOp wp).base.rangeEnd := by
  obtain ⟨hk, he, -⟩ := waitersOp_fields wp hp
  obtain ⟨hk', he', -⟩ := leaveOp_fields wp hp
  rw [hk, he, hk', he']
  exact ⟨fun k hk' => h.trans (keyRangeUnder_prefix wp hp k hk'),
    fun k hk' => h.trans (keyRangeUnder_prefix wp hp k hk')⟩

/-- The selection of a prefix get with no filter: the keys of `s` with the prefix. -/
theorem rangeSel_prefix (wp : GoString) (o : OpFull) (s : List EtcdKv) (hp : wp ≠ [])
    (hk : o.key = wp) (he : o.base.rangeEnd = prefixRangeEnd wp)
    (h1 : o.base.minModRev = W64 0) (h2 : o.base.maxModRev = W64 0)
    (h3 : o.base.minCreateRev = W64 0) (h4 : o.base.maxCreateRev = W64 0) :
    rangeSel s o = s.filter (fun v => decide (wp <+: v.key)) := by
  unfold rangeSel rangeIn
  rw [List.filter_filter]
  apply List.filter_congr
  intro v _
  rw [hk, he, kvFilterOk_zero o v h1 h2 h3 h4, Bool.true_and]
  have := inRange_prefix wp v.key hp
  cases hr : inRange wp (prefixRangeEnd wp) v.key <;> simp_all

/-- **`enteredClients`' get** lists the waiters (the keys with the prefix `wp`), sorted by create
revision. -/
theorem waitersOp_kvs (wp : GoString) (s kvs : List EtcdKv) (hp : wp ≠ [])
    (h : rangeKvsOk (waitersOp wp) (rangeSel s (waitersOp wp)) kvs) :
    kvs.Perm (s.filter (fun v => decide (wp <+: v.key))) ∧
      kvs.Pairwise (fun a b => sint.Z a.createRev ≤ sint.Z b.createRev) := by
  obtain ⟨hkey, he, hso, hst, hl, hc, hko, h1, h2, h3, h4⟩ := waitersOp_fields wp hp
  rw [rangeSel_prefix wp _ s hp hkey he h1 h2 h3 h4] at h
  obtain ⟨l, hperm, -, hsorted, -, rfl⟩ := h
  have hsorted := hsorted hso
  rw [hst] at hsorted
  simp only [hc, hl, hko]
  simp
  refine ⟨hperm, ?_⟩
  exact hsorted.imp (fun h => by simpa [kvLeBy] using h)

/-- **`Leave`'s get** lists the waiters, in key order. -/
theorem leaveOp_kvs (wp : GoString) (s kvs : List EtcdKv) (hp : wp ≠ [])
    (h : rangeKvsOk (leaveOp wp) (rangeSel s (leaveOp wp)) kvs) :
    kvs = s.filter (fun v => decide (wp <+: v.key)) := by
  obtain ⟨hkey, he, hso, hl, hc, hko, h1, h2, h3, h4⟩ := leaveOp_fields wp hp
  rw [rangeSel_prefix wp _ s hp hkey he h1 h2 h3 h4] at h
  obtain ⟨l, -, hl0, -, -, rfl⟩ := h
  rw [hl0 hso]
  simp [hc, hl, hko]

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

/-! ## What `Enter` promises -/

/-- **At revision `R`, at least `count` keys with the prefix `wp` were present** (persistent). -/
def waitersSeen (pfx wp : GoString) (count : w64) (R : w64) : IProp GF :=
  iprop(∃ s : List EtcdKv, □ etcdState R pfx s ∗ ⌜sint.Z count ≤ (waiterCount wp s : Int)⌝)

instance waitersSeen_persistent (pfx wp : GoString) (count R : w64) :
    Persistent (waitersSeen (GF := GF) pfx wp count R) := by
  unfold waitersSeen; infer_instance

/-- **`rk` was written at revision `z`** (persistent): present in etcd's state at `z` with mod
revision `z`. -/
def readyPut (pfx rk : GoString) (z : w64) : IProp GF :=
  iprop(∃ s : List EtcdKv, □ etcdState z pfx s ∗ ⌜∃ v ∈ s, v.key = rk ∧ v.modRev = z⌝)

instance readyPut_persistent (pfx rk : GoString) (z : w64) :
    Persistent (readyPut (GF := GF) pfx rk z) := by
  unfold readyPut; infer_instance

/-- **What a successful `Enter` saw**, for its key created at `c` (persistent): at a revision `R`
etcd has reached, at least `count` waiters (its direct path: it put `key/ready` itself); or a write
of `key/ready` at a revision `z ≥ c` etcd has reached (its waiting path). -/
def enterReady (pfx key : GoString) (count c : w64) : IProp GF :=
  iprop((∃ R : w64, etcdReached R ∗ waitersSeen pfx (key ++ go!"/waiters") count R) ∨
    (∃ z : w64, etcdReached z ∗ readyPut pfx (key ++ go!"/ready") z ∗ ⌜sint.Z c ≤ sint.Z z⌝))

instance enterReady_persistent (pfx key : GoString) (count c : w64) :
    Persistent (enterReady (GF := GF) pfx key count c) := by
  unfold enterReady; infer_instance

/-- **The protocol's premise on `key/ready`** (persistent; on etcd's history, that is, on every
process using `key`): every write of `key/ready` (at `z`) is preceded by a state with at least
`count` waiters (at some `R ≤ z`). Holds if only `Enter`s of double barriers on `key` for `count`
write `key/ready`, by their direct path's `waitersSeen`. -/
def readyPutsCounted (pfx key : GoString) (count : w64) : IProp GF :=
  iprop(□ ∀ z : w64, readyPut pfx (key ++ go!"/ready") z -∗
    ∃ R : w64, waitersSeen pfx (key ++ go!"/waiters") count R ∗ ⌜sint.Z R ≤ sint.Z z⌝)

instance readyPutsCounted_persistent (pfx key : GoString) (count : w64) :
    Persistent (readyPutsCounted (GF := GF) pfx key count) := by
  unfold readyPutsCounted; infer_instance

/-- **Under the protocol's premise, `Enter` saw `count` waiters**: at a revision etcd has reached
(so at or before `Enter`'s return), at least `count` keys with the prefix `key/waiters` were
present. -/
theorem enterReady_counted (pfx key : GoString) (count c : w64) :
    enterReady (GF := GF) pfx key count c ∗ readyPutsCounted pfx key count ⊢
      ∃ R : w64, etcdReached R ∗ waitersSeen pfx (key ++ go!"/waiters") count R := by
  unfold enterReady readyPutsCounted
  iintro ⟨(H | ⟨%z, #Hz, #Hp, -⟩), #Hprem⟩
  · iexact H
  · ihave ⟨%R, #HR, %HRz⟩ := Hprem $$ %z Hp
    iexists R
    iframe HR
    iapply etcdReached_mono z R HRz $$ Hz

/-! ## The barrier -/

/-- **The double barrier** `b` (persistent): its session `s` (of `client`, with the lease `id`), its
context (`context.TODO()`), its `key` and `count` (positive: see the module docstring), read-only;
the client's recipes contracts for the prefix `key ++ "/"` (`isEtcdRecipesClient`: under the
premise that a watch channel is never closed) and `context`'s package fact `WaitEvents` needs. -/
def isDoubleBarrier (b s : Loc) (γ : SessionNames) (client : Loc) (id : w64) (key : GoString)
    (count : w64) : IProp GF :=
  iprop(structFieldRef DoubleBarrier go!"s" b ↦□ s ∗
    structFieldRef DoubleBarrier go!"ctx" b ↦□ GoInterface.ok todoCtxVal ∗
    structFieldRef DoubleBarrier go!"key" b ↦□ key ∗
    structFieldRef DoubleBarrier go!"count" b ↦□ count ∗ ⌜0 < sint.Z count⌝ ∗
    isSession s γ client id ∗ isEtcdRecipesClient client (key ++ go!"/") ∗ context.isClosedchanInit)

instance isDoubleBarrier_persistent (b s : Loc) (γ : SessionNames) (client : Loc) (id : w64)
    (key : GoString) (count : w64) :
    Persistent (isDoubleBarrier (GF := GF) b s γ client id key count) := by
  unfold isDoubleBarrier; infer_instance

/-- **The barrier's key** (exclusive), as `rwMyKey`: the field `myKey` holds `ek`; for
`some (ek, st)`, the proof owns the `*EphemeralKV` `ek` with the record `st` (a key under `pfx`,
whose `KV`, if any, has the recipes' contracts); for `none`, a pointer the proof does not track
(nil after `NewDoubleBarrier`). -/
def dbMyKey (b : Loc) (pfx : GoString) : Option (Loc × RemoteKVSt) → IProp GF
  | none => iprop(∃ ek : Loc, structFieldRef DoubleBarrier go!"myKey" b ↦ ek)
  | some (ek, st) => iprop(structFieldRef DoubleBarrier go!"myKey" b ↦ ek ∗ ownEphemeralKV ek st ∗
      isRecipesKV st.kv pfx ∗ ⌜pfx <+: st.key⌝)

/-- The field `myKey` of any key state (dropping the key's ownership). -/
theorem dbMyKey_field (b : Loc) (pfx : GoString) (o : Option (Loc × RemoteKVSt)) :
    dbMyKey (GF := GF) b pfx o ⊢ ∃ ek : Loc, structFieldRef DoubleBarrier go!"myKey" b ↦ ek := by
  rcases o with _ | ⟨ek, st⟩
  · unfold dbMyKey; iintro H; iexact H
  · unfold dbMyKey; iintro ⟨H, -⟩; iexists ek; iexact H

/-- The key a successful `newUniqueEphemeralKey(s, kp)` returns, with the client's `KV`, as
`myKey`'s state. -/
theorem dbMyKey_new (b client : Loc) (pfx kp key : GoString) (kv : GoInterfaceOk) (ek : Loc)
    (r : w64) (hp : pfx <+: kp) (hk : kp ++ go!"/" <+: key) :
    structFieldRef DoubleBarrier go!"myKey" b ↦ ek ∗
      ownEphemeralKV (GF := GF) ek ⟨GoInterface.ok kv, key, r, []⟩ ∗
      clientKVAddr client ↦□ GoInterface.ok kv ∗ isEtcdRecipesClient client pfx ⊢
      dbMyKey b pfx (some (ek, ⟨GoInterface.ok kv, key, r, []⟩)) := by
  iintro ⟨Hmk, Hek, #HKVf, #Hcl⟩
  ihave ⟨%kv', #HKVf', #Hkvc⟩ := isEtcdRecipesClient_kv client pfx $$ Hcl
  icombine HKVf HKVf' gives %Heq
  cases Heq
  simp only [dbMyKey]
  iframe Hmk Hek Hkvc
  ipureintro
  exact hp.trans ((List.prefix_append _ _).trans hk)

/-- **`enteredClients`' response** `resp` at revision `R` for the waiters' prefix `wp` (under
`pfx`): its `Kvs` hold `kvs`, the keys with the prefix `wp` of etcd's state at `R`, sorted by
create revision (persistent). -/
def waitersResp (pfx wp : GoString) (resp : Loc) (R : w64) (kvs : List EtcdKv) : IProp GF :=
  iprop(∃ (s : List EtcdKv) (sl : GoSlice) (ps : List Loc),
    □ etcdState R pfx s ∗ ⌜EtcdStateWf pfx s⌝ ∗
    structFieldRef go_etcd_io.etcd.client.v3.GetResponse go!"Kvs" resp ↦□ sl ∗ sl ↦*□ ps ∗
    kvPtrsAt ps kvs ∗
    ⌜kvs.Perm (s.filter (fun v => decide (wp <+: v.key))) ∧
      kvs.Pairwise (fun a b => sint.Z a.createRev ≤ sint.Z b.createRev)⌝)

instance waitersResp_persistent (pfx wp : GoString) (resp : Loc) (R : w64) (kvs : List EtcdKv) :
    Persistent (waitersResp (GF := GF) pfx wp resp R kvs) := by
  unfold waitersResp; infer_instance

/-- **What `Enter` returns**, called knowing etcd has reached `lo`: `nil` with a fresh key `st.key`
under `key/waiters/` (created at `st.rev ≥ lo` with the session's lease `id`, its record's `KV`
not nil, so that `Leave` deletes it) in `myKey`, and `enterReady`; `ErrTooManyClients`, with `myKey` anything (unchanged if it failed before creating
its key; otherwise its key, which its `Delete`, whose error the code ignores, may have left in
place); or another error, with `myKey` anything. -/
def enterResult (b : Loc) (key : GoString) (count id lo : w64) (err : GoInterface) : IProp GF :=
  iprop((⌜err = GoInterface.nil⌝ ∗ ∃ (ek : Loc) (st : RemoteKVSt),
      dbMyKey b (key ++ go!"/") (some (ek, st)) ∗
      keyCreatedAt (key ++ go!"/") st.key [] id st.rev ∗
      enterReady (key ++ go!"/") key count st.rev ∗
      ⌜(key ++ go!"/waiters") ++ go!"/" <+: st.key ∧ sint.Z lo ≤ sint.Z st.rev ∧
        st.kv ≠ GoInterface.nil⌝) ∨
    (isPkgErr ErrTooManyClients err ∗ ∃ o : Option (Loc × RemoteKVSt), dbMyKey b (key ++ go!"/") o) ∨
    (⌜err ≠ GoInterface.nil⌝ ∗ ∃ o : Option (Loc × RemoteKVSt), dbMyKey b (key ++ go!"/") o))

/-- **What `Leave` returns** for the key record `st`, called knowing etcd has reached `lo`: `nil`
with the key absent at a revision at least `lo` etcd has reached, or with the record's `KV` nil
(the caller's own earlier `Delete` of it: `Enter`'s `ErrTooManyClients` path, an earlier `Leave`;
`Leave`'s `Delete` then does nothing); or an error. -/
def leaveResult (pfx : GoString) (st : RemoteKVSt) (lo : w64) (err : GoInterface) : IProp GF :=
  iprop((⌜err = GoInterface.nil⌝ ∗
      ((∃ r : w64, etcdReached r ∗ etcdAbsent pfx st.key r ∗ ⌜sint.Z lo ≤ sint.Z r⌝) ∨
        ⌜st.kv = GoInterface.nil⌝)) ∨
    ⌜err ≠ GoInterface.nil⌝)

/-- What `RemoteKV.Delete` returns for the record `st` (its spec's postcondition) is a
`leaveResult`. -/
theorem leaveResult_of_delete (pfx : GoString) (st : RemoteKVSt) (lo : w64) (err : GoInterface) :
    (match st.kv with
      | .nil => iprop(⌜err = GoInterface.nil⌝)
      | .ok _ => deleteResult (GF := GF) pfx lo (opDeleteModel st.key []) err) ⊢
      leaveResult pfx st lo err := by
  unfold leaveResult
  rcases hkv : st.kv with kv | _
  · simp only
    iintro Hres
    iunfold deleteResult at Hres
    icases Hres with (%Hne | ⟨%Hnil, %r, %s, #Hr, %Hrs, #Hst⟩)
    · iright; ipureintro; exact Hne
    ileft
    isplitr
    · ipureintro; exact Hnil
    ileft
    iexists r
    iframe Hr
    isplitr
    · iapply concurrency.deleteTxn_absent pfx st.key r s $$ Hst
    ipureintro; exact Hrs.1
  · simp only
    iintro %H
    ileft
    isplitr
    · ipureintro; exact H
    iright; ipureintro; trivial

instance leaveResult_persistent (pfx : GoString) (st : RemoteKVSt) (lo : w64) (err : GoInterface) :
    Persistent (leaveResult (GF := GF) pfx st lo err) := by
  unfold leaveResult; infer_instance

end defs

end recipes
end EtcdGrove
end Perennial
