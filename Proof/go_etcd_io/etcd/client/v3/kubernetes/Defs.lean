/-
Lean-first (no Rocq counterpart).

# `client/v3/kubernetes`: shared definitions (phase 3 of `notes/k8s-etcd3-plan.md`)

The client Kubernetes' etcd3 store calls (`Get`, `OptimisticPut`, `OptimisticDelete`, `Count`)
wraps `New`'s client (`clientv3.Client`), so its specs are stated as linkvtxn's calls are
(`linkvtxn/Calls.lean`, whose generic half, `srvStart`, `kvRegs_*`, `rangeReply_state'`, they
reuse, as linkv3p does): a read update or an update fired at most once at each member, and the
answer as a function of the state `σ` the update fired at.

- `kvOut`: a response's `KV` field, `nil` or a key's key-value;
- `kvIs_ne_null`: a response's key-value pointer is not `nil` (the package's one `sorry`, a gap of
  the server's response predicate);
- `getKey1Op`, `srvRangeOk_getKey1`: `Get`'s range, `OpGet(key, WithRev(0), WithLimit(1))` on the
  wire, selects the key's first key-value (`findKey`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Calls

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kubernetes

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver mvcc

section pure
variable [ext : FfiSyntax]

/-- `Get`'s range on the wire: `OpGet(key, WithRev(0), WithLimit(1))`. -/
abbrev getKey1Op (key : GoString) : OpFull :=
  txn.rangeOpOf key [] (W64 0) (W64 1) (W32 0) (W32 0) false false false (W64 0) (W64 0) (W64 0)
    (W64 0)

theorem rangeWireOf_getKey1 (key : GoString) :
    rangeWireOf (opGetModel key [withRevM (W64 0), withLimitM (W64 1)]) = getKey1Op key := rfl

/-- The first element of a filter is `find?`'s. -/
theorem filter_take_one {α : Type} (p : α → Bool) (l : List α) :
    (l.filter p).take 1 = (l.find? p).toList := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : p a
    · simp [h]
    · simp [h, ih]

/-- **`Get`'s range selects the key's first key-value** (pure; with `WithLimit(1)` the server
reads two and returns one, `More` if there were two). -/
theorem srvRangeOk_getKey1 (key : GoString) (s kvs : List EtcdKv) (more : Bool)
    (h : txn.srvRangeOk (getKey1Op key) s kvs more) :
    kvs = (findKey key s).toList := by
  obtain ⟨L, hsort, -, hkvs⟩ := h
  have hpre : txn.srvPre (getKey1Op key) s = (s.filter (fun v => decide (v.key = key))).take 2 := by
    have hr : txn.kvRead false = id := by funext v; simp [txn.kvRead]
    unfold txn.srvPre
    simp [txn.rangeLimitOf, txn.hasRevFilters, txn.isDefaultOrd, mvcc.limitOf, mvcc.takeLimit,
      txn.fastKeysOnly, rangeIn, inRange, hr]
    have h2 : sint.Z (2#64) = 2 := by decide
    rw [h2]
    simp only [show (0 : Int) < 2 from by decide, ↓reduceIte]
    apply List.filter_eq_self.2
    intro v _
    simp [kvFilterOk]
  have hord : (getKey1Op key).effSortOrder = W64 0 := by
    simp [OpFull.effSortOrder]
  have hL : L = txn.srvPre (getKey1Op key) s := by
    obtain ⟨-, -, -, h4⟩ := hsort
    exact h4 (by rw [hord]; decide) (by rw [hord]; decide)
  have hid : txn.respKv (getKey1Op key) = id := by funext v; simp [txn.respKv]
  rw [hkvs, hL, hpre, hid, List.map_id]
  unfold txn.srvTrunc txn.srvMore
  have hf := filter_take_one (fun v : EtcdKv => decide (v.key = key)) s
  unfold findKey
  rw [← hf]
  generalize s.filter (fun v => decide (v.key = key)) = F
  have h1 : sint.Z (getKey1Op key).base.limit = 1 := by
    simp only [getKey1Op, txn.rangeOpOf]; decide
  rw [h1]
  match F with
  | [] => simp
  | [a] => simp
  | a :: b :: F' => simp

/-- `Keys`'s range on the wire:
`OpGet(pfx, WithRange(GetPrefixRangeEnd(pfx)), WithKeysOnly(), WithRev(0))`. -/
abbrev keysPrefixOp (pfx : GoString) : OpFull :=
  txn.rangeOpOf pfx (prefixRangeEnd pfx) (W64 0) (W64 0) (W32 0) (W32 0) false true false
    (W64 0) (W64 0) (W64 0) (W64 0)

theorem rangeWireOf_keysPrefix (pfx : GoString) :
    rangeWireOf (opGetModel pfx [withRangeM (prefixRangeEnd pfx), withKeysOnlyM, withRevM (W64 0)]) =
      keysPrefixOp pfx := rfl

/-- **`Keys`'s range selects the prefix range's key-values (without values/leases)** (pure). -/
theorem srvRangeOk_keysPrefix (pfx : GoString) (s kvs : List EtcdKv) (more : Bool)
    (h : txn.srvRangeOk (keysPrefixOp pfx) s kvs more) :
    kvs.map EtcdKv.key =
      (s.filter (fun v => inRange pfx (prefixRangeEnd pfx) v.key)).map EtcdKv.key ∧
      more = false := by
  obtain ⟨L, hsort, hmore, hkvs⟩ := h
  have hpre : txn.srvPre (keysPrefixOp pfx) s =
      (s.filter (fun v => inRange pfx (prefixRangeEnd pfx) v.key)).map (txn.kvRead true) := by
    unfold txn.srvPre
    simp [txn.rangeLimitOf, txn.hasRevFilters, mvcc.limitOf, mvcc.takeLimit, txn.fastKeysOnly,
      rangeIn, kvFilterOk]
  have hord : (keysPrefixOp pfx).effSortOrder = W64 0 := by
    simp [OpFull.effSortOrder]
  have hL : L = txn.srvPre (keysPrefixOp pfx) s := by
    obtain ⟨-, -, -, h4⟩ := hsort
    exact h4 (by rw [hord]; decide) (by rw [hord]; decide)
  have hm : txn.srvMore (keysPrefixOp pfx) L = false := by
    simp [txn.srvMore]
  refine ⟨?_, by rw [hmore, hm]⟩
  rw [hkvs]
  unfold txn.srvTrunc
  rw [hm, hL, hpre]
  simp [List.map_map, txn.respKv, txn.kvRead]

/-- **`Keys`'s count is the number of keys in `[pfx, prefixRangeEnd pfx)`** (pure). -/
theorem srvCount_keysPrefix (pfx : GoString) (s : List EtcdKv) :
    txn.srvCount (keysPrefixOp pfx) s true =
      W64 (((s.filter (fun v => inRange pfx (prefixRangeEnd pfx) v.key)).length : Int)) := by
  unfold txn.srvCount
  simp [txn.rangeLimitOf, txn.hasRevFilters, mvcc.limitOf, mvcc.totalOf, rangeIn]

/-- The start key `WithPrefix()` sets for `pfx`: `"\x00"` when `pfx` is empty, `pfx` otherwise. -/
def prefixStart (pfx : GoString) : GoString :=
  if pfx = [] then [W8 0] else pfx

/-- `Count`'s range on the wire: `OpGet(pfx, WithPrefix(), WithCountOnly())`. -/
abbrev countPrefixOp (pfx : GoString) : OpFull :=
  txn.countOp (prefixStart pfx) (prefixRangeEnd pfx) (W64 0)

theorem rangeWireOf_countPrefix (pfx : GoString) :
    rangeWireOf (opGetModel pfx [withPrefixM, withCountOnlyM]) = countPrefixOp pfx := by
  by_cases h : pfx = []
  · subst h; rfl
  · have hop : opGetModel pfx [withPrefixM, withCountOnlyM] =
        { (OpFull.getInit pfx) with
          base := { OpModel.zero with rangeEnd := prefixRangeEnd pfx, countOnly := true },
          withPrefix := true, rangeEndSet := true } := by
      unfold opGetModel opFold OpFull.getInit OpFull.newOp withPrefixM withCountOnlyM
      simp [h]
    have hst : prefixStart pfx = pfx := by simp [prefixStart, h]
    rw [hop, countPrefixOp, hst]
    rfl

/-- **`Count`'s count is the number of keys in `[prefixStart pfx, prefixRangeEnd pfx)`** (pure). -/
theorem srvCount_countPrefix (pfx : GoString) (s : List EtcdKv) :
    txn.srvCount (countPrefixOp pfx) s true =
      W64 (((s.filter (fun v => inRange (prefixStart pfx) (prefixRangeEnd pfx) v.key)).length : Int)) := by
  unfold txn.srvCount
  simp [countPrefixOp, txn.countOp, rangeIn]

/-- `OptimisticPut`'s transaction (linkv's): put `val` at `key` if its mod revision is `rev`, else
get it if `g`. -/
abbrev optPutTxn (key val : GoString) (rev : w64) (g : Bool) : TxnModel :=
  linkv.txnOf [.mod key rev] [.put key val] (if g then [.get key] else [])

/-- `OptimisticDelete`'s transaction (linkv's). -/
abbrev optDelTxn (key : GoString) (rev : w64) (g : Bool) : TxnModel :=
  linkv.txnOf [.mod key rev] [.del key] (if g then [.get key] else [])

/-- **A failed `GetOnFailure` transaction's responses** (pure): its else branch's get, one range
response whose key-values are the key's at the state. -/
theorem failure_resps (s : List EtcdKv) (r : w64) (cs : List (linkv.MCmp GoString GoString))
    (t : List (linkv.MOp GoString GoString)) (key : GoString) (resps : List OpRespM)
    (hok : (txn.srvRunTxn r s (linkv.txnOf cs t [.get key])).1 = false)
    (hrel : client.opRespsRel false ((linkv.txnOf cs t [.get key]).branch false)
      (txn.srvRunTxn r s (linkv.txnOf cs t [.get key])).2.2 resps) :
    ∃ rv more count, resps = [.range rv (s.filter fun v => decide (v.key = key)) more count] := by
  unfold txn.srvRunTxn at hok hrel
  simp only at hok hrel
  rw [hok] at hrel
  simp only [linkv.txnOf, TxnModel.branch, List.map_cons, List.map_nil, Bool.false_eq_true,
    ↓reduceIte, linkv.tOpOf] at hrel
  rw [txn.srvOps_cons, txn.srvOps_nil] at hrel
  simp only [txn.srvOp] at hrel
  match resps, hrel with
  | [m], hrel =>
    simp only [client.opRespsRel] at hrel
    obtain ⟨h1, -⟩ := hrel
    cases m with
    | range rv kvs more count =>
      simp only [client.opRespRel, Bool.false_eq_true, ↓reduceIte] at h1
      obtain ⟨-, kvs', hk, hkv⟩ := h1
      refine ⟨rv, more, count, ?_⟩
      obtain ⟨l, -, h0, -, -, hl⟩ := hk
      have hord : (linkv.getOp key).effSortOrder = W64 0 := by simp [OpFull.effSortOrder]
      have hlz : txn.leaseZ (txn.fastKeysOnly (linkv.getOp key)) = id := by
        funext v; simp [txn.leaseZ, txn.fastKeysOnly]
      have hsel : rangeSel s (linkv.getOp key) = s.filter fun v => decide (v.key = key) := by
        unfold rangeSel rangeIn
        rw [List.filter_filter]
        apply List.filter_congr
        intro v _
        simp [kvFilterOk, inRange]
      rw [hkv, hlz, List.map_id, hl, ← hsel, ← h0 hord]
      simp
    | _ => simp [client.opRespRel] at h1
  | [], hrel => simp [client.opRespsRel] at hrel
  | _ :: _ :: _, hrel => simp [client.opRespsRel] at hrel

end pure

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A key's key-value in a response** (`resp.KV`): `nil` for none, or the key-value,
read-only. -/
def kvOut (p : Loc) (kv : Option EtcdKv) : IProp GF :=
  match kv with
  | none => iprop(⌜p = null⌝)
  | some v => iprop(⌜p ≠ null⌝ ∗ txn.kvIs p v)

instance kvOut_persistent (p : Loc) (kv : Option EtcdKv) : Persistent (kvOut (GF := GF) p kv) := by
  unfold kvOut; cases kv <;> infer_instance

/-- **A response's key-value pointer is not `nil`** (`sorry`). The server's response predicate
`txn.kvIs` does not say it (its field points-tos do not imply it), and the store branches on
`KV == nil`. `notes/k8s-etcd3-plan.md`, "From the etcd client proof", request 3: `txn.kvIs`
carrying `⌜l ≠ null⌝` (from the struct's typed points-to, `txn.kvAt_persist'`) proves it. -/
theorem kvIs_ne_null (l : Loc) (v : EtcdKv) : txn.kvIs (GF := GF) l v ⊢ ⌜l ≠ null⌝ := by
  sorry

/-- A key-value as a response's `KV` (`kvIs_ne_null`). -/
theorem kvOut_some (l : Loc) (v : EtcdKv) : txn.kvIs (GF := GF) l v ⊢ kvOut l (some v) := by
  iintro #H
  ihave %Hn := kvIs_ne_null l v $$ H
  simp only [kvOut]
  isplitr
  · ipureintro; exact Hn
  · iexact H

/-- The one key-value of a list, if it has exactly one (`len(Kvs) == 1`). -/
def single {α : Type} : List α → Option α
  | [v] => some v
  | _ => none

/-- **A response's slice of keys** (`resp.Keys` in `KeysResponse`): a slice of `[]byte` slices `ksls`
of the same length as `ks`, where each `ksls[i]` points to `ks[i]` read-only. -/
def keysSlice (s : GoSlice) (ks : List GoString) : IProp GF :=
  iprop(∃ ksls : List GoSlice, s ↦* ksls ∗ ⌜ksls.length = ks.length⌝ ∗
    ∀ (i : Nat) (ksl : GoSlice) (k : GoString),
      ⌜ksls[i]? = some ksl⌝ -∗ ⌜ks[i]? = some k⌝ -∗ ksl ↦*□ k)

open Iris.ProofMode in
/-- **What a linearizable range's reply says, including `m.count`** (extends `rangeReply_state_bnd`
with `m.count = txn.srvCount o σ.kvs true`). -/
theorem rangeReply_state_count_bnd
    [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    [go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
    [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.Assumptions]
    (E : apply.AEnv GF) (γr : ReadNames) (c cid mid : w64)
    (o : OpFull) (F : mvcc.Log) (Q : KVState → IProp GF) (m : RangeRespM)
    (hs : o.base.serializable = false) (hr : o.base.rev = W64 0) :
    client.rangeReplyOk E γr c F o cid mid Q m ⊢
      ∃ σ : KVState, □ Q σ ∗ ⌜txn.srvRangeOk o σ.kvs m.kvs m.more ∧
        m.count = txn.srvCount o σ.kvs true ∧
        m.hdr.revision = W64 (σ.rev : Int) ∧ σ.rev + 3 < 2 ^ 63⌝ := by
  iintro #H
  iunfold client.rangeReplyOk at H
  icases H with ⟨%l, -, -, %Hl, -, #HQ⟩
  simp only [hs, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨hlen, hlen', hrev, -, -, -, hcnt, hsel, -⟩ := Hl
  have hst : mvcc.stateAt l (sint.nat (mvcc.rangeRev m.hdr.revision o.base.rev)) =
      mvcc.stateAfter l := by
    have h1 : mvcc.rangeRev m.hdr.revision o.base.rev = m.hdr.revision := by
      simp [mvcc.rangeRev, hr]
    rw [h1, hrev]
    have h2 : sint.nat (W64 ((l.length : Int) - 1)) = l.length - 1 := by
      unfold sint.nat; word
    rw [h2, mvcc.stateAt_last]
  rw [hst] at hsel hcnt
  iexists kvStateOf l
  iframe HQ
  ipureintro
  refine ⟨hsel, hcnt, ?_, ?_⟩
  · rw [hrev]
    unfold kvStateOf
    simp only
    congr 1
    omega
  · unfold kvStateOf
    simp only
    omega

end defs

end kubernetes
end EtcdGrove
end Perennial
