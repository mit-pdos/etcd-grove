/-
Lean-first (no Rocq counterpart).

# `client/v3/kubernetes`: shared definitions (phase 3 of `notes/k8s-etcd3-plan.md`)

The client Kubernetes' etcd3 store calls (`Get`, `OptimisticPut`, `OptimisticDelete`, `Count`)
wraps `New`'s client (`clientv3.Client`), so its specs are stated as linkvtxn's calls are
(`linkvtxn/Calls.lean`, whose generic half, `srvStart`, `kvRegs_*`, `rangeReply_state'`, they
reuse, as linkv3p does): a read update or an update fired at most once at each member, and the
answer as a function of the state `σ` the update fired at.

- `kvOut`: a response's `KV` field, `nil` or a key's key-value;
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
    · simp [List.filter_cons, h, List.find?_cons]
    · simp [List.filter_cons, h, List.find?_cons, ih]

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

end defs

end kubernetes
end EtcdGrove
end Perennial
