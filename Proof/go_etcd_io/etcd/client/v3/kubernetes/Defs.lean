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

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Calls
public import Proof.go_etcd_io.etcd.client.v3.kubernetes.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kubernetes

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver mvcc

section pure
variable [GooseExts]

/-! ### The requests' sizes (2026-10-30, `notes/invoke-size-b.md`) -/

open etcd_txnlin in
/-- The optimistic transactions' payload: the key three times at most (comparison, operation,
`GetOnFailure`'s get) and the value. -/
theorem clientTxn_size {cs : List (linkv.MCmp GoString GoString)}
    {t e : List (linkv.MOp GoString GoString)} {key val : GoString} (rev : w64)
    (hcs : cs = [.mod key rev]) (ht : t = [.put key val] ∨ t = [.del key])
    (he : e = [] ∨ e = [.get key]) (hk : key.length ≤ 2 ^ 27) (hv : val.length ≤ 2 ^ 28) :
    txnSizeOk (txnWireOf (clientTxn cs t e)) := by
  apply txnSizeOk_wireOf
  subst hcs
  unfold txnSizeOk txnWireLen clientTxn
  rcases ht with rfl | rfl <;> rcases he with rfl | rfl <;>
    simp [linkv.cmpOf, clientTOp, cmpWireLen, TxnOp.wireLen, opWireLen, wireSlack, opGetModel,
      opDeleteModel, opFold, OpFull.getInit, OpFull.deleteInit, OpFull.newOp, OpModel.zero] <;>
    omega

/-- `Get`'s range on the wire: `OpGet(key, WithRev(rev), WithLimit(1))`. -/
abbrev getKey1Op (key : GoString) (rev : w64) : OpFull :=
  txn.rangeOpOf key [] rev (W64 1) (W32 0) (W32 0) false false false (W64 0) (W64 0) (W64 0)
    (W64 0)

theorem rangeWireOf_getKey1 (key : GoString) (rev : w64) :
    rangeWireOf (opGetModel key [withRevM rev, withLimitM (W64 1)]) = getKey1Op key rev := rfl

/-- `Get`'s range passes the server's check (`v3rpc.rangeCheck`) for a non-empty key. -/
theorem rangeCheck_getKey1 (key : GoString) (rev : w64) (hk : key ≠ []) :
    v3rpc.rangeCheck (getKey1Op key rev) = none := by
  unfold v3rpc.rangeCheck
  simp [txn.rangeOpOf, hk, v3rpc.sortOrderKnown, v3rpc.sortTargetKnown]

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
theorem srvRangeOk_getKey1 (key : GoString) (rev : w64) (s kvs : List EtcdKv) (more : Bool)
    (h : txn.srvRangeOk (getKey1Op key rev) s kvs more) :
    kvs = (findKey key s).toList := by
  obtain ⟨L, hsort, -, hkvs⟩ := h
  have hpre : txn.srvPre (getKey1Op key rev) s = (s.filter (fun v => decide (v.key = key))).take 2 := by
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
  have hord : (getKey1Op key rev).effSortOrder = W64 0 := by
    simp [OpFull.effSortOrder]
  have hL : L = txn.srvPre (getKey1Op key rev) s := by
    obtain ⟨-, -, -, h4⟩ := hsort
    exact h4 (by rw [hord]; decide) (by rw [hord]; decide)
  have hid : txn.respKv (getKey1Op key rev) = id := by funext v; simp [txn.respKv]
  rw [hkvs, hL, hpre, hid, List.map_id]
  unfold txn.srvTrunc txn.srvMore
  have hf := filter_take_one (fun v : EtcdKv => decide (v.key = key)) s
  unfold findKey
  rw [← hf]
  generalize s.filter (fun v => decide (v.key = key)) = F
  have h1 : sint.Z (getKey1Op key rev).base.limit = 1 := by
    simp only [getKey1Op, txn.rangeOpOf]; decide
  rw [h1]
  match F with
  | [] => simp
  | [a] => simp
  | a :: b :: F' => simp

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
variable [GooseExts] [GooseSemantics] [GooseInterp]
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

/-- **A response's key-value pointer is not `nil`**: the server's response predicate `txn.kvIs`
carries it (from the struct's typed points-to, `txn.kvAt_persist'`), and the store branches on
`KV == nil` (`notes/k8s-etcd3-plan.md`, "From the etcd client proof", request 3). -/
theorem kvIs_ne_null (l : Loc) (v : EtcdKv) : txn.kvIs (GF := GF) l v ⊢ ⌜l ≠ null⌝ := by
  unfold txn.kvIs
  iintro ⟨%ks, %vs, -, -, -, -, -, -, -, -, %Hn⟩
  ipureintro; exact Hn

/-- A key-value as a response's `KV` (`kvIs_ne_null`). -/
theorem kvOut_some (l : Loc) (v : EtcdKv) : txn.kvIs (GF := GF) l v ⊢ kvOut l (some v) := by
  iintro #H
  ihave %Hn := kvIs_ne_null l v $$ H
  simp only [kvOut]
  isplitr
  · ipureintro; exact Hn
  · iexact H

open client Iris.ProofMode in
/-- **What a linearizable range's reply says, at any revision** (k8s 7e-1, the Draft's §2.4;
`rangeReply_state_bnd` at `o.base.rev = 0`): the client's read update fired at a state `σ` (`□ Q
σ`) whose store at the revision read (`σ.readRev`, at most `σ.rev`) gives the reply's key-values
and count, whose revision is the reply's header revision, and which is below `2 ^ 63`. Without
`receiptBound`: the log's facts come from the reply itself. -/
theorem rangeReply_state_at (E : apply.AEnv GF) (γr : ReadNames) (c cid mid : w64) (o : OpFull)
    (F : mvcc.Log) (Q : KVState → IProp GF) (m : RangeRespM) (hs : o.base.serializable = false) :
    rangeReplyOk E γr c F o cid mid Q m ⊢
      ∃ σ : KVState, □ Q σ ∗
        ⌜txn.srvRangeOk o (σ.at (σ.readRev o.base.rev)).kvs m.kvs m.more ∧
          m.count = txn.srvCount o (σ.at (σ.readRev o.base.rev)).kvs true ∧
          m.hdr.revision = W64 (σ.rev : Int) ∧ σ.readRev o.base.rev ≤ σ.rev ∧ kvRevFits σ.rev ∧
          ∀ v ∈ σ.kvs, v.value.length ≤ etcdKeyMax⌝ := by
  iintro #H
  iunfold rangeReplyOk at H
  icases H with ⟨%l, -, %Hlk, %Hl, -, #HQ⟩
  simp only [hs, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨hlen, hlen', hrev, -, -, hle, hcount, hsel, -⟩ := Hl
  have h2 : sint.Z (W64 ((l.length : Int) - 1)) = (l.length : Int) - 1 := by word
  have hn : sint.nat (W64 ((l.length : Int) - 1)) = l.length - 1 := by unfold sint.nat; word
  have hRR : (kvStateOf l).readRev o.base.rev =
      sint.nat (mvcc.rangeRev m.hdr.revision o.base.rev) := by
    unfold KVState.readRev mvcc.rangeRev
    rw [kvStateOf_rev, hrev]
    by_cases h0 : sint.Z o.base.rev ≤ 0
    · simp only [h0, ↓reduceIte]; rw [hn]
    · simp only [h0, ↓reduceIte]
  have hRle : sint.nat (mvcc.rangeRev m.hdr.revision o.base.rev) ≤ l.length - 1 := by
    have hle' : sint.Z o.base.rev ≤ (l.length : Int) - 1 := by rw [hrev, h2] at hle; exact hle
    unfold mvcc.rangeRev; rw [hrev]
    by_cases h0 : sint.Z o.base.rev ≤ 0
    · simp only [h0, ↓reduceIte]; exact hn ▸ Nat.le_refl _
    · simp only [h0, ↓reduceIte]
      show (sint.Z o.base.rev).toNat ≤ l.length - 1
      omega
  iexists kvStateOf l
  iframe HQ
  ipureintro
  rw [hRR, kvStateOf_at_kvs l _ hRle]
  refine ⟨hsel, hcount, ?_, ?_, ?_, ?_⟩
  · rw [hrev, kvStateOf_rev]
    congr 1
    omega
  · rw [kvStateOf_rev]; exact hRle
  · unfold kvRevFits; rw [kvStateOf_rev]; omega
  · rw [kvStateOf_kvs]; exact mvcc.stateAfter_vals Hlk

open client Iris.ProofMode in
/-- **A linearizable range's future-revision error** (k8s 7e-1, the Draft's §2.5): the read's
update fired at a state below the revision asked. -/
theorem rangeErrReply_future (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (F : mvcc.Log)
    (o : OpFull) (Q : KVState → IProp GF) (hs : o.base.serializable = false) :
    rangeErrReply E γr c F o Q (rangeFutureAt o) ⊢
      ∃ σ : KVState, □ Q σ ∗ ⌜(σ.rev : Int) < sint.Z o.base.rev⌝ := by
  iintro #H
  iunfold rangeErrReply at H
  icases H with ⟨%l, %crev, -, -, -, -, %Hl, -, #HQ⟩
  simp only [hs, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨-, hlen, hlen', -, -, hfut⟩ := Hl
  unfold rangeFutureAt at hfut
  have h2 : sint.Z (W64 ((l.length : Int) - 1)) = (l.length : Int) - 1 := by word
  iexists kvStateOf l
  iframe HQ
  ipureintro
  rw [kvStateOf_rev]
  omega

/-- The one key-value of a list, if it has exactly one (`len(Kvs) == 1`). -/
def single {α : Type} : List α → Option α
  | [v] => some v
  | _ => none

end defs

end kubernetes

/-! ## The store's list vocabulary the client's `List`/`Get` are stated in (moved from the
store's `ListDefs.lean`, k8s 7e-1, the Draft's §3.2; namespace `k8s` kept) -/

namespace k8s

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts]

/-- **A list's scope** (`store.go:1081-1100`): recursive, the keys under the prepared prefix `kp`
(`kubernetes.Client.List`'s range `[kp, GetPrefixRangeEnd kp)`, `client.go:59-73`); not recursive,
the key `kp` itself (`kubernetes.Client.Get`, `client.go:47-57`). -/
def kInScope (kp : GoString) (recur : Bool) (k : GoString) : Bool :=
  if recur then decide (kp <+: k) else decide (k = kp)
/-- A list's limit as a count (`opts.Predicate.Limit`; none for `≤ 0`). -/
def limN (l : w64) : Nat := if 0 < sint.Z l then sint.nat l else 0

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A range error's future-revision soundness** (B4, decided by etcd-grove-81: the future half
only): an error whose description is `ErrFutureRev`'s (`errDesc`, D29) means the state the read's
update fired at is below the revision `o` asked, whatever revision `R` the update was made for
(7e-1's R1: the client makes its update for the prophesied response revision, never resolved on an
error, so `R` is unrelated to `σ.rev`). What `Client.List`/`Client.Get` give. -/
def rangeErrSound (o : w64) (Q : w64 → KVState → IProp GF) (err : GoInterface) : IProp GF :=
  iprop(□ (⌜go_etcd_io.etcd.cache.v3.errDesc err = go_etcd_io.etcd.cache.v3.futureRevDesc⌝ -∗
      ∃ (R : w64) (σ : KVState), □ Q R σ ∗ ⌜σ.rev < sint.nat o⌝))

instance rangeErrSound_persistent o Q err : Persistent (rangeErrSound (GF := GF) o Q err) := by
  unfold rangeErrSound; infer_instance

/-- **A page of a list read** (Draft §3.5) in the store `s`, from `start` with limit `l`: the first
`l` key-values of the scope from `start` (all for `l = 0`), and the count of the scope from
`start`. -/
def pageKvsL (s : KVStore) (kp : GoString) (recur : Bool) (start : GoString) (l : Nat) :
    List EtcdKv × Nat :=
  let sc := s.kvs.filter fun v => kInScope kp recur v.key && !decide (go.GoStringLt v.key start)
  (if l = 0 then sc else sc.take l, sc.length)

/-- In a key-sorted list (`KVStore.kvs_sorted`), the key-values of the key `k` are the one
`findKey` finds, or none. -/
theorem filter_key_eq_findKey (k : GoString) :
    ∀ (s : List EtcdKv), s.Pairwise etcdKvLess →
      s.filter (fun v => decide (v.key = k)) = (mvcc.findKey k s).toList
  | [], _ => by simp [mvcc.findKey]
  | w :: ws, hs => by
    rw [List.pairwise_cons] at hs
    rw [findKey_cons]
    by_cases hw : w.key = k
    · have hnil : ws.filter (fun v => decide (v.key = k)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro y hy hyk
        have hlt := hs.1 y hy
        unfold etcdKvLess at hlt
        simp only [decide_eq_true_eq] at hyk
        rw [hw, hyk] at hlt
        exact go.goStringLt_irrefl _ hlt
      simp [hw, hnil]
    · simp only [List.filter_cons, hw, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact filter_key_eq_findKey k ws hs.2

/-- **A non-recursive list's page** (`getList`'s `Get` branch, from the key itself with `Count` at
most one): the key's key-value in the store, or none. -/
theorem pageKvsL_key (s : KVStore) (kp : GoString) :
    pageKvsL s kp false kp 1 =
      ((mvcc.findKey kp s.kvs).toList, (mvcc.findKey kp s.kvs).toList.length) := by
  have hf : s.kvs.filter (fun v => kInScope kp false v.key && !decide (go.GoStringLt v.key kp)) =
      s.kvs.filter (fun v => decide (v.key = kp)) := by
    apply List.filter_congr
    intro v _
    by_cases hv : v.key = kp
    · simp [kInScope, hv, go.goStringLt_irrefl]
    · simp [kInScope, hv]
  unfold pageKvsL
  simp only [hf, filter_key_eq_findKey kp s.kvs (KVStore.kvs_sorted s)]
  cases mvcc.findKey kp s.kvs <;> rfl

/-- `getList`'s answer (Draft §3.5): a page of `σ`'s store at `σ.readRev rev`, the response's
revision `σ`'s. -/
def listRespIs (resp : go_etcd_io.etcd.client.v3.kubernetes.ListResponse) (σ : KVState)
    (kp : GoString) (recur : Bool) (rev lim : w64) (start : GoString) : IProp GF :=
  let pg := pageKvsL (σ.at (σ.readRev rev)) kp recur start (if recur then limN lim else 1)
  iprop(⌜resp.Revision' = W64 (σ.rev : Int) ∧ resp.Count' = W64 (pg.2 : Int)⌝ ∗
    ∃ ps, resp.Kvs' ↦* ps ∗ [∗list] q;kv ∈ ps;pg.1, txn.kvIs q kv)


end defs

end k8s

end EtcdGrove
end Perennial
