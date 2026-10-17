/-
**The client meets the server** (unit C1, 2026-10-14; over the generic gRPC specification since
2026-10-14): the client's `kv.Put` and `kv.Get` on a `KV` made by `NewKV` over a connection to a
gRPC server, end to end through the transport (grpc's `ClientConn.Invoke`, the client side of the
trust boundary: `Spec/google_golang_org/grpc/ClientConn__Invoke.lean`; since unit P3a the
interceptor chain over one attempt, the client's retry interceptor proved and assumed of the
connection, `isEtcdConn`, through `kvObjAt`: `client/v3/EtcdInvoke.lean`), and etcd's gRPC handlers
(`v3rpc/Results.lean`: `put_end_to_end`, `range_end_to_end`, `deleteRange_end_to_end`) meeting
etcd's specs of the KV methods, served at an address (`grpc.serve`, the server side), with the
trust base of each printed in the build log (`#print axioms`). Lean-first (no Rocq counterpart);
the design: `notes/decisions.md`, "A generic gRPC specification".

**etcd's specs of the KV methods** (`etcdPutSpec`, `etcdRangeSpec`, `etcdDeleteSpec`: predicate
transformers over the messages' models, `GrpcSpec`): a caller asking the request `o` gets a reply
message `m` with `putReplied` (`putReplyOk`, persistent, with the write's witness `appliedWit γr`
since unit C2a, and the token of the revision the put made, `revMinted`: the slice's unit V1,
carried since a reply's `Φ` is delivered once),
`rangeReplyOk` at the committed index `c` the caller knows of (`committedAtLeast γr c`,
persistent, `0` free), `deleteReplied` (`deleteReplyOk` and the token).

**The handlers** (`etcd_putHandlerOk`, `etcd_rangeHandlerOk`, `etcd_deleteHandlerOk`:
`grpcHandlerOk`): `kvServer.Put`/`Range`/`DeleteRange` at the server's `*kvServer` `p`, with the
per-run slot `etcdRunSlot`
(the reader slots of `s.leadTimeMu`, the store, the logger and the read loop: every run gives
them back) and the context the runtime made; the id credit a run takes is minted from the
server's id budget `□ |==> idCred ρ.ids 1` (`srvStarted`'s, the server's own idealization: the
generator's `2 ^ 48 - 1` ids are assumed not to wrap).

**As grpc runs them** (unit P3b; `etcd_putMethodOk`, ...: `grpcMethodOk`): the generated
`_KV_Put_Handler` (`_KV_Range_Handler`, `_KV_DeleteRange_Handler`, proved) on the `*quotaKVServer`
`q` that `RegisterKVServer` is given (`NewQuotaKVServer(s)`: its `Put` checks the quota first,
`quotaKVServer.Put` proved; its `Range`/`DeleteRange` are `p`'s, promoted), under the server's
chain of transparent interceptors (`srvInterceptorsOk`: `newLogUnaryInterceptor`'s and
`newUnaryInterceptor`'s, proved; grpc-prometheus's, assumed); a run's slot as the runtime holds it
is `etcdGrpcSlot` (`etcdRunSlot`, a reader slot of `leadTimeMu` for the quota's alarm, the log
interceptor's of `lgMu`).

**What the client learns** (`putReplyOk`, `rangeReplyOk`, `deleteReplyOk`, persistent): for a
`Put`, the apply thread's application of the put the server decoded at the log the entry met, the
reply's header revision that log's length, its ids the cluster's and member's, its previous
key-value the state's if asked, mvcc's certificate of the log after (`put_end_to_end`'s
`putAppliedOk`, carried to the reply); for a `Get`, the txn package's range at a certified log of
at least two revisions (`range_end_to_end`'s `rangeAnsOk`), read after the read index unless
serializable (`readLogOk γr c log`), the reply's key-values, `More` and `Count` the server's
selection; for a `DeleteRange`, the application of the delete the proposed data decode to.

The results:
* **`etcd_kv_served`** (the server side): the gRPC server at `addr` built with etcd's chain of
  interceptors and the KV service registered on the quota wrapper (`grpcServerAt`), that hands
  the runtime `N` run slots, registers etcd's three specs at `addr` (`isGrpcRpc`).
* **`client_put_end_to_end`**: `kv.Put(ctx, key, val)` with no options on a connection to `addr`
  whose `Put` is registered with `etcdPutSpec`: `nil` and a reply holding a message `m`
  (`putRespMsg`) with `putReplied` for the put `key ↦ val` (`putReplyOk` and the revision's
  token `revMinted`, carried by the reply's `Φ` since the merge with the slice's unit V1); or an
  error.
* **`client_get_end_to_end`**: `kv.Get(ctx, key)` with no options, `Range` registered with
  `etcdRangeSpec`: `nil` and a reply holding a message `m` (`rangeRespMsg`) with `rangeReplyOk`
  for the get of `key`; or an error.
* **`client_get_after_put`** (unit C2a, 2026-10-14; one server): after a `Put` of `key ↦ val`
  that returned `nil` (its reply's `putReplyOk E γr`, `client_put_end_to_end`'s `putReplied` with
  its token dropped, `putReplied_ok`; with the witness `appliedWit γr` of the
  log after: applied through an index `i` of the committed log), `kv.Get(ctx', key)` with `Range`
  registered at the same read names: `nil` and a reply `m` that reads the put (`getAfterPutOk`:
  at a certified log extending the put's log after, its revision at least the put's; and, if no
  later revision touched `key`, exactly the put's key-value, `get_after_put_kvs`); or an error.
  The `Get` asks the read index at `i` (`committedAtLeast γr i`), so `readLogOk` gives a log
  extending the log applied through some index `≥ i`, which extends the put's (`appliedMono`).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.Link
public import Proof.go_etcd_io.etcd.client.v3.ServerWatcher
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Results
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.QuotaLemmas

@[expose] public section

set_option pp.fullNames true
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

/-! ## A get after a put, purely (unit C2a, 2026-10-14) -/

section pure
open mvcc

/-- The get of one key with no options (what `kv.Get(ctx, key)` sends, `client_get_end_to_end`). -/
abbrev getKeyOp (key : GoString) : OpFull :=
  txn.rangeOpOf key [] (W64 0) (W64 0) (W32 0) (W32 0) false false false (W64 0) (W64 0) (W64 0)
    (W64 0)

/-- The put of `key ↦ val` with no options (what `kv.Put(ctx, key, val)` sends). -/
abbrev putKeyOp (key val : GoString) : OpFull :=
  txn.putOpOf key val (W64 0) false false false

/-- **The get of one key with no options selects the key's key-value** (pure): the server's
answer is the state's key-values of that key, no `More`. -/
theorem srvRangeOk_getKey (key : GoString) (s kvs : List EtcdKv) (more : Bool)
    (h : txn.srvRangeOk (getKeyOp key) s kvs more) :
    kvs = s.filter (fun v => decide (v.key = key)) ∧ more = false := by
  obtain ⟨L, hsort, hmore, hkvs⟩ := h
  have hpre : txn.srvPre (getKeyOp key) s = s.filter (fun v => decide (v.key = key)) := by
    have hr : txn.kvRead false = id := by funext v; simp [txn.kvRead]
    unfold txn.srvPre
    simp [txn.rangeLimitOf, txn.hasRevFilters, mvcc.limitOf, mvcc.takeLimit, txn.fastKeysOnly,
      rangeIn, inRange, hr]
    apply List.filter_congr
    intro v _
    simp [kvFilterOk]
  have hord : (getKeyOp key).effSortOrder = W64 0 := by
    simp [OpFull.effSortOrder]
  have hL : L = txn.srvPre (getKeyOp key) s := by
    obtain ⟨-, -, -, h4⟩ := hsort
    exact h4 (by rw [hord]; decide) (by rw [hord]; decide)
  have hm : txn.srvMore (getKeyOp key) L = false := by
    simp [txn.srvMore]
  refine ⟨?_, by rw [hmore, hm]⟩
  rw [hkvs]
  unfold txn.srvTrunc
  rw [hm, hL, hpre]
  have hid : txn.respKv (getKeyOp key) = id := by funext v; simp [txn.respKv]
  simp [hid]

/-- In a state sorted by key, the key-values of a key are the one its key finds. -/
theorem filter_key_of_findKey (k : GoString) :
    ∀ (s : List EtcdKv), s.Pairwise etcdKvLess → ∀ kv, findKey k s = some kv →
      s.filter (fun v => decide (v.key = k)) = [kv]
  | [], _, kv, h => by simp [findKey] at h
  | w :: ws, hs, kv, h => by
    rw [List.pairwise_cons] at hs
    rw [findKey_cons] at h
    by_cases hw : w.key = k
    · rw [ite_eq_left hw] at h
      cases h
      have hnil : ws.filter (fun v => decide (v.key = k)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro y hy
        have hlt := hs.1 y hy
        unfold etcdKvLess at hlt
        intro hyk
        simp only [decide_eq_true_eq] at hyk
        rw [hw, hyk] at hlt
        exact goStringLt_irrefl _ hlt
      simp [hw, hnil]
    · rw [ite_eq_right hw] at h
      simp only [List.filter_cons, hw, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact filter_key_of_findKey k ws hs.2 kv h

/-- In a state sorted by key, a key it does not find has no key-value. -/
theorem filter_key_of_findKey_none (k : GoString) :
    ∀ (s : List EtcdKv), findKey k s = none → s.filter (fun v => decide (v.key = k)) = []
  | [], _ => rfl
  | w :: ws, h => by
    rw [findKey_cons] at h
    by_cases hw : w.key = k
    · rw [ite_eq_left hw] at h; cases h
    · rw [ite_eq_right hw] at h
      simp only [List.filter_cons, hw, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact filter_key_of_findKey_none k ws h

/-- **The get of one key returns the key's value in the model** (pure; 2026-10-14, unit T1): its
first key-value's value is `kvVal` of the log read. -/
theorem getKey_value (key : GoString) (l : Log) (kvs : List EtcdKv) (more : Bool)
    (h : txn.srvRangeOk (getKeyOp key) (stateAfter l) kvs more) :
    kvs.head?.map EtcdKv.value = kvVal l key := by
  obtain ⟨hkvs, -⟩ := srvRangeOk_getKey key _ kvs more h
  unfold kvVal
  cases hf : findKey key (stateAfter l) with
  | none => rw [hkvs, filter_key_of_findKey_none key _ hf]; rfl
  | some kv => rw [hkvs, filter_key_of_findKey key _ (stateAfter_sorted l) kv hf]; rfl

/-- A key the changes do not touch keeps its key-value. -/
theorem findKey_applyChanges_untouched (k : GoString) (r : w64) :
    ∀ (cs : List Change) (s : List EtcdKv), s.Pairwise etcdKvLess → (∀ c ∈ cs, c.key ≠ k) →
      findKey k (applyChanges r s cs) = findKey k s
  | [], _, _, _ => rfl
  | c :: cs, s, hs, hc => by
    have hc0 := hc c (List.mem_cons_self ..)
    have hrest : ∀ c' ∈ cs, c'.key ≠ k := fun c' h => hc c' (List.mem_cons_of_mem _ h)
    show findKey k (applyChanges r (applyChange r s c) cs) = findKey k s
    rw [findKey_applyChanges_untouched k r cs _ (applyChange_sorted hs r c) hrest]
    cases c with
    | put k' v l =>
      exact findKey_putKv_other hs r k k' v l hc0
    | del k' =>
      show findKey k (s.filter fun x => !decide (x.key = k')) = findKey k s
      rw [findKey_filter_ne]
      simp only [Change.key] at hc0
      rw [ite_eq_right hc0]

/-- A key no later revision touches keeps its key-value. -/
theorem findKey_stateAfter_untouched (k : GoString) :
    ∀ (rest L : Log), (∀ cs ∈ rest, ∀ c ∈ cs, c.key ≠ k) →
      findKey k (stateAfter (L ++ rest)) = findKey k (stateAfter L)
  | [], L, _ => by simp
  | cs :: rest, L, h => by
    have h1 := findKey_stateAfter_untouched k rest (L ++ [cs])
      (fun cs' hcs' => h cs' (List.mem_cons_of_mem _ hcs'))
    rw [show L ++ cs :: rest = (L ++ [cs]) ++ rest by simp, h1, stateAfter_append,
      findKey_applyChanges_untouched k _ cs _ (stateAfter_sorted _) (h cs (List.mem_cons_self ..))]

/-- The put of `key ↦ val` finds the value it wrote. -/
theorem findKey_putKv_value (s : List EtcdKv) (hs : s.Pairwise etcdKvLess) (r : w64)
    (k v : GoString) (l : w64) :
    ∃ nv, findKey k (putKv r k v l s) = some nv ∧ nv.key = k ∧ nv.value = v := by
  unfold putKv
  simp only
  rw [findKey_btInsert _ s hs]
  cases h : s.find? (fun v => decide (v.key = k)) with
  | none =>
    refine ⟨{ key := k, createRev := r, modRev := r, version := W64 1, value := v, lease := l },
      ?_, rfl, rfl⟩
    simp
  | some kv =>
    have hk : kv.key = k := by simpa using List.find?_some h
    refine ⟨{ kv with modRev := r, version := kv.version + W64 1, value := v, lease := l }, ?_,
      hk, rfl⟩
    simp [hk]


/-- **A put applied with no error through any chain wrote the client's put change** (pure). -/
theorem chainStep_put_applied (op : OpFull) (rq : apply.IRRModel)
    (hk : apply.dispatchKind rq = .put) (hop : rq.put = some op) (log l : Log) :
    ∀ c : apply.Chain, apply.chainStep apply.backendStep c rq log (.applied l false) →
      l = log ++ [[txn.putChangeOf op (findKey op.key (stateAfter log))]]
  | .backend, h => by
    simp only [apply.chainStep, apply.backendStep, hk] at h
    obtain ⟨op', hop', h⟩ := h
    rw [hop] at hop'; cases hop'
    rcases h with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, h⟩
    · cases h
    · cases h
    · cases h; rfl
  | .corrupt c, h => by
    simp only [apply.chainStep, hk, apply.corruptRejects, ↓reduceIte] at h
    cases h
  | .capped c, h => by
    simp only [apply.chainStep, hk, apply.cappedRejects, ↓reduceIte] at h
    cases h
  | .auth _ c, h => by
    unfold apply.chainStep at h
    split at h
    · rcases h with ⟨-, h⟩ | h
      · cases h
      · exact chainStep_put_applied op rq hk hop log l c h
    · exact chainStep_put_applied op rq hk hop log l c h
  | .quota c, h => by
    unfold apply.chainStep at h
    exact chainStep_put_applied op rq hk hop log l c h

/-- **What a successful put applied** (pure; chain-agnostic, unlike `v3rpc.put_end_to_end_model`):
the log after is the log the entry met with the client's put change. -/
theorem put_applied_log (o : OpFull) (hm : apply.HeaderModel) (x x' : apply.ApplyKV)
    (l : Log) (skip : Bool)
    (h : apply.applyStep (apply.withHeader (irrPut o) hm) true x x'
      (.dispatched (.applied l false) skip)) :
    x'.log = x.log ++ [[txn.putChangeOf o (findKey o.key (stateAfter x.log))]] := by
  obtain ⟨-, hd, hl, -⟩ := h
  have hk : apply.dispatchKind (apply.withHeader (irrPut o) hm) = .put := by
    simp [apply.dispatchKind, apply.withHeader, irrPut, apply.irrEmpty]
  have hop : (apply.withHeader (irrPut o) hm).put = some o := by
    simp [apply.withHeader, irrPut, apply.irrEmpty]
  unfold apply.dispatchStep at hd
  rw [hk] at hd
  simp only [apply.preV3Kind, apply.storeKind, Bool.false_eq_true, false_or, ↓reduceIte] at hd
  rw [hl]
  exact chainStep_put_applied o _ hk hop x.log l x.chain hd

/-- **A get after a put reads the put's value unless a later revision touched the key** (pure; the
corollary of `client_get_after_put`): the put of `key ↦ val` at the log `x.log` (`put_applied_log`:
`x'.log` is `x.log` with the put's change) and a get of `key` with no options at a log `l` extending
`x'.log`, with no later revision of `l` touching `key`: the get's key-values are exactly the put's
key-value (key `key`, value `val`), and no `More`. -/
theorem get_after_put_kvs (key val : GoString) (x x' : apply.ApplyKV) (l : Log)
    (kvs : List EtcdKv) (more : Bool)
    (hx' : x'.log = x.log ++ [[txn.putChangeOf (putKeyOp key val)
      (findKey key (stateAfter x.log))]])
    (hpre : x'.log <+: l) (hget : txn.srvRangeOk (getKeyOp key) (stateAfter l) kvs more)
    (hno : ∀ cs ∈ l.drop x'.log.length, ∀ c ∈ cs, c.key ≠ key) :
    ∃ kv, kvs = [kv] ∧ kv.key = key ∧ kv.value = val ∧ more = false := by
  obtain ⟨rest, rfl⟩ := hpre
  have hrest : List.drop x'.log.length (x'.log ++ rest) = rest := by simp
  rw [hrest] at hno
  obtain ⟨hkvs, hmore⟩ := srvRangeOk_getKey key _ kvs more hget
  have hput : findKey key (stateAfter x'.log) =
      findKey key (putKv (W64 x.log.length) key val (W64 0) (stateAfter x.log)) := by
    rw [hx', stateAfter_append]
    simp [applyChanges, applyChange, txn.putChangeOf, txn.putValOf, txn.putLeaseOf, putKeyOp,
      txn.putOpOf]
  obtain ⟨nv, hnv, hk, hv⟩ := findKey_putKv_value _ (stateAfter_sorted x.log) (W64 x.log.length)
    key val (W64 0)
  rw [hnv] at hput
  have hf := filter_key_of_findKey key _ (stateAfter_sorted (x'.log ++ rest)) nv
    (by rw [findKey_stateAfter_untouched key rest x'.log hno, hput])
  exact ⟨nv, by rw [hkvs, hf], hk, hv, hmore⟩

end pure

/-! ## Plain operations -/

/-- An operation that is not a nested transaction (what the client's builder makes: `txnOpOf`
never gives one). -/
def TxnOp.plain : TxnOp → Prop
  | .txn _ _ _ => False
  | _ => True

/-- A transaction of plain operations, in both branches. -/
def TxnModel.plain (t : TxnModel) : Prop :=
  (∀ op ∈ t.thenOps, TxnOp.plain op) ∧ ∀ op ∈ t.elseOps, TxnOp.plain op

theorem opWire_plain (op : TxnOp) (h : TxnOp.plain op) : TxnOp.plain (opWire op) := by
  cases op <;> simp_all [TxnOp.plain, opWire]

theorem txnOpOf_plain (o : OpFull) (op : TxnOp) (h : txnOpOf o = some op) : TxnOp.plain op := by
  unfold txnOpOf at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq] at h; subst h; trivial)
    | cases h

/-- A delete's count of plain operations: `delCountT` and `v3rpc.delCount` agree. -/
theorem delCount_toTxnOps : ∀ (us : List v3rpc.ReqOp) (ops : List TxnOp),
    v3rpc.ReqOp.toTxnOps us = some ops → (∀ op ∈ ops, TxnOp.plain op) → v3rpc.delCount us = delCountT ops
  | [], ops, h, _ => by
    simp [v3rpc.ReqOp.toTxnOps] at h; subst h; simp [v3rpc.delCount, delCountT]
  | u :: us, ops, h, hp => by
    simp only [v3rpc.ReqOp.toTxnOps] at h
    split at h
    · rename_i t ts h1 h2
      simp only [Option.some.injEq] at h
      subst h
      have ih := delCount_toTxnOps us ts h2 (fun op hm => hp op (List.mem_cons_of_mem _ hm))
      have ht := hp t (List.mem_cons_self ..)
      cases u with
      | range o => simp [v3rpc.ReqOp.toTxnOp] at h1; subst h1; simp [v3rpc.delCount, delCountT, ih]
      | put o =>
        simp [v3rpc.ReqOp.toTxnOp] at h1; subst h1
        unfold txn.putTxnOp
        split <;> (try split) <;> simp [v3rpc.delCount, delCountT, ih]
      | delete o => simp [v3rpc.ReqOp.toTxnOp] at h1; subst h1; simp [v3rpc.delCount, delCountT, ih]
      | txn cs ts' es' =>
        simp only [v3rpc.ReqOp.toTxnOp] at h1
        split at h1 <;> simp at h1
        subst h1; exact ht.elim
      | empty => simp [v3rpc.ReqOp.toTxnOp] at h1
    · cases h

section bridge
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A plain operation of the server's copy is the handler's request operation**: the txn
package's `requestOpIs` of a plain operation is `v3rpc.reqOpIs` of a request operation whose
model it is. -/
theorem reqOp_of_requestOp (p : Loc) (op : TxnOp) (hp : TxnOp.plain op) :
    txn.requestOpIs (GF := GF) p op ⊢ ∃ u : v3rpc.ReqOp, v3rpc.reqOpIs p u ∗ ⌜v3rpc.ReqOp.toTxnOp u = some op⌝ := by
  cases op with
  | txn cs ts es => exact hp.elim
  | get o =>
    iintro #H
    iunfold txn.requestOpIs at H
    icases H with ⟨%Hn, %u, %w, %r, %o', #Hu, (⟨%Hx, #Hw, #Hr⟩ | ⟨%Hx, -⟩ | ⟨%Hx, -⟩)⟩
    · obtain ⟨rfl, Ho⟩ := Hx
      cases Ho
      iexists (v3rpc.ReqOp.range o)
      isplitl
      · unfold v3rpc.reqOpIs; imodintro; isplitl; · ipureintro; exact Hn
        iexists w, r; iframe #
      · ipureintro; rfl
    · exfalso
      have := Hx.2
      unfold txn.putTxnOp at this; split at this <;> (try split at this) <;> simp at this
    · cases Hx.2
  | delete o =>
    iintro #H
    iunfold txn.requestOpIs at H
    icases H with ⟨%Hn, %u, %w, %r, %o', #Hu, (⟨%Hx, -⟩ | ⟨%Hx, -⟩ | ⟨%Hx, #Hw, #Hr⟩)⟩
    · cases Hx.2
    · exfalso
      have := Hx.2
      unfold txn.putTxnOp at this; split at this <;> (try split at this) <;> simp at this
    · obtain ⟨rfl, Ho⟩ := Hx
      cases Ho
      iexists (v3rpc.ReqOp.delete o)
      isplitl
      · unfold v3rpc.reqOpIs; imodintro; isplitl; · ipureintro; exact Hn
        iexists w, r; iframe #
      · ipureintro; rfl
  | put k v l =>
    iintro #H
    iunfold txn.requestOpIs at H
    icases H with ⟨%Hn, %u, %w, %r, %o', #Hu, (⟨%Hx, -⟩ | ⟨%Hx, #Hw, #Hr⟩ | ⟨%Hx, -⟩)⟩
    · cases Hx.2
    · obtain ⟨rfl, Ho⟩ := Hx
      iexists (v3rpc.ReqOp.put o')
      isplitl
      · unfold v3rpc.reqOpIs; imodintro; isplitl; · ipureintro; exact Hn
        iexists w, r; iframe #
      · ipureintro; simp [v3rpc.ReqOp.toTxnOp, Ho]
    · cases Hx.2
  | putKeep k l =>
    iintro #H
    iunfold txn.requestOpIs at H
    icases H with ⟨%Hn, %u, %w, %r, %o', #Hu, (⟨%Hx, -⟩ | ⟨%Hx, #Hw, #Hr⟩ | ⟨%Hx, -⟩)⟩
    · cases Hx.2
    · obtain ⟨rfl, Ho⟩ := Hx
      iexists (v3rpc.ReqOp.put o')
      isplitl
      · unfold v3rpc.reqOpIs; imodintro; isplitl; · ipureintro; exact Hn
        iexists w, r; iframe #
      · ipureintro; simp [v3rpc.ReqOp.toTxnOp, Ho]
    · cases Hx.2
  | putIgnVal k l =>
    iintro #H
    iunfold txn.requestOpIs at H
    icases H with ⟨%Hn, %u, %w, %r, %o', #Hu, (⟨%Hx, -⟩ | ⟨%Hx, #Hw, #Hr⟩ | ⟨%Hx, -⟩)⟩
    · cases Hx.2
    · obtain ⟨rfl, Ho⟩ := Hx
      iexists (v3rpc.ReqOp.put o')
      isplitl
      · unfold v3rpc.reqOpIs; imodintro; isplitl; · ipureintro; exact Hn
        iexists w, r; iframe #
      · ipureintro; simp [v3rpc.ReqOp.toTxnOp, Ho]
    · cases Hx.2

/-- **The plain operations of the server's copy are the handler's request operations** (in
order). -/
theorem reqOps_of_requestOps : ∀ (ps : List Loc) (ops : List TxnOp),
    (∀ op ∈ ops, TxnOp.plain op) →
    txn.requestOpsIs (GF := GF) ps ops ⊢
      ∃ us : List v3rpc.ReqOp, v3rpc.reqOpsIs ps us ∗ ⌜v3rpc.ReqOp.toTxnOps us = some ops⌝
  | [], [], _ => by
    iintro -
    iexists []
    unfold v3rpc.reqOpsIs
    isplitl; · itrivial
    ipureintro; rfl
  | p :: ps, op :: ops, hp => by
    iintro H
    iunfold txn.requestOpsIs at H
    icases H with ⟨H1, H2⟩
    ihave ⟨%u, H1, %Hu⟩ := reqOp_of_requestOp p op (hp op (List.mem_cons_self ..)) $$ H1
    ihave ⟨%us, H2, %Hus⟩ := reqOps_of_requestOps ps ops
      (fun o hm => hp o (List.mem_cons_of_mem _ hm)) $$ H2
    iexists u :: us
    rw [v3rpc.reqOpsIs.eq_2]
    iframe H1 H2
    ipureintro
    simp [v3rpc.ReqOp.toTxnOps, Hu, Hus]
  | [], _ :: _, _ => by iintro H; iunfold txn.requestOpsIs at H; iexfalso; iexact H
  | _ :: _, [], _ => by iintro H; iunfold txn.requestOpsIs at H; iexfalso; iexact H

/-- A request operation that is not a nested transaction. -/
def reqNotTxn : v3rpc.ReqOp → Prop
  | .txn _ _ _ => False
  | _ => True

theorem reqNotTxn_of_toTxnOps : ∀ (us : List v3rpc.ReqOp) (ops : List TxnOp),
    v3rpc.ReqOp.toTxnOps us = some ops → (∀ op ∈ ops, TxnOp.plain op) → ∀ u ∈ us, reqNotTxn u
  | [], _, _, _ => by simp
  | u :: us, ops, h, hp => by
    simp only [v3rpc.ReqOp.toTxnOps] at h
    split at h
    · rename_i t ts h1 h2
      simp only [Option.some.injEq] at h
      subst h
      have ih := reqNotTxn_of_toTxnOps us ts h2 (fun op hm => hp op (List.mem_cons_of_mem _ hm))
      intro u' hu'
      rcases List.mem_cons.mp hu' with rfl | hm
      · have ht := hp t (List.mem_cons_self ..)
        cases u' with
        | txn cs ts' es' =>
          simp only [v3rpc.ReqOp.toTxnOp] at h1
          split at h1 <;> simp at h1
          subst h1; exact ht.elim
        | _ => trivial
      · exact ih u' hm
    · cases h

/-- The deletes' range ends of the operations `ps` are `nil` or not empty (what `txnWireOk` says
of each branch). -/
def delWireAt (ps : List Loc) : IProp GF :=
  iprop(□ ∀ (i : Nat) (p w d : Loc) (esl : GoSlice), ⌜ps[i]? = some p⌝ -∗
      structFieldRef etcdserverpb.RequestOp go!"Request" p ↦□
        (interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestDeleteRange.ty) #w :
          GoInterface) -∗
      structFieldRef etcdserverpb.RequestOp_RequestDeleteRange go!"RequestDeleteRange" w ↦□ d -∗
      structFieldRef etcdserverpb.DeleteRangeRequest go!"RangeEnd" d ↦□ esl -∗
      ⌜esl = slice.nil ∨ esl.len ≠ W64 0⌝)

instance delWireAt_persistent (ps : List Loc) : Persistent (delWireAt (GF := GF) ps) := by
  unfold delWireAt; infer_instance

theorem reqOpsWire_of_delWireAt : ∀ (ps : List Loc) (us : List v3rpc.ReqOp),
    (∀ u ∈ us, reqNotTxn u) → delWireAt (GF := GF) ps ⊢ v3rpc.reqOpsWire ps us
  | [], [], _ => by iintro -; unfold v3rpc.reqOpsWire; itrivial
  | [], _ :: _, _ => by iintro -; unfold v3rpc.reqOpsWire; itrivial
  | _ :: _, [], _ => by iintro -; unfold v3rpc.reqOpsWire; itrivial
  | p :: ps, u :: us, hu => by
    iintro #H
    iunfold delWireAt at H
    have ih := reqOpsWire_of_delWireAt ps us (fun u' hm => hu u' (List.mem_cons_of_mem _ hm))
    rw [v3rpc.reqOpsWire.eq_2]
    isplitl
    · cases u with
      | delete o =>
        unfold v3rpc.reqOpWire
        iintro !> %w %d %esl #H1 #H2 #H3
        iapply H $$ %0 %p %w %d %esl %rfl H1 H2 H3
      | txn cs ts es => exact (hu _ (List.mem_cons_self ..)).elim
      | range o => unfold v3rpc.reqOpWire; itrivial
      | put o => unfold v3rpc.reqOpWire; itrivial
      | empty => unfold v3rpc.reqOpWire; itrivial
    · iapply ih
      unfold delWireAt
      iintro !> %i %q %w %d %esl %Hi #H1 #H2 #H3
      iapply H $$ %(i + 1) %q %w %d %esl %Hi H1 H2 H3

/-- **The transport's request is the gRPC handler's** (see the file header): the server's copy of
a transaction `t` of plain operations, as decoded (`txnRequestIs`, `txnWireOk`), is the handler's
request `txnReqIs r t.cmps ts es` with its wire facts, whose model is `t`. -/
theorem txnReq_of_requestIs (r : Loc) (t : TxnModel) (hp : TxnModel.plain t) :
    txn.txnRequestIs (GF := GF) r t ∗ txnWireOk r t ⊢
      ∃ ts es : List v3rpc.ReqOp, v3rpc.txnReqIs r t.cmps ts es ∗ v3rpc.txnReqWire r ts es ∗
        ⌜v3rpc.txnModelOf t.cmps ts es = some t⌝ := by
  iintro ⟨#Hreq, #Hw⟩
  iunfold txn.txnRequestIs at Hreq
  icases Hreq with ⟨%Hrn, Hreq⟩
  iunfold txn.txnFieldsIs at Hreq
  icases Hreq with ⟨%csl, %ssl, %fsl, %cps, %sps, %fps, #Hc, #Hcs, #Hcm, #Hs, #Hss, #Hsm,
    #Hf, #Hfs, #Hfm⟩
  ihave ⟨%ts, #Hts, %Hts'⟩ := reqOps_of_requestOps sps t.thenOps hp.1 $$ Hsm
  ihave ⟨%es, #Hes, %Hes'⟩ := reqOps_of_requestOps fps t.elseOps hp.2 $$ Hfm
  iexists ts, es
  iunfold txnWireOk at Hw
  icases Hw with ⟨%Hcnt, #Hw⟩
  isplitl
  · unfold v3rpc.txnReqIs
    isplitl; · ipureintro; exact Hrn
    iexists csl, ssl, fsl, cps, sps, fps
    iframe #
  isplitl
  · unfold v3rpc.txnReqWire
    isplitl
    · ipureintro
      rw [delCount_toTxnOps ts _ Hts' hp.1, delCount_toTxnOps es _ Hes' hp.2]
      exact Hcnt
    iintro !> %ssl' %fsl' %sps' %fps' #Hs' #Hss' #Hf' #Hfs'
    isplitl
    · iapply reqOpsWire_of_delWireAt sps' ts (reqNotTxn_of_toTxnOps ts _ Hts' hp.1)
      unfold delWireAt
      iintro !> %i %q %w %d %esl %Hi #H1 #H2 #H3
      iapply Hw $$ %ssl' %sps' %i %q %w %d %esl [] Hss' %Hi H1 H2 H3
      ileft; iexact Hs'
    · iapply reqOpsWire_of_delWireAt fps' es (reqNotTxn_of_toTxnOps es _ Hes' hp.2)
      unfold delWireAt
      iintro !> %i %q %w %d %esl %Hi #H1 #H2 #H3
      iapply Hw $$ %fsl' %fps' %i %q %w %d %esl [] Hfs' %Hi H1 H2 H3
      iright; iexact Hf'
  · ipureintro
    simp [v3rpc.txnModelOf, Hts', Hes']

end bridge

/-! ## The response's model -/

mutual
/-- **A response message of an operation answers it** (`skip`: ranges header-only): the
message `m` of the server's response of the operation `op` with result `res` (the txn package's
`responseOpIs`): a get's count and key-values (as the range model's: `rangeKvsOk`, the leases
zeroed by a fast keys-only read), or nothing if header-only; a put's; a delete's count; a nested
transaction's verdict and its branch's responses. The inner headers' revisions and a put's or
delete's previous key-values are unconstrained (the server's `responseOpIs` leaves them so). -/
def opRespRel (skip : Bool) : TxnOp → TxnOpResult → OpRespM → Prop
  | .get o, .range sel n, .range _ kvs more count =>
      if skip then kvs = [] ∧ more = false ∧ count = W64 0
      else count = W64 (n : Int) ∧
        ∃ kvs', rangeKvsOk o sel kvs' ∧ kvs = kvs'.map (txn.leaseZ (txn.fastKeysOnly o))
  | .put .., .put, .put _ _ => True
  | .putKeep .., .put, .put _ _ => True
  | .putIgnVal .., .put, .put _ _ => True
  | .delete _, .delete n, .delete _ d _ => d = W64 (n : Int)
  | .txn _ ts es, .txn ok rs, .txn _ ok' ms =>
      ok' = ok ∧ (if ok then opRespsRel skip ts rs ms else opRespsRel skip es rs ms)
  | _, _, _ => False

/-- `opRespRel` of each operation, in order. -/
def opRespsRel (skip : Bool) : List TxnOp → List TxnOpResult → List OpRespM → Prop
  | [], [], [] => True
  | op :: ops, res :: rs, m :: ms => opRespRel skip op res m ∧ opRespsRel skip ops rs ms
  | _, _, _ => False
end

section resp
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

mutual
/-- **The server's response of an operation is a response message that answers it**
(`opRespRel`). -/
theorem opResp_of_responseOp (skip : Bool) (p : Loc) (op : TxnOp) (res : TxnOpResult) :
    txn.responseOpIs (GF := GF) skip p op res ⊢
      ∃ m : OpRespM, opRespMsg p m ∗ ⌜opRespRel skip op res m⌝ := by
  match op, res with
  | .txn cs ts es, .txn ok rs =>
    rw [txn.responseOpIs.eq_1]
    iintro #H
    icases H with ⟨%Hn, %w, %r, #Hu0, #Hw, %Hrn, %h, %sl, %ps, #Hh, %Hhn, #Hrev, #Hok, #Hsl, #Hps,
      Hrs⟩
    cases ok with
    | true =>
      ihave ⟨%ms, #Hms, %Hrel⟩ := opResps_of_responseOps skip ps ts rs $$ Hrs
      iexists (OpRespM.txn (W64 0) true ms)
      isplitl
      · unfold opRespMsg
        isplitl; · ipureintro; exact Hn
        iexists w, r, h, sl, ps
        iframe #
        isplitl; · ipureintro; exact Hrn
        ipureintro; exact Hhn
      · ipureintro; simp only [opRespRel]; exact ⟨trivial, by simpa using Hrel⟩
    | false =>
      ihave ⟨%ms, #Hms, %Hrel⟩ := opResps_of_responseOps skip ps es rs $$ Hrs
      iexists (OpRespM.txn (W64 0) false ms)
      isplitl
      · unfold opRespMsg
        isplitl; · ipureintro; exact Hn
        iexists w, r, h, sl, ps
        iframe #
        isplitl; · ipureintro; exact Hrn
        ipureintro; exact Hhn
      · ipureintro; simp only [opRespRel]; exact ⟨trivial, by simpa using Hrel⟩
  | .txn cs ts es, .range .. | .txn cs ts es, .put | .txn cs ts es, .delete .. =>
    simp only [txn.responseOpIs]
    iintro #H
    icases H with ⟨%Hn, %u, %w, %r, -, Hf⟩
    iexfalso; iexact Hf
  | .get o, .range sel n =>
    cases skip with
    | true =>
      simp only [txn.responseOpIs, ↓reduceIte]
      iintro #H
      icases H with ⟨%Hn, %u, %w, %r, #Hu0, %Hu, #Hw, %rev, Hr⟩
      subst Hu
      iexists (OpRespM.range rev [] false (W64 0))
      isplitl
      · unfold opRespMsg
        isplitl; · ipureintro; exact Hn
        iexists w, r
        iframe #
      · ipureintro; simp [opRespRel]
    | false =>
      simp only [txn.responseOpIs, ↓reduceIte, Bool.false_eq_true]
      iintro #H
      icases H with ⟨%Hn, %u, %w, %r, #Hu0, %Hu, #Hw, %rev, Hr⟩
      subst Hu
      icases Hr with ⟨%kvs, %more, #Hrr, %Hk⟩
      iexists (OpRespM.range rev kvs more (W64 (n : Int)))
      isplitl
      · unfold opRespMsg
        isplitl; · ipureintro; exact Hn
        iexists w, r
        iframe #
      · ipureintro; simp only [opRespRel]; exact ⟨by simp, Hk⟩
  | .delete o, .delete n =>
    simp only [txn.responseOpIs]
    iintro #H
    icases H with ⟨%Hn, %u, %w, %r, #Hu0, %Hu, #Hw, %rev, %prevs, #Hrr⟩
    subst Hu
    iunfold txn.deleteRangeResponseIs at Hrr
    icases Hrr with ⟨%Hrn, %h, %sl, %ps, #Hh, %Hhn, #Hrev, #Hd, #Hsl, #Hps, #Hkvs⟩
    iexists (OpRespM.delete rev (W64 (n : Int)) prevs)
    isplitl
    · unfold opRespMsg
      isplitl; · ipureintro; exact Hn
      iexists w, r
      iframe #
      isplitl
      · ipureintro; exact Hrn
      · ipureintro; exact Hhn
    · ipureintro; simp [opRespRel]
  | .put k v l, .put | .putKeep k v, .put | .putIgnVal k l, .put =>
    simp only [txn.responseOpIs]
    iintro #H
    icases H with ⟨%Hn, %u, %w, %r, #Hu0, %Hu, #Hw, %rev, %prev, #Hrr⟩
    subst Hu
    iexists (OpRespM.put rev prev)
    isplitl
    · unfold opRespMsg
      isplitl; · ipureintro; exact Hn
      iexists w, r
      iframe #
    · ipureintro; simp [opRespRel]
  | .get _, .put | .get _, .delete _ | .get _, .txn .. | .delete _, .range .. | .delete _, .put
  | .delete _, .txn .. | .put .., .range .. | .put .., .delete _ | .put .., .txn ..
  | .putKeep .., .range .. | .putKeep .., .delete _ | .putKeep .., .txn ..
  | .putIgnVal .., .range .. | .putIgnVal .., .delete _ | .putIgnVal .., .txn .. =>
    simp only [txn.responseOpIs]
    iintro #H
    icases H with ⟨%Hn, %u, %w, %r, -, Hf⟩
    iexfalso; iexact Hf
termination_by sizeOf op

/-- **The server's responses are response messages that answer them** (in order). -/
theorem opResps_of_responseOps (skip : Bool) (ps : List Loc) (ops : List TxnOp)
    (rs : List TxnOpResult) :
    txn.responseOpsIs (GF := GF) skip ps ops rs ⊢
      ∃ ms : List OpRespM, opRespsMsg ps ms ∗ ⌜opRespsRel skip ops rs ms⌝ := by
  match ps, ops, rs with
  | [], [], [] =>
    iintro -
    iexists []
    unfold opRespsMsg
    isplitl; · itrivial
    ipureintro; simp [opRespsRel]
  | p :: ps, op :: ops, res :: rs =>
    iintro #H
    iunfold txn.responseOpsIs at H
    icases H with ⟨H1, H2⟩
    ihave ⟨%m, #H1, %Hm⟩ := opResp_of_responseOp skip p op res $$ H1
    ihave ⟨%ms, #H2, %Hms⟩ := opResps_of_responseOps skip ps ops rs $$ H2
    iexists m :: ms
    rw [opRespsMsg.eq_2]
    iframe #
    ipureintro
    simp only [opRespsRel]
    exact ⟨Hm, Hms⟩
  | [], [], _ :: _ | [], _ :: _, _ | _ :: _, [], _ | _ :: _, _ :: _, [] =>
    iintro H; iunfold txn.responseOpsIs at H; iexfalso; iexact H
termination_by sizeOf ops
end

end resp

/-! ## What a transaction's reply tells the client -/

/-- **A transaction within the txn package's model** (`v3rpc.txnInModel` of the model; a
premise): if read-only, each of its gets reads the transaction's revision and is not a sort cut
early by a limit (`txn.cutEarly`, `issues/etcd-range-sort-none-limit.md`). -/
def txnModelIn (t : TxnModel) : Prop :=
  txn.txnReadonly t = true →
    ∀ o : OpFull, TxnOp.get o ∈ t.thenOps ++ t.elseOps → o.base.rev = W64 0 ∧ ¬ txn.cutEarly o

theorem txnInModel_of (t : TxnModel) (cs : List CmpModel) (ts es : List v3rpc.ReqOp)
    (h : txnModelIn t) (hm : v3rpc.txnModelOf cs ts es = some t) : v3rpc.txnInModel cs ts es := by
  intro t' ht'
  rw [hm] at ht'
  cases ht'
  exact h

theorem txnWireOf_plain (t : TxnModel) (h : TxnModel.plain t) : TxnModel.plain (txnWireOf t) := by
  refine ⟨?_, ?_⟩
  · intro op hm
    simp only [txnWireOf, List.mem_map] at hm
    obtain ⟨op0, h0, rfl⟩ := hm
    exact opWire_plain op0 (h.1 op0 h0)
  · intro op hm
    simp only [txnWireOf, List.mem_map] at hm
    obtain ⟨op0, h0, rfl⟩ := hm
    exact opWire_plain op0 (h.2 op0 h0)

section reply
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **What a successful `Txn` of `t` delivers to the client** with the reply's message `m`, for a
client that knows the committed index `c` and has the floor `F` (the vertical slice's unit V2).
A read-only `t`: the server's run of `t` at a certified log extending `F`, after the read index
unless serializable (`readLogOk`), the header's revision its last; the verdict and the chosen
branch's responses the run's (`opRespsRel`). A writing `t`: the apply thread's application of
the request the proposed data decode to (`rq'`, whose transaction `t'` is `t` unless a range end
is `[0]`), at `x.log` extending `F`, the header's revision the write's; the verdict and the
responses the run's (ranges header-only if `skip`); mvcc's certificate of the log after and the
token minted (`revMinted`, exclusive: a reply's `Φ` is delivered once), with the write's witness
(`appliedWit γw`, unit C2a, at the request path's read names); unit W-M3: the caller's
certificate of the log read or written (`certOk`: its revisions are reached in the clients'
model) and `□ Q` of the state of the log the write met (the transaction's update fired there) or,
for a linearizable read-only `t`, of the log read (its read update, deposited with the read index,
fired there; as `rangeReplyOk`'s). -/
def txnReplied (E : apply.AEnv GF) (γw γr : ReadNames) (c : w64) (F : mvcc.Log) (t : TxnModel)
    (Q : KVState → IProp GF) (cid mid : w64) (m : TxnRespM) : IProp GF :=
  if txn.txnReadonly t then
    iprop(∃ log : mvcc.Log, mvcc.idxCert E.γ.idx log ∗ mvcc.certOk E.γ log ∗
      ⌜2 ≤ log.length ∧ log.length + 3 ≤ 2 ^ 63 ∧ F <+: log ∧
        m.hdr.revision = W64 ((log.length : Int) - 1) ∧ m.hdr.clusterId = cid ∧
        m.hdr.memberId = mid ∧
        m.succeeded = (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).1 ∧
        opRespsRel false (t.branch m.succeeded)
          (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.2 m.resps⌝ ∗
      (if txn.txnSerializable t then iprop(True) else readLogOk γr c log) ∗
      (if txn.txnSerializable t then iprop(True) else □ Q (kvStateOf log)))
  else
    iprop(∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel) (t' : TxnModel)
        (x x' : apply.ApplyKV) (l : mvcc.Log) (skip : Bool),
      ⌜irrWireOf (apply.withHeader (irrTxn t) hm) rq' ∧ rq'.txn = some t' ∧
        (irrNoZeroEnd (irrTxn t) → t' = t) ∧
        apply.applyStep rq' true x x' (.dispatched (.applied l false) skip) ∧
        m.hdr.revision = W64 (mvcc.writeRev x.log
          (txn.srvRunTxn (W64 (x.log.length : Int)) (mvcc.stateAfter x.log) t').2.1 : Int) ∧
        m.hdr.clusterId = cid ∧ m.hdr.memberId = mid ∧
        F <+: x.log ∧ 2 ≤ x.log.length ∧ x.log.length + 4 ≤ 2 ^ 63 ∧
        m.succeeded = (txn.srvRunTxn (W64 (x.log.length : Int)) (mvcc.stateAfter x.log) t').1 ∧
        opRespsRel skip (t'.branch m.succeeded)
          (txn.srvRunTxn (W64 (x.log.length : Int)) (mvcc.stateAfter x.log) t').2.2 m.resps⌝ ∗
      mvcc.idxCert E.γ.idx x'.log ∗ revMinted E x.log x'.log ∗ appliedWit γw x'.log ∗
      mvcc.certOk E.γ x'.log ∗ □ Q (kvStateOf x.log))

/-- **etcd's spec of the KV service's `Txn`** (the vertical slice's unit V2; a predicate
transformer, as `etcdPutSpec`): a caller asking a transaction `t` of plain operations (no nested
transaction: what the client's builder sends) within the txn package's model (`txnModelIn`: if
read-only, gets at the transaction's revision, no sort cut early by a limit), who knows the
committed index `c` and has the floor `F`, gets a reply message `m` with `txnReplied`. A writing
transaction (2026-10-15, unit T2) is plain in the KV model (`txn.txnPlain`: its gets at revision
`0`, its puts with no lease and no `IgnoreLease`), no range end `[0]` (`txnNoZeroEnd`), with the
caller's persistent update over the whole state `kvOpAu (.txn t) Q`, whose `□ Q` of the state it
linearized at the reply carries (unit W-M3: in `txnReplied`, at the state of the log the write
met); a read-only one takes none (`Q` trivial) or, linearizable (unit W-M3), a read update
(`kvReadAu`, at the read names, as `etcdRangeSpec`'s), whose `□ Q` at the state of the log read
the reply carries. -/
def etcdTxnSpec (E : apply.AEnv GF) (γw γr : ReadNames) (cid mid : w64) :
    GrpcSpec (GF := GF) pbTxnRequest pbTxnResponse :=
  fun (t : TxnModel) (Φ : TxnRespM → IProp GF) =>
    iprop(⌜TxnModel.plain t ∧ txnModelIn t⌝ ∗ ∃ Q : KVState → IProp GF,
      (⌜txn.txnReadonly t = true ∧ Q = fun _ => iprop(True)⌝ ∨
        (⌜txn.txnReadonly t = true ∧ txn.txnSerializable t = false⌝ ∗ kvReadAu γr.kv Q) ∨
        (⌜txn.txnReadonly t = false ∧ txn.txnPlain t ∧ txnNoZeroEnd t⌝ ∗
          kvOpAu γw.kv (.txn t) Q)) ∗
      ∃ (c : w64) (F : mvcc.Log), committedAtLeast γr c ∗
      mvcc.idxCert E.γ.idx F ∗
      ∀ m : TxnRespM, txnReplied E γw γr c F t Q cid mid m -∗ Φ m)

end reply

section proofs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **The server's `TxnResponse` is a message** (`txnRespMsg`) whose verdict and responses are
the run's: from the txn package's `txnResponseIs` and the handler's filled header. -/
theorem txnRespMsg_of_server (skip : Bool) (resp h : Loc) (rev : w64) (t : TxnModel) (ok : Bool)
    (rs : List TxnOpResult) (cid mid : w64) :
    structFieldRef etcdserverpb.TxnResponse go!"Header" resp ↦□ h ∗ v3rpc.hdrFilled h cid mid ∗
      txn.txnResponseIs (GF := GF) skip resp rev t ok rs ⊢ |==>
    ∃ m : TxnRespM, txnRespMsg resp m ∗
      ⌜m.hdr.revision = rev ∧ m.hdr.clusterId = cid ∧ m.hdr.memberId = mid ∧ m.succeeded = ok ∧
        opRespsRel skip (t.branch ok) rs m.resps⌝ := by
  iintro ⟨#Hh, Hf, #Hres⟩
  iunfold txn.txnResponseIs at Hres
  icases Hres with ⟨%Hrn, Hres⟩
  iunfold txn.txnRespFieldsIs at Hres
  icases Hres with ⟨%h2, #Hh2, %Hh2n, #Hrev, #Hok, Hrs⟩
  iunfold txn.respsIs at Hrs
  icases Hrs with ⟨%sl, %ps, #Hsl, #Hps, Hrs⟩
  ihave ⟨%ms, #Hms, %Hrel⟩ := opResps_of_responseOps skip ps (t.branch ok) rs $$ Hrs
  icombine Hh Hh2 gives %Heq
  subst Heq
  iunfold v3rpc.hdrFilled at Hf
  icases Hf with ⟨-, %tm, %ld, Hcid, Hmid, Ht, Hl⟩
  ipersist Hcid
  ipersist Hmid
  ipersist Ht
  ipersist Hl
  imodintro
  iexists (TxnRespM.mk (HdrM.mk cid mid rev tm ld) ok ms)
  isplitl
  · unfold txnRespMsg hdrFull
    isplitl; · ipureintro; exact Hrn
    iexists h, sl, ps
    iframe #
    ipureintro; exact Hh2n
  · ipureintro; exact ⟨rfl, rfl, rfl, rfl, Hrel⟩

end proofs

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **A run's slot** (see the file header): the reader slots a run of etcd's KV handlers holds
and gives back: `s.leadTimeMu`'s (`srvCall`'s), the store's, the logger's, the read loop's and the
auth store's reader resource (`E.RD`, 2026-10-14, unit A2; `srvRdCall`'s). The server hands the
gRPC runtime a number of them when it serves (bounded `RWMutex` slots: at most that many runs at
a time). -/
def etcdRunSlot (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  iprop(srvLeadTimeReader s ∗ mvcc.storeReader E.s E.γ ∗ srvLgReader s ∗ srvReadReader s γr ∗
    E.RD)

/-- **What a successful `Put` of `o` tells the client** about the reply's message `m` (persistent;
see the file header): since 2026-10-14 (unit C2a) with the witness that the log after is applied
through an index of the committed log at the read names `γr` (`appliedWit`: a linearizable read
at that index reads a log extending it, `client_get_after_put`); unit W-M3: the caller's
certificate of the log after (`certOk`: the put's revision is reached in the clients' model). -/
def putReplyOk (E : apply.AEnv GF) (γr : ReadNames) (F : mvcc.Log) (o : OpFull) (cid mid : w64)
    (m : PutRespM) : IProp GF :=
  iprop(∃ (hm : apply.HeaderModel) (x x' : apply.ApplyKV) (l : mvcc.Log) (skip : Bool),
    ⌜apply.applyStep (apply.withHeader (irrPut o) hm) true x x'
        (.dispatched (.applied l false) skip) ∧
      m.hdr.revision = W64 (x.log.length : Int) ∧ m.hdr.clusterId = cid ∧ m.hdr.memberId = mid ∧
      m.prev = (if o.base.prevKV then mvcc.findKey o.key (mvcc.stateAfter x.log) else none) ∧
      F <+: x.log ∧ 2 ≤ x.log.length ∧ x.log.length + 4 ≤ 2 ^ 63⌝ ∗
    mvcc.idxCert E.γ.idx x'.log ∗ appliedWit γr x'.log ∗ mvcc.certOk E.γ x'.log)

instance putReplyOk_persistent (E : apply.AEnv GF) (γr : ReadNames) (F : mvcc.Log) (o : OpFull)
    (cid mid : w64) (m : PutRespM) : Persistent (putReplyOk E γr F o cid mid m) := by
  unfold putReplyOk; infer_instance

/-- **What a successful `Get` of `o` tells the client** about the reply's message `m`
(persistent; see the file header); 2026-10-14 (unit T1): a linearizable get's result `□ Q` at the
log read (its update, deposited with the read index, fired there; 2026-10-15, unit T2: at the
whole state of the log read, `kvStateOf`); the log read extends the caller's floor `F` (the
vertical slice's unit V2); unit W-M3: the caller's certificate of the log read (`certOk`). -/
def rangeReplyOk (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (F : mvcc.Log) (o : OpFull)
    (cid mid : w64) (Q : KVState → IProp GF) (m : RangeRespM) : IProp GF :=
  iprop(∃ log : mvcc.Log, mvcc.idxCert E.γ.idx log ∗ mvcc.certOk E.γ log ∗
    ⌜2 ≤ log.length ∧ log.length + 3 ≤ 2 ^ 63 ∧
      m.hdr.revision = W64 ((log.length : Int) - 1) ∧ m.hdr.clusterId = cid ∧
      m.hdr.memberId = mid ∧ sint.Z o.base.rev ≤ sint.Z m.hdr.revision ∧
      m.count = txn.srvCount o
        (mvcc.stateAt log (sint.nat (mvcc.rangeRev m.hdr.revision o.base.rev))) true ∧
      txn.srvRangeOk o (mvcc.stateAt log (sint.nat (mvcc.rangeRev m.hdr.revision o.base.rev)))
        m.kvs m.more ∧ F <+: log⌝ ∗
    (if o.base.serializable then iprop(True) else readLogOk γr c log) ∗
    (if o.base.serializable then iprop(True) else □ Q (kvStateOf log)))

instance rangeReplyOk_persistent (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (F : mvcc.Log)
    (o : OpFull) (cid mid : w64) (Q : KVState → IProp GF) (m : RangeRespM) :
    Persistent (rangeReplyOk E γr c F o cid mid Q m) := by
  unfold rangeReplyOk; split <;> infer_instance

/-- **What a successful `Put` of `o` delivers to the client** with the reply's message `m`
(the merge of the generic gRPC specification with the slice's unit V1, 2026-10-14): `putReplyOk`'s
knowledge (with its witness at the read names `γr`, unit C2a) and the token of the revision the
put made (`revMinted`, exclusive: a reply's `Φ` is delivered once, so the generic spec carries it;
`putReplied_ok` drops it); unit W-M3: `□ Q` of the state of the log the put met (the put's
update fired there: the state it linearized at). -/
def putReplied (E : apply.AEnv GF) (γr : ReadNames) (F : mvcc.Log) (o : OpFull)
    (Q : KVState → IProp GF) (cid mid : w64) (m : PutRespM) : IProp GF :=
  iprop(∃ (hm : apply.HeaderModel) (x x' : apply.ApplyKV) (l : mvcc.Log) (skip : Bool),
    ⌜apply.applyStep (apply.withHeader (irrPut o) hm) true x x'
        (.dispatched (.applied l false) skip) ∧
      m.hdr.revision = W64 (x.log.length : Int) ∧ m.hdr.clusterId = cid ∧ m.hdr.memberId = mid ∧
      m.prev = (if o.base.prevKV then mvcc.findKey o.key (mvcc.stateAfter x.log) else none) ∧
      F <+: x.log ∧ 2 ≤ x.log.length ∧ x.log.length + 4 ≤ 2 ^ 63⌝ ∗
    mvcc.idxCert E.γ.idx x'.log ∗ revMinted E x.log x'.log ∗ appliedWit γr x'.log ∗
    mvcc.certOk E.γ x'.log ∗ □ Q (kvStateOf x.log))

open Iris.ProofMode in
/-- The knowledge of a delivered put (its token and its update's result dropped; the witness
kept). -/
theorem putReplied_ok (E : apply.AEnv GF) (γr : ReadNames) (F : mvcc.Log) (o : OpFull)
    (Q : KVState → IProp GF) (cid mid : w64) (m : PutRespM) :
    putReplied E γr F o Q cid mid m ⊢ putReplyOk E γr F o cid mid m := by
  iintro H
  unfold putReplied putReplyOk
  icases H with ⟨%hm, %x, %x', %l, %skip, %Hp, #Hc, -, #Hw, #Hok, -⟩
  iexists hm, x, x', l, skip
  iframe Hc Hw Hok
  ipureintro; exact Hp

/-- **etcd's spec of the KV service's `Put`** (a predicate transformer; see the file header): a
caller asking the put `o` gets a reply message `m` with `putReplied` (`putReplyOk`, with its
witness at the read names `γr` (2026-10-14, unit C2a), and the revision's token), at a log
extending the caller's floor `F` (the vertical slice's unit V2); since 2026-10-15 (unit T2) a put
with no lease (any other flags) with the caller's persistent update over the whole state
`kvOpAu (.put o) Q`, whose `□ Q` of the state it linearized at the reply carries. -/
def etcdPutSpec (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64) :
    GrpcSpec (GF := GF) pbPutRequest pbPutResponse :=
  fun (o : OpFull) (Φ : PutRespM → IProp GF) =>
    iprop(∃ F : mvcc.Log, mvcc.idxCert E.γ.idx F ∗
      ∃ Q : KVState → IProp GF, ⌜o.leaseID = W64 0⌝ ∗ kvOpAu γr.kv (.put o) Q ∗
          ∀ m : PutRespM, putReplied E γr F o Q cid mid m -∗ Φ m)

/-- **A get of `key` after the put of `key ↦ val` read the put** (persistent; unit C2a,
2026-10-14; `client_get_after_put`): the put's reply `mp` and the get's reply `m` are of two logs of
the member's store, the put's log after `x'.log` (the log `x.log` the put met with the put's change,
`put_applied_log`; `mp`'s revision `x.log`'s length) a prefix of the get's `l` (certified; `m`'s
revision `l`'s last, so at least the put's), and the get's answer the server's selection of `key`
at `l`; if no revision of `l` after the put's touches `key`, the get's key-values are exactly
the put's (`get_after_put_kvs`). -/
def getAfterPutOk (E : apply.AEnv GF) (key val : GoString) (cid mid : w64) (mp : PutRespM)
    (m : RangeRespM) : IProp GF :=
  iprop(∃ (hm : apply.HeaderModel) (x x' : apply.ApplyKV) (lp : mvcc.Log) (skip : Bool)
      (l : mvcc.Log),
    ⌜apply.applyStep (apply.withHeader (irrPut (putKeyOp key val)) hm) true x x'
        (.dispatched (.applied lp false) skip) ∧
      x'.log = x.log ++ [[txn.putChangeOf (putKeyOp key val)
        (mvcc.findKey key (mvcc.stateAfter x.log))]] ∧
      mp.hdr.revision = W64 (x.log.length : Int) ∧
      x'.log <+: l ∧ 2 ≤ l.length ∧ l.length + 3 ≤ 2 ^ 63 ∧
      m.hdr.revision = W64 ((l.length : Int) - 1) ∧ m.hdr.clusterId = cid ∧ m.hdr.memberId = mid ∧
      sint.Z mp.hdr.revision ≤ sint.Z m.hdr.revision ∧
      m.count = txn.srvCount (getKeyOp key) (mvcc.stateAfter l) true ∧
      txn.srvRangeOk (getKeyOp key) (mvcc.stateAfter l) m.kvs m.more ∧
      ((∀ cs ∈ l.drop x'.log.length, ∀ c ∈ cs, c.key ≠ key) →
        ∃ kv, m.kvs = [kv] ∧ kv.key = key ∧ kv.value = val ∧ m.more = false)⌝ ∗
    mvcc.idxCert E.γ.idx l)

instance getAfterPutOk_persistent (E : apply.AEnv GF) (key val : GoString) (cid mid : w64)
    (mp : PutRespM) (m : RangeRespM) : Persistent (getAfterPutOk E key val cid mid mp m) := by
  unfold getAfterPutOk; infer_instance

/-- **etcd's spec of the KV service's `Range`**: a caller that knows the committed index `c`
(`committedAtLeast γr c`; `0` is free) asking the range `o` gets a reply message `m` with
`rangeReplyOk` at `c`; since 2026-10-14 (unit T1) with the caller's persistent read update
(`kvReadAu`, over the whole state since 2026-10-15, unit T2: a linearizable range), or none (`Q`
trivial). -/
def etcdRangeSpec (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64) :
    GrpcSpec (GF := GF) pbRangeRequest pbRangeResponse :=
  fun (o : OpFull) (Φ : RangeRespM → IProp GF) =>
    iprop(∃ (c : w64) (F : mvcc.Log) (Q : KVState → IProp GF), committedAtLeast γr c ∗
      mvcc.idxCert E.γ.idx F ∗
      (⌜Q = fun _ => iprop(True)⌝ ∨ (⌜o.base.serializable = false⌝ ∗ kvReadAu γr.kv Q)) ∗
      ∀ m : RangeRespM, rangeReplyOk E γr c F o cid mid Q m -∗ Φ m)

/-- **What a successful `DeleteRange` of `o` tells the client** about the reply's message `m`
(persistent): the apply thread's application of the delete `op'` the proposed data decode to
(`o` itself unless a range end is empty, `deleteRange_end_to_end`'s `deleteAppliedOk`), at the log
the entry met, the reply's header revision the delete's write revision, its ids the cluster's and
member's, `Deleted` the number of keys in the range, `PrevKvs` their key-values if asked;
mvcc's certificate of the log after. -/
def deleteReplyOk (E : apply.AEnv GF) (γr : ReadNames) (F : mvcc.Log) (o : OpFull) (cid mid : w64)
    (m : DelRespM) : IProp GF :=
  iprop(∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel) (op' : OpFull) (x x' : apply.ApplyKV)
      (l : mvcc.Log) (skip : Bool),
    ⌜irrWireOf (apply.withHeader (irrDeleteRange o) hm) rq' ∧ rq'.deleteRange = some op' ∧
      (irrNoZeroEnd (irrDeleteRange o) → op' = o) ∧
      apply.applyStep rq' true x x' (.dispatched (.applied l false) skip) ∧
      m.hdr.revision =
        W64 ((mvcc.writeRev x.log (txn.delChanges (mvcc.stateAfter x.log) op') : Nat) : Int) ∧
      m.hdr.clusterId = cid ∧ m.hdr.memberId = mid ∧
      m.deleted = W64 ((rangeIn (mvcc.stateAfter x.log) op').length : Int) ∧
      m.prevs = (if op'.base.prevKV then rangeIn (mvcc.stateAfter x.log) op' else []) ∧
      F <+: x.log ∧ 2 ≤ x.log.length ∧ x.log.length + 4 ≤ 2 ^ 63⌝ ∗
    mvcc.idxCert E.γ.idx x'.log ∗ appliedWit γr x'.log ∗ mvcc.certOk E.γ x'.log)

instance deleteReplyOk_persistent (E : apply.AEnv GF) (γr : ReadNames) (F : mvcc.Log) (o : OpFull)
    (cid mid : w64) (m : DelRespM) : Persistent (deleteReplyOk E γr F o cid mid m) := by
  unfold deleteReplyOk; infer_instance

/-- **What a successful `DeleteRange` of `o` delivers to the client** (as `putReplied`):
`deleteReplyOk`'s knowledge and the revision's token (`revMinted`; none minted if nothing was
deleted). -/
def deleteReplied (E : apply.AEnv GF) (γr : ReadNames) (F : mvcc.Log) (o : OpFull)
    (Q : KVState → IProp GF) (cid mid : w64) (m : DelRespM) : IProp GF :=
  iprop(∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel) (op' : OpFull) (x x' : apply.ApplyKV)
      (l : mvcc.Log) (skip : Bool),
    ⌜irrWireOf (apply.withHeader (irrDeleteRange o) hm) rq' ∧ rq'.deleteRange = some op' ∧
      (irrNoZeroEnd (irrDeleteRange o) → op' = o) ∧
      apply.applyStep rq' true x x' (.dispatched (.applied l false) skip) ∧
      m.hdr.revision =
        W64 ((mvcc.writeRev x.log (txn.delChanges (mvcc.stateAfter x.log) op') : Nat) : Int) ∧
      m.hdr.clusterId = cid ∧ m.hdr.memberId = mid ∧
      m.deleted = W64 ((rangeIn (mvcc.stateAfter x.log) op').length : Int) ∧
      m.prevs = (if op'.base.prevKV then rangeIn (mvcc.stateAfter x.log) op' else []) ∧
      F <+: x.log ∧ 2 ≤ x.log.length ∧ x.log.length + 4 ≤ 2 ^ 63⌝ ∗
    mvcc.idxCert E.γ.idx x'.log ∗ revMinted E x.log x'.log ∗ appliedWit γr x'.log ∗
    mvcc.certOk E.γ x'.log ∗ □ Q (kvStateOf x.log))

open Iris.ProofMode in
/-- The knowledge of a delivered delete (its token and its update's result dropped). -/
theorem deleteReplied_ok (E : apply.AEnv GF) (γr : ReadNames) (F : mvcc.Log) (o : OpFull)
    (Q : KVState → IProp GF) (cid mid : w64) (m : DelRespM) :
    deleteReplied E γr F o Q cid mid m ⊢ deleteReplyOk E γr F o cid mid m := by
  iintro H
  unfold deleteReplied deleteReplyOk
  icases H with ⟨%hm, %rq', %op', %x, %x', %l, %skip, %Hp, #Hc, -, #Hw, #Hok, -⟩
  iexists hm, rq', op', x, x', l, skip
  iframe Hc Hw Hok
  ipureintro; exact Hp

/-- **etcd's spec of the KV service's `DeleteRange`**: a caller asking the delete `o` gets a
reply message `m` with `deleteReplied` (`deleteReplyOk` and the revision's token); since
2026-10-15 (unit T2) a delete whose range end is not `[0]` (the wire keeps it), with the caller's
persistent update over the whole state `kvOpAu (.deleteRange o) Q`, whose `□ Q` of the state it
linearized at the reply carries. -/
def etcdDeleteSpec (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64) :
    GrpcSpec (GF := GF) pbDeleteRangeRequest pbDeleteRangeResponse :=
  fun (o : OpFull) (Φ : DelRespM → IProp GF) =>
    iprop(∃ F : mvcc.Log, mvcc.idxCert E.γ.idx F ∗
      ∃ Q : KVState → IProp GF, ⌜o.base.rangeEnd ≠ [W8 0]⌝ ∗ kvOpAu γr.kv (.deleteRange o) Q ∗
      ∀ m : DelRespM, deleteReplied E γr F o Q cid mid m -∗ Φ m)

/-- **etcd's KV methods** as registered (unit P3b): `Put`, `Range` and `DeleteRange`, the generated
handlers of `KV_ServiceDesc` (`rpc_grpc.pb.go`) with the service value `RegisterKVServer` is
given (`v3rpc.Server`: `NewQuotaKVServer(s)`, the `*quotaKVServer` `q`), with etcd's specs (the
`Put`'s witness at the request path's read names `γw`, 2026-10-14, unit C2a). -/
def etcdKVMethods (q : Loc) (E : apply.AEnv GF) (γw γr : ReadNames) (cid mid : w64) :
    List (GrpcMethod GF) :=
  [⟨go!"/etcdserverpb.KV/Put", pbPutRequest, pbPutResponse, etcdPutSpec E γw cid mid,
     (@! etcdserverpb._KV_Put_Handler),
     interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty) #q⟩,
   ⟨go!"/etcdserverpb.KV/Range", pbRangeRequest, pbRangeResponse, etcdRangeSpec E γr cid mid,
     (@! etcdserverpb._KV_Range_Handler),
     interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty) #q⟩,
   ⟨go!"/etcdserverpb.KV/DeleteRange", pbDeleteRangeRequest, pbDeleteRangeResponse,
     etcdDeleteSpec E γw cid mid, (@! etcdserverpb._KV_DeleteRange_Handler),
     interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty) #q⟩,
   ⟨go!"/etcdserverpb.KV/Txn", pbTxnRequest, pbTxnResponse,
     etcdTxnSpec E γw γr cid mid, (@! etcdserverpb._KV_Txn_Handler),
     interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty) #q⟩]

/-- **What `RegisterKVServer(gs, q)` registers of the KV service's unary methods we specify**
(the `ServiceDesc`'s `MethodDesc`s under `"/etcdserverpb.KV/"`, with the service value). -/
def etcdKVRegs (q : Loc) : List (GoString × val × GoInterface) :=
  [(go!"/etcdserverpb.KV/Put", (@! etcdserverpb._KV_Put_Handler),
     interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty) #q),
   (go!"/etcdserverpb.KV/Range", (@! etcdserverpb._KV_Range_Handler),
     interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty) #q),
   (go!"/etcdserverpb.KV/DeleteRange", (@! etcdserverpb._KV_DeleteRange_Handler),
     interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty) #q),
   (go!"/etcdserverpb.KV/Txn", (@! etcdserverpb._KV_Txn_Handler),
     interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty) #q)]

/-- **The interceptors' per-run resources** (`v3rpc.Server`'s chain: `newLogUnaryInterceptor`'s
reader slot of `s.lgMu`, the metrics interceptor's and `newUnaryInterceptor`'s none). -/
def etcdIcRs (s : Loc) : List (IProp GF) := [srvLgReader s, iprop(True), iprop(True)]

/-- **A run's slot, as grpc's runtime holds it** (unit P3b): the handlers' (`etcdRunSlot`), the
quota wrapper's reader slot of `s.leadTimeMu` and auth reader resource `E.RD` (its NOSPACE alarm's
`raftRequest`; `E.RD` since unit A2), and the interceptors' (`etcdIcRs`). -/
def etcdGrpcSlot (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  iprop((etcdRunSlot s E γr ∗ srvLeadTimeReader s ∗ E.RD) ∗ [∗list] R ∈ etcdIcRs s, R)

end defs

section proofs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `kvServerAt` reads of the server's parameters only what does not depend on the committed index
the caller knew of (`hdrIs`: the KV's `Rev()` resources). -/
theorem kvServerAt_srvKVAns (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (c c' cid mid n : w64) (F F' : mvcc.Log) (d d' : v3rpc.KVDep GF) :
    v3rpc.kvServerAt (GF := GF) p s (v3rpc.srvKVAns s E ρ γr c F d) cid mid n =
      v3rpc.kvServerAt p s (v3rpc.srvKVAns s E ρ γr c' F' d') cid mid n := rfl

open Iris.ProofMode in
/-- **A range's deposit's result at the log read** (2026-10-14, unit T1): the server's answer's
(`rangeAnsOk`'s, at a committed raft log whose model is the log read) as the client's `□ Q` of the
state of the log read (2026-10-15, unit T2), for no deposit (`Q` trivial) or the client's read. -/
theorem readQ_of_ans (γr : ReadNames) (d : v3rpc.KVDep GF) (Q : KVState → IProp GF)
    (ser : Bool) (log : mvcc.Log)
    (h : (d = .none ∧ Q = fun _ => iprop(True)) ∨ d = .read Q) :
    (if ser then iprop(True) else
      ∃ L : List EntryModel, srvRLogLb γr.raft L ∗ ⌜kvModel γr.kv L = log⌝ ∗
        □ v3rpc.rangeDepQ γr.kv d L : IProp GF) ⊢
      (if ser then iprop(True) else □ Q (kvStateOf log)) := by
  cases hs : ser
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iintro ⟨%L, -, %HL, #HQ⟩
    rcases h with ⟨rfl, rfl⟩ | rfl
    · iintro !>; itrivial
    · simp only [v3rpc.rangeDepQ]
      rw [← HL]
      iintro !>
      iexact HQ
  · simp only [↓reduceIte]; iintro -; itrivial


theorem rangeQ_of_ans (γr : ReadNames) (d : v3rpc.KVDep GF) (Q : KVState → IProp GF)
    (o : OpFull) (log : mvcc.Log)
    (h : (d = .none ∧ Q = fun _ => iprop(True)) ∨ d = .read Q) :
    (if o.base.serializable then iprop(True) else
      ∃ L : List EntryModel, srvRLogLb γr.raft L ∗ ⌜kvModel γr.kv L = log⌝ ∗
        □ v3rpc.rangeDepQ γr.kv d L : IProp GF) ⊢
      (if o.base.serializable then iprop(True) else □ Q (kvStateOf log)) :=
  readQ_of_ans γr d Q o.base.serializable log h

/-- A run's call resources give back its slot (the committed index dropped). -/
theorem etcdRunSlot_back (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (c : w64) :
    srvLeadTimeReader (GF := GF) s ∗ srvRdCall s E γr c ⊢ etcdRunSlot s E γr := by
  iintro ⟨Hlt, Hrd⟩
  unfold srvRdCall etcdRunSlot
  icases Hrd with ⟨Hsr, Hlg, -, Hrr, Hard⟩
  iframe

/-- **A run's context carries no trace** (`traceutil.ctxTraceIs ci none`, what `v3rpc.srvCall`
needs, unit P1b): `TraceKey` is a type of etcd's packages, under which the server's runtime sets no
value (`grpcRunCtx`, part of the trusted runtime). -/
theorem ctxTraceIs_none_of_runCtx (ci : GoInterfaceOk) :
    grpcRunCtx (GF := GF) ci ⊢ traceutil.ctxTraceIs ci none := by
  iintro #H
  iunfold grpcRunCtx at H
  unfold traceutil.ctxTraceIs
  iintro !> %Φ HΦ
  simp only [traceutil.traceKeyVal, go_etcd_io.etcd.pkg.v3.traceutil.TraceKey.ty]
  iapply H
  · ipureintro
    exact ⟨go!"pkg/v3/traceutil.TraceKey", rfl⟩
  inext
  iapply HΦ
  ipureintro
  left; rfl

/-- **etcd's `Put` handler meets etcd's `Put` spec** (`grpcHandlerOk`; from `put_end_to_end`):
a run, with its slot, the runtime's context, an id credit the server mints (`□ |==> idCred ρ.ids
1`, `srvStarted`'s), the decoded request: its slot back, the reply holds the response's
message, with `putReplied` (`putReplyOk` and the revision's token). -/
theorem etcd_putHandlerOk (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (cid mid n : w64) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗
        v3rpc.kvServerAt p s (v3rpc.srvKVAns s E ρ γr (W64 0) [] .none) cid mid n ∗
        □ (|==> idCred ρ.ids 1) ⊢
      grpcHandlerOk (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!!
      go!"Put") (etcdRunSlot s E γr) (etcdPutSpec E ρ.rd cid mid) := by
  iintro ⟨#Pv, #Ps, #Hsrv, #Hsrd, #Hat, #HNR⟩
  unfold grpcHandlerOk
  iintro %o %Φ %ci %cd %r !> %Ψ ⟨Hslot, #Hctx, #Hrc, #Hr, Hspec⟩ HΨ
  ihave #Htr := ctxTraceIs_none_of_runCtx ci $$ Hrc
  rw [show (pbPutRequest (GF := GF)).recv r o = txn.putRequestIs r o from rfl]
  iunfold etcdPutSpec at Hspec
  icases Hspec with ⟨%F, #HF, Hspec⟩
  ihave ⟨%d, Hdep, %Hdp, Hk⟩ : iprop(∃ d : v3rpc.KVDep GF, v3rpc.kvDepOwn ρ γr d ∗
      ⌜v3rpc.kvDepPre d (.put o)⌝ ∗
      ∀ m : PutRespM, putReplied E ρ.rd F o (v3rpc.opDepQ d) cid mid m -∗ Φ m)
      $$ [Hspec]
  · icases Hspec with ⟨%Q, %Hpl, #Hau, Hk⟩
    iexists (.op (.put o) Q)
    rw [show v3rpc.kvDepOwn (GF := GF) ρ γr (.op (.put o) Q) = kvOpAu ρ.kv (.put o) Q from rfl]
    isplitr
    · iexact Hau
    isplitr
    · ipureintro; exact ⟨⟨Q, rfl⟩, Hpl⟩
    iintro %m Hm
    iapply Hk
    simp only [v3rpc.opDepQ]; iexact Hm
  rw [kvServerAt_srvKVAns p s E ρ γr (W64 0) (W64 0) cid mid n [] F .none d]
  iunfold etcdRunSlot at Hslot
  icases Hslot with ⟨Hlt, Hsr, Hlg, Hrd, Hard⟩
  ihave Hu := HNR
  imod Hu with Hid
  imod (monoNatLbOwn_0 (GF := GF) γr.committed) with #H0
  iapply wp_fupd
  iapply (v3rpc.put_end_to_end p s E ρ γr (W64 0) cid mid n (GoInterface.ok ci) r o F d) $$
    [Hlt Hsr Hlg Hrd Hard Hid Hdep]
  · iframe #
    unfold v3rpc.srvCall srvRdCall committedAtLeast
    isplitl [Hlt Hid]
    · iexists ci, cd
      iframe
      iframe #
      ipureintro; rfl
    iframe
    rw [show uint.nat (W64 0) = 0 from rfl]
    iframe H0
    ipureintro; exact Hdp
  inext
  iintro %resp %err Hpost
  cases hc : v3rpc.putCheck o with
  | some e =>
    icases Hpost with ⟨#Hco, Hc, Hc0, -⟩
    unfold v3rpc.srvCall
    icases Hc with ⟨%ci', %cd', -, -, -, -, Hlt⟩
    iunfold v3rpc.checkOut at Hco
    icases Hco with ⟨-, #Hev⟩
    iunfold txn.errVarIs at Hev
    icases Hev with ⟨%e', -, %He'⟩
    imodintro
    iapply HΨ
    isplitl [Hlt Hc0]
    · iapply etcdRunSlot_back s E γr (W64 0)
      iframe
    iintro %Hnil
    rw [He'] at Hnil; cases Hnil
  | none =>
    icases Hpost with (⟨%Herr, %h, %rv, %rv', #Hh, Hf, -, Hc0, Hap⟩ | ⟨%Herr, %e, Hc0, Hep⟩)
    · obtain ⟨rfl, Hrn⟩ := Herr
      iunfold v3rpc.putAppliedOk at Hap
      icases Hap with ⟨Hlt, Hap⟩
      iunfold v3rpc.putApplied at Hap
      -- the revision's token (`revMinted`, exclusive) goes to the reply's `Φ` (`putReplied`),
      -- with the witness (`appliedWit`, persistent)
      icases Hap with ⟨%hm, %x, %x', %l, %skip, %Hst, Hout, #Hcert, Htok, #Hwit, #Hcok, #HQv⟩
      iunfold apply.putOutcomeIs at Hout
      icases Hout with ⟨#Hpr, -⟩
      iunfold txn.putResponseIs at Hpr
      icases Hpr with ⟨-, %h2, %pk, #Hh2, %Hh2n, #Hrev, #Hpk, #Hprev⟩
      icombine Hh Hh2 gives %Heq
      subst Heq
      iunfold v3rpc.hdrFilled at Hf
      icases Hf with ⟨-, %t, %ld, Hcid, Hmid, Ht, Hl⟩
      ipersist Hcid
      ipersist Hmid
      ipersist Ht
      ipersist Hl
      imodintro
      iapply HΨ
      isplitl [Hlt Hc0]
      · iapply etcdRunSlot_back s E γr (W64 0)
        iframe
      iintro -
      iexists (PutRespM.mk (HdrM.mk cid mid (W64 (x.log.length : Int)) t ld)
        (if o.base.prevKV then mvcc.findKey o.key (mvcc.stateAfter x.log) else none))
      isplitl []
      · simp only [pbPutResponse]
        unfold putRespMsg hdrFull
        isplitl []
        · ipureintro; exact Hrn
        iexists h, pk
        iframe #
        ipureintro; exact Hh2n
      · iapply Hk
        unfold putReplied
        iexists hm, x, x', l, skip
        iframe Htok
        iframe #
        ipureintro
        exact ⟨Hst.1, rfl, rfl, rfl, rfl, Hst.2.2⟩
    · iunfold v3rpc.putErrOk at Hep
      icases Hep with ⟨Hlt, -⟩
      imodintro
      iapply HΨ
      isplitl [Hlt Hc0]
      · iapply etcdRunSlot_back s E γr (W64 0)
        iframe
      iintro %Hnil
      exact absurd Hnil Herr.2

/-- **etcd's `Range` handler meets etcd's `Range` spec** (`grpcHandlerOk`; from
`range_end_to_end`): as `etcd_putHandlerOk`, the reply with `rangeReplyOk` at the committed index
the caller knew of. -/
theorem etcd_rangeHandlerOk (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (cid mid n : w64) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗
        v3rpc.kvServerAt p s (v3rpc.srvKVAns s E ρ γr (W64 0) [] .none) cid mid n ∗
        □ (|==> idCred ρ.ids 1) ⊢
      grpcHandlerOk (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!!
      go!"Range") (etcdRunSlot s E γr) (etcdRangeSpec E γr cid mid) := by
  iintro ⟨#Pv, #Ps, #Hsrv, #Hsrd, #Hat, #HNR⟩
  unfold grpcHandlerOk
  iintro %o %Φ %ci %cd %r !> %Ψ ⟨Hslot, #Hctx, #Hrc, #Hr, Hspec⟩ HΨ
  ihave #Htr := ctxTraceIs_none_of_runCtx ci $$ Hrc
  rw [show (pbRangeRequest (GF := GF)).recv r o = txn.rangeRequestIs r o from rfl]
  iunfold etcdRangeSpec at Hspec
  icases Hspec with ⟨%c, %F, %Q, #Hc0, #HF, Hdq, Hk⟩
  ihave ⟨%d, Hdep, %Hdp, %Hdd⟩ : iprop(∃ d : v3rpc.KVDep GF, v3rpc.kvDepOwn ρ γr d ∗
      ⌜v3rpc.kvDepPre d (.range o)⌝ ∗
      ⌜(d = .none ∧ Q = fun _ => iprop(True)) ∨ d = .read Q⌝) $$ [Hdq]
  · icases Hdq with (%HQ | ⟨%Hser, #Hau⟩)
    · iexists .none
      rw [show v3rpc.kvDepOwn (GF := GF) ρ γr .none = iprop(True) from rfl]
      isplitr
      · itrivial
      ipureintro
      exact ⟨(fun Q' h => by cases h), Or.inl ⟨rfl, HQ⟩⟩
    · iexists (.read Q)
      rw [show v3rpc.kvDepOwn (GF := GF) ρ γr (.read Q) = kvReadAu γr.kv Q from rfl]
      iframe Hau
      ipureintro
      exact ⟨(fun Q' h => by cases h; exact Hser), Or.inr rfl⟩
  rw [kvServerAt_srvKVAns p s E ρ γr (W64 0) c cid mid n [] F .none d]
  iunfold etcdRunSlot at Hslot
  icases Hslot with ⟨Hlt, Hsr, Hlg, Hrd, Hard⟩
  ihave Hu := HNR
  imod Hu with Hid
  iapply wp_fupd
  iapply (v3rpc.range_end_to_end p s E ρ γr c cid mid n (GoInterface.ok ci) r o F d) $$
    [Hlt Hsr Hlg Hrd Hard Hid Hdep]
  · iframe #
    unfold v3rpc.srvCall srvRdCall
    isplitl [Hlt Hid]
    · iexists ci, cd
      iframe
      iframe #
      ipureintro; rfl
    iframe
    iframe Hc0
    ipureintro; exact Hdp
  inext
  iintro %resp %err Hpost
  cases hc : v3rpc.rangeCheck o with
  | some e =>
    icases Hpost with ⟨#Hco, Hc, Hcr, -⟩
    unfold v3rpc.srvCall
    icases Hc with ⟨%ci', %cd', -, -, -, -, Hlt⟩
    iunfold v3rpc.checkOut at Hco
    icases Hco with ⟨-, #Hev⟩
    iunfold txn.errVarIs at Hev
    icases Hev with ⟨%e', -, %He'⟩
    imodintro
    iapply HΨ
    isplitl [Hlt Hcr]
    · iapply etcdRunSlot_back s E γr c
      iframe
    iintro %Hnil
    rw [He'] at Hnil; cases Hnil
  | none =>
    icases Hpost with (⟨%Herr, %h, %rv, %rv', #Hh, Hf, -, Hcr, -, Hlt, Hans⟩ |
      ⟨%Herr, %e, Hcr, -, Hlt⟩)
    · obtain ⟨rfl, Hrn⟩ := Herr
      iunfold v3rpc.rangeAnsOk at Hans
      icases Hans with ⟨%log, #Hcert, #Hcok, %Hlog, #Hrl, HQl, Hres⟩
      ihave #HQl' := rangeQ_of_ans γr d Q o log Hdd $$ HQl
      iunfold txn.rangeResult at Hres
      icases Hres with (⟨%Hx, -⟩ | ⟨%Hx, -⟩ | ⟨%Hx, %kvs, %more, #Hrr, %Hsel⟩)
      · exact absurd Hx.2 Hrn
      · exact absurd Hx.2.2.2 Hrn
      iunfold txn.rangeResponseIs at Hrr
      icases Hrr with ⟨-, %h2, %sl, %ps, #Hh2, %Hh2n, #Hrev, #Hkvs, #Hps, #Hkv, #Hmore, #Hcount⟩
      icombine Hh Hh2 gives %Heq
      subst Heq
      iunfold v3rpc.hdrFilled at Hf
      icases Hf with ⟨-, %t, %ld, Hcid, Hmid, Ht, Hl⟩
      ipersist Hcid
      ipersist Hmid
      ipersist Ht
      ipersist Hl
      imodintro
      iapply HΨ
      isplitl [Hlt Hcr]
      · iapply etcdRunSlot_back s E γr c
        iframe
      iintro -
      iexists (RangeRespM.mk (HdrM.mk cid mid (W64 ((log.length : Int) - 1)) t ld) kvs more
        (txn.srvCount o (mvcc.stateAt log (sint.nat (mvcc.rangeRev (W64 ((log.length : Int) - 1))
          o.base.rev))) true))
      isplitl []
      · simp only [pbRangeResponse]
        unfold rangeRespMsg hdrFull
        isplitl []
        · ipureintro; exact Hrn
        iexists h, sl, ps
        iframe #
        ipureintro; exact Hh2n
      · iapply Hk
        unfold rangeReplyOk
        iexists log
        iframe #
        ipureintro
        exact ⟨Hlog.1, Hlog.2.1, rfl, rfl, rfl, Hx.1, rfl, Hsel, Hlog.2.2.2⟩
    · imodintro
      iapply HΨ
      isplitl [Hlt Hcr]
      · iapply etcdRunSlot_back s E γr c
        iframe
      iintro %Hnil
      exact absurd Hnil Herr.2

/-- **etcd's `DeleteRange` handler meets etcd's `DeleteRange` spec** (`grpcHandlerOk`; from
`deleteRange_end_to_end`): as `etcd_putHandlerOk`, the reply with `deleteReplyOk`. A third
registered method needs only this (its spec and handler proof), no new axiom. -/
theorem etcd_deleteHandlerOk (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (cid mid n : w64) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗
        v3rpc.kvServerAt p s (v3rpc.srvKVAns s E ρ γr (W64 0) [] .none) cid mid n ∗
        □ (|==> idCred ρ.ids 1) ⊢
      grpcHandlerOk
        (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!!
          go!"DeleteRange")
        (etcdRunSlot s E γr) (etcdDeleteSpec E ρ.rd cid mid) := by
  iintro ⟨#Pv, #Ps, #Hsrv, #Hsrd, #Hat, #HNR⟩
  unfold grpcHandlerOk
  iintro %o %Φ %ci %cd %r !> %Ψ ⟨Hslot, #Hctx, #Hrc, #Hr, Hspec⟩ HΨ
  ihave #Htr := ctxTraceIs_none_of_runCtx ci $$ Hrc
  rw [show (pbDeleteRangeRequest (GF := GF)).recv r o = txn.deleteRangeRequestIs r o from rfl]
  iunfold etcdDeleteSpec at Hspec
  icases Hspec with ⟨%F, #HF, %Q, %Hz, #Hau, Hk⟩
  rw [kvServerAt_srvKVAns p s E ρ γr (W64 0) (W64 0) cid mid n [] F .none
    (.op (.deleteRange o) Q)]
  iunfold etcdRunSlot at Hslot
  icases Hslot with ⟨Hlt, Hsr, Hlg, Hrd, Hard⟩
  ihave Hu := HNR
  imod Hu with Hid
  imod (monoNatLbOwn_0 (GF := GF) γr.committed) with #H0
  iapply wp_fupd
  iapply (v3rpc.deleteRange_end_to_end p s E ρ γr (W64 0) cid mid n (GoInterface.ok ci) r o F
      (.op (.deleteRange o) Q)) $$ [Hlt Hsr Hlg Hrd Hard Hid]
  · rw [show v3rpc.kvDepOwn (GF := GF) ρ γr (.op (.deleteRange o) Q) = kvOpAu ρ.kv (.deleteRange o) Q from rfl]
    iframe #
    unfold v3rpc.srvCall srvRdCall committedAtLeast
    isplitl [Hlt Hid]
    · iexists ci, cd
      iframe
      iframe #
      ipureintro; rfl
    iframe
    rw [show uint.nat (W64 0) = 0 from rfl]
    iframe H0
    ipureintro; exact ⟨⟨Q, rfl⟩, Hz⟩
  inext
  iintro %resp %err Hpost
  cases hc : v3rpc.deleteCheck o with
  | some e =>
    icases Hpost with ⟨#Hco, Hc, Hc0, -⟩
    unfold v3rpc.srvCall
    icases Hc with ⟨%ci', %cd', -, -, -, -, Hlt⟩
    iunfold v3rpc.checkOut at Hco
    icases Hco with ⟨-, #Hev⟩
    iunfold txn.errVarIs at Hev
    icases Hev with ⟨%e', -, %He'⟩
    imodintro
    iapply HΨ
    isplitl [Hlt Hc0]
    · iapply etcdRunSlot_back s E γr (W64 0)
      iframe
    iintro %Hnil
    rw [He'] at Hnil; cases Hnil
  | none =>
    icases Hpost with (⟨%Herr, %h, %rv, %rv', #Hh, Hf, -, Hc0, Hap⟩ | ⟨%Herr, %e, Hc0, Hep⟩)
    · obtain ⟨rfl, Hrn⟩ := Herr
      iunfold v3rpc.deleteAppliedOk at Hap
      icases Hap with ⟨Hlt, Hap⟩
      iunfold v3rpc.deleteApplied at Hap
      -- the revision's token (`revMinted`) goes to the reply's `Φ` (`deleteReplied`)
      icases Hap with ⟨%hm, %rq', %op', %x, %x', %l, %skip, %Hst, Hout, #Hcert, Htok, #Hwit, #Hcok,
        #HQv⟩
      simp only [v3rpc.opDepQ] at *
      iunfold apply.deleteOutcomeIs at Hout
      icases Hout with ⟨#Hdr, -⟩
      iunfold txn.deleteRangeResponseIs at Hdr
      icases Hdr with ⟨-, %h2, %sl, %ps, #Hh2, %Hh2n, #Hrev, #Hdel, #Hpk, #Hps, #Hkvs⟩
      icombine Hh Hh2 gives %Heq
      subst Heq
      iunfold v3rpc.hdrFilled at Hf
      icases Hf with ⟨-, %t, %ld, Hcid, Hmid, Ht, Hl⟩
      ipersist Hcid
      ipersist Hmid
      ipersist Ht
      ipersist Hl
      imodintro
      iapply HΨ
      isplitl [Hlt Hc0]
      · iapply etcdRunSlot_back s E γr (W64 0)
        iframe
      iintro -
      iexists (DelRespM.mk (HdrM.mk cid mid
          (W64 ((mvcc.writeRev x.log (txn.delChanges (mvcc.stateAfter x.log) op') : Nat) : Int))
          t ld)
        (W64 ((rangeIn (mvcc.stateAfter x.log) op').length : Int))
        (if op'.base.prevKV then rangeIn (mvcc.stateAfter x.log) op' else []))
      isplitl []
      · simp only [pbDeleteRangeResponse]
        unfold delRespMsg hdrFull
        isplitl []
        · ipureintro; exact Hrn
        iexists h, sl, ps
        iframe #
        ipureintro; exact Hh2n
      · iapply Hk
        unfold deleteReplied
        iexists hm, rq', op', x, x', l, skip
        iframe Htok
        iframe #
        ipureintro
        exact ⟨Hst.1, Hst.2.1, Hst.2.2.1, Hst.2.2.2.1, rfl, rfl, rfl, rfl, rfl, Hst.2.2.2.2.2⟩
    · iunfold v3rpc.deleteErrOk at Hep
      icases Hep with ⟨Hlt, -⟩
      imodintro
      iapply HΨ
      isplitl [Hlt Hc0]
      · iapply etcdRunSlot_back s E γr (W64 0)
        iframe
      iintro %Hnil
      exact absurd Hnil Herr.2

/-- **etcd's `Txn` handler meets etcd's `Txn` spec** (`grpcHandlerOk`; from `txn_end_to_end`; the
vertical slice's unit V2): as `etcd_rangeHandlerOk`, for a transaction of plain operations within
the txn package's model (`etcdTxnSpec`'s premises), the reply with `txnReplied` at the committed
index the caller knew of and its floor. -/
theorem etcd_txnHandlerOk (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (cid mid n : w64) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗
        v3rpc.kvServerAt p s (v3rpc.srvKVAns s E ρ γr (W64 0) [] .none) cid mid n ∗
        □ (|==> idCred ρ.ids 1) ⊢
      grpcHandlerOk (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!!
      go!"Txn") (etcdRunSlot s E γr) (etcdTxnSpec E ρ.rd γr cid mid) := by
  iintro ⟨#Pv, #Ps, #Hsrv, #Hsrd, #Hat, #HNR⟩
  unfold grpcHandlerOk
  iintro %t %Φ %ci %cd %r !> %Ψ ⟨Hslot, #Hctx, #Hrc, #Hr, Hspec⟩ HΨ
  ihave #Htr := ctxTraceIs_none_of_runCtx ci $$ Hrc
  rw [show (pbTxnRequest (GF := GF)).recv r t = iprop(txn.txnRequestIs r t ∗ txnWireOk r t)
    from rfl]
  iunfold etcdTxnSpec at Hspec
  icases Hspec with ⟨%Hpl, %Q, Hnp, %c, %F, #Hc0, #HF, Hspec⟩
  obtain ⟨hp, hin⟩ := Hpl
  icases Hr with ⟨#Hreq, #Hw⟩
  ihave ⟨%ts, %es, #Htq, #Htw, %Hmod⟩ := txnReq_of_requestIs r t hp $$ [$Hreq $Hw]
  -- the deposit (unit T2): none, or (unit W-M3) a linearizable read-only transaction's read
  -- update, or a writing one's update
  ihave ⟨%d, Hdep, %Hdp, %HdQ⟩ : iprop(∃ d : v3rpc.KVDep GF, v3rpc.kvDepOwn ρ γr d ∗
      ⌜v3rpc.kvDepPre d (.txn t.cmps ts es)⌝ ∗
      ⌜(txn.txnReadonly t = true ∧ ((d = .none ∧ Q = fun _ => iprop(True)) ∨ d = .read Q)) ∨
        (txn.txnReadonly t = false ∧ d = .op (.txn t) Q)⌝) $$ [Hnp]
  · icases Hnp with (%Hro | ⟨%Hrs, #Hau⟩ | ⟨%Hw, #Hau⟩)
    · iexists .none
      rw [show v3rpc.kvDepOwn (GF := GF) ρ γr .none = iprop(True) from rfl]
      isplitr
      · itrivial
      ipureintro
      refine ⟨?_, Or.inl ⟨Hro.1, Or.inl ⟨rfl, Hro.2⟩⟩⟩
      intro t' ht'
      rw [Hmod] at ht'
      cases ht'
      left; exact ⟨Hro.1, fun Q' h => by cases h⟩
    · iexists (.read Q)
      rw [show v3rpc.kvDepOwn (GF := GF) ρ γr (.read Q) = kvReadAu γr.kv Q from rfl]
      iframe Hau
      ipureintro
      refine ⟨?_, Or.inl ⟨Hrs.1, Or.inr rfl⟩⟩
      intro t' ht'
      rw [Hmod] at ht'
      cases ht'
      left; exact ⟨Hrs.1, fun Q' _ => Hrs.2⟩
    · iexists (.op (.txn t) Q)
      rw [show v3rpc.kvDepOwn (GF := GF) ρ γr (.op (.txn t) Q) = kvOpAu ρ.kv (.txn t) Q from rfl]
      iframe Hau
      ipureintro
      refine ⟨?_, Or.inr ⟨Hw.1, rfl⟩⟩
      intro t' ht'
      rw [Hmod] at ht'
      cases ht'
      right; exact ⟨⟨Q, rfl⟩, Hw.2⟩
  rw [kvServerAt_srvKVAns p s E ρ γr (W64 0) c cid mid n [] F .none d]
  iunfold etcdRunSlot at Hslot
  icases Hslot with ⟨Hlt, Hsr, Hlg, Hrd⟩
  ihave Hu := HNR
  imod Hu with Hid
  iapply wp_fupd
  iapply (v3rpc.txn_end_to_end p s E ρ γr c cid mid n (GoInterface.ok ci) r t.cmps ts es F d) $$
    [Hlt Hsr Hlg Hrd Hid Hdep]
  · iframe #
    unfold v3rpc.srvCall srvRdCall
    isplitl [Hlt Hid]
    · iexists ci, cd
      iframe
      iframe #
      ipureintro; rfl
    iframe
    iframe Hc0
    isplitr
    · ipureintro; exact txnInModel_of t _ _ _ hin Hmod
    ipureintro; exact Hdp
  inext
  iintro %resp %err Hpost
  cases hc : v3rpc.txnAllCheck (sint.Z n) t.cmps ts es with
  | some e =>
    simp only [hc]
    icases Hpost with ⟨#Hco, Hc, Hcr, -⟩
    unfold v3rpc.srvCall
    icases Hc with ⟨%ci', %cd', -, -, -, -, Hlt⟩
    iunfold v3rpc.checkOut at Hco
    icases Hco with ⟨-, #Hev⟩
    iunfold txn.errVarIs at Hev
    icases Hev with ⟨%e', -, %He'⟩
    imodintro
    iapply HΨ
    isplitl [Hlt Hcr]
    · iapply etcdRunSlot_back s E γr c
      iframe
    iintro %Hnil
    rw [He'] at Hnil; cases Hnil
  | none =>
    simp only [hc]
    icases Hpost with (⟨%Herr, %h, %rv, %rv', #Hh, Hf, -, Hcr, Hlt, %t', %Ht', Hans⟩ |
      ⟨%Herr, %e, Hcr, Hlt, -⟩)
    · rw [Hmod] at Ht'
      cases Ht'
      obtain ⟨rfl, Hrn⟩ := Herr
      cases hro : txn.txnReadonly t with
      | true =>
        simp only [hro, ↓reduceIte]
        icases Hans with ⟨-, Hans⟩
        iunfold v3rpc.txnReadAns at Hans
        icases Hans with ⟨%log, #Hcert, #Hcok, %Hlog, #Hrl, HQl, Hres⟩
        have hdq : (d = .none ∧ Q = fun _ => iprop(True)) ∨ d = .read Q := by
          rcases HdQ with ⟨-, h⟩ | ⟨h, -⟩
          · exact h
          · rw [hro] at h; cases h
        ihave #HQl' := readQ_of_ans γr d Q (txn.txnSerializable t) log hdq $$ HQl
        imod (txnRespMsg_of_server false resp h _ t _ _ cid mid) $$ [$Hh $Hf $Hres]
          with ⟨%m, #Hm, %Hmm⟩
        imodintro
        iapply HΨ
        isplitl [Hlt Hcr]
        · iapply etcdRunSlot_back s E γr c
          iframe
        iintro -
        iexists m
        isplitl []
        · simp only [pbTxnResponse]; iexact Hm
        iapply Hspec
        unfold txnReplied
        simp only [hro, ↓reduceIte]
        iexists log
        iframe #
        ipureintro
        obtain ⟨h1, h2, h3, h4, h5⟩ := Hmm
        refine ⟨Hlog.1, Hlog.2.1, Hlog.2.2.2, ?_, h2, h3, h4, ?_⟩
        · rw [h1]
        · rw [h4]; exact h5
      | false =>
        simp only [hro, Bool.false_eq_true, ↓reduceIte]
        iunfold v3rpc.txnAppliedAns at Hans
        icases Hans with ⟨%hm, %rq', %t'', %x, %x', %l, %skip, %Hst, Hout, #Hcert, HMint, #Hwit,
          #Hcok, #HQv⟩
        have hdq : d = .op (.txn t) Q := by
          rcases HdQ with ⟨h, -⟩ | ⟨-, h⟩
          · rw [hro] at h; cases h
          · exact h
        subst hdq
        simp only [v3rpc.opDepQ] at *
        iunfold apply.txnOutcomeIs at Hout
        icases Hout with ⟨#Hres, -⟩
        imod (txnRespMsg_of_server skip resp h _ t'' _ _ cid mid) $$ [$Hh $Hf $Hres]
          with ⟨%m, #Hm, %Hmm⟩
        imodintro
        iapply HΨ
        isplitl [Hlt Hcr]
        · iapply etcdRunSlot_back s E γr c
          iframe
        iintro -
        iexists m
        isplitl []
        · simp only [pbTxnResponse]; iexact Hm
        iapply Hspec
        unfold txnReplied
        simp only [hro, Bool.false_eq_true, ↓reduceIte]
        iexists hm, rq', t'', x, x', l, skip
        iframe Hcert HMint Hwit Hcok HQv
        ipureintro
        obtain ⟨h1, h2, h3, h4, h5⟩ := Hmm
        obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ := Hst
        refine ⟨s1, s2, s3, s4, ?_, h2, h3, s6, s7, s8, h4, ?_⟩
        · rw [h1]
        · rw [h4]; exact h5
    · obtain ⟨-, Hne⟩ := Herr
      imodintro
      iapply HΨ
      isplitl [Hlt Hcr]
      · iapply etcdRunSlot_back s E γr c
        iframe
      iintro %Hnil
      exact absurd Hnil Hne

/-- A put or delete request at a pointer: the learner check reads nothing of it. -/
theorem putReq_learnerOk (l : Loc) :
    ⊢ v3rpc.learnerReqOk (GF := GF)
      (interface.mkOk (go.GoType.PointerType etcdserverpb.PutRequest.ty) #l) :=
  v3rpc.learnerReqOk_ptr _ l (by
    simp [etcdserverpb.PutRequest.ty, etcdserverpb.RangeRequest.ty])

theorem deleteReq_learnerOk (l : Loc) :
    ⊢ v3rpc.learnerReqOk (GF := GF)
      (interface.mkOk (go.GoType.PointerType etcdserverpb.DeleteRangeRequest.ty) #l) :=
  v3rpc.learnerReqOk_ptr _ l (by
    simp [etcdserverpb.DeleteRangeRequest.ty, etcdserverpb.RangeRequest.ty])

/-- **etcd's `Put`, as grpc runs it** (`grpcMethodOk`): the generated `_KV_Put_Handler` on the
`*quotaKVServer` `q` whose `Put` meets etcd's spec, under a chain of transparent interceptors
(for requests the learner check reads); the run's resource is the method's and the
interceptors'. -/
theorem etcd_putMethodOk [v3rpc.QuotaKVServerIsKVServer] (q : Loc) (E : apply.AEnv GF)
    (γr : ReadNames) (cid mid : w64) (S : IProp GF) (ics : List GoFunc) (Rs : List (IProp GF)) :
    grpcHandlerOk (q @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty @!! go!"Put")
        S (etcdPutSpec E γr cid mid) ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
        srvInterceptorsOk v3rpc.learnerReqOk ics Rs ⊢
      grpcMethodOk (@! etcdserverpb._KV_Put_Handler)
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty) #q)
        ics iprop(S ∗ [∗list] R ∈ Rs, R) (etcdPutSpec E γr cid mid) := by
  iintro ⟨#Hh, #Ppb, #Hics⟩
  unfold grpcMethodOk
  iintro %m %Φ %ci %cd %dec %ui !> %Ψ ⟨⟨HS, HRs⟩, #Hctx, #Hrc, #Hdec, #Hch, HSpec⟩ HΨ
  ihave #Hbl : iprop(□ ∀ l : Loc, l ↦ (zero_val etcdserverpb.PutRequest) -∗
      (pbPutRequest (GF := GF)).blank l) $$ []
  · iintro !> %l Hl; simp only [pbPutRequest]; iexact Hl
  ihave #HQr : iprop(□ ∀ l : Loc, (pbPutRequest (GF := GF)).recv l m -∗
      v3rpc.learnerReqOk (interface.mkOk (go.GoType.PointerType etcdserverpb.PutRequest.ty) #l)) $$ []
  · iintro !> %l -
    iapply putReq_learnerOk
  iapply (v3rpc.etcdserverpb.wp__KV_Put_Handler pbPutRequest pbPutResponse (etcdPutSpec E γr cid mid)
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty, #q⟩
    S ics Rs v3rpc.learnerReqOk m Φ ci cd dec ui rfl rfl v3rpc.QuotaKVServerIsKVServer.is_kv)
    $$ [HS HRs HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, HRs, Hres⟩
  iapply HΨ
  iframe

/-- **etcd's `Range`, as grpc runs it** (as `etcd_putMethodOk`). -/
theorem etcd_rangeMethodOk [v3rpc.QuotaKVServerIsKVServer] (q : Loc) (E : apply.AEnv GF)
    (γr : ReadNames) (cid mid : w64) (S : IProp GF) (ics : List GoFunc) (Rs : List (IProp GF)) :
    grpcHandlerOk (q @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty @!! go!"Range")
        S (etcdRangeSpec E γr cid mid) ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ srvInterceptorsOk v3rpc.learnerReqOk ics Rs ⊢
      grpcMethodOk (@! etcdserverpb._KV_Range_Handler)
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty) #q)
        ics iprop(S ∗ [∗list] R ∈ Rs, R) (etcdRangeSpec E γr cid mid) := by
  iintro ⟨#Hh, #Ppb, #Hics⟩
  unfold grpcMethodOk
  iintro %m %Φ %ci %cd %dec %ui !> %Ψ ⟨⟨HS, HRs⟩, #Hctx, #Hrc, #Hdec, #Hch, HSpec⟩ HΨ
  ihave #Hbl : iprop(□ ∀ l : Loc, l ↦ (zero_val etcdserverpb.RangeRequest) -∗
      (pbRangeRequest (GF := GF)).blank l) $$ []
  · iintro !> %l Hl; simp only [pbRangeRequest]; iexact Hl
  ihave #HQr : iprop(□ ∀ l : Loc, (pbRangeRequest (GF := GF)).recv l m -∗
      v3rpc.learnerReqOk (interface.mkOk (go.GoType.PointerType etcdserverpb.RangeRequest.ty) #l)) $$ []
  · iintro !> %l #Hr
    rw [show (pbRangeRequest (GF := GF)).recv l m = txn.rangeRequestIs l m from rfl]
    iapply (v3rpc.learnerReqOk_range l m)
    iexact Hr
  iapply (v3rpc.etcdserverpb.wp__KV_Range_Handler pbRangeRequest pbRangeResponse
    (etcdRangeSpec E γr cid mid)
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty, #q⟩
    S ics Rs v3rpc.learnerReqOk m Φ ci cd dec ui rfl rfl v3rpc.QuotaKVServerIsKVServer.is_kv)
    $$ [HS HRs HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, HRs, Hres⟩
  iapply HΨ
  iframe

/-- **etcd's `DeleteRange`, as grpc runs it** (as `etcd_putMethodOk`). -/
theorem etcd_deleteMethodOk [v3rpc.QuotaKVServerIsKVServer] (q : Loc) (E : apply.AEnv GF)
    (γr : ReadNames) (cid mid : w64) (S : IProp GF) (ics : List GoFunc) (Rs : List (IProp GF)) :
    grpcHandlerOk (q @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty @!! go!"DeleteRange")
        S (etcdDeleteSpec E γr cid mid) ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ srvInterceptorsOk v3rpc.learnerReqOk ics Rs ⊢
      grpcMethodOk (@! etcdserverpb._KV_DeleteRange_Handler)
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty) #q)
        ics iprop(S ∗ [∗list] R ∈ Rs, R) (etcdDeleteSpec E γr cid mid) := by
  iintro ⟨#Hh, #Ppb, #Hics⟩
  unfold grpcMethodOk
  iintro %m %Φ %ci %cd %dec %ui !> %Ψ ⟨⟨HS, HRs⟩, #Hctx, #Hrc, #Hdec, #Hch, HSpec⟩ HΨ
  ihave #Hbl : iprop(□ ∀ l : Loc, l ↦ (zero_val etcdserverpb.DeleteRangeRequest) -∗
      (pbDeleteRangeRequest (GF := GF)).blank l) $$ []
  · iintro !> %l Hl; simp only [pbDeleteRangeRequest]; iexact Hl
  ihave #HQr : iprop(□ ∀ l : Loc, (pbDeleteRangeRequest (GF := GF)).recv l m -∗
      v3rpc.learnerReqOk (interface.mkOk (go.GoType.PointerType etcdserverpb.DeleteRangeRequest.ty) #l)) $$ []
  · iintro !> %l -
    iapply deleteReq_learnerOk
  iapply (v3rpc.etcdserverpb.wp__KV_DeleteRange_Handler pbDeleteRangeRequest pbDeleteRangeResponse
    (etcdDeleteSpec E γr cid mid)
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty, #q⟩
    S ics Rs v3rpc.learnerReqOk m Φ ci cd dec ui rfl rfl v3rpc.QuotaKVServerIsKVServer.is_kv)
    $$ [HS HRs HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, HRs, Hres⟩
  iapply HΨ
  iframe

theorem txnReq_learnerOk (l : Loc) :
    ⊢ v3rpc.learnerReqOk (GF := GF)
      (interface.mkOk (go.GoType.PointerType etcdserverpb.TxnRequest.ty) #l) :=
  v3rpc.learnerReqOk_ptr _ l (by
    simp [etcdserverpb.TxnRequest.ty, etcdserverpb.RangeRequest.ty])

/-- **etcd's `Txn`, as grpc runs it** (as `etcd_putMethodOk`; the vertical slice's unit V2). -/
theorem etcd_txnMethodOk [v3rpc.QuotaKVServerIsKVServer] (q : Loc) (E : apply.AEnv GF)
    (γw γr : ReadNames) (cid mid : w64) (S : IProp GF) (ics : List GoFunc) (Rs : List (IProp GF)) :
    grpcHandlerOk (q @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty @!! go!"Txn")
        S (etcdTxnSpec E γw γr cid mid) ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ srvInterceptorsOk v3rpc.learnerReqOk ics Rs ⊢
      grpcMethodOk (@! etcdserverpb._KV_Txn_Handler)
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty) #q)
        ics iprop(S ∗ [∗list] R ∈ Rs, R) (etcdTxnSpec E γw γr cid mid) := by
  iintro ⟨#Hh, #Ppb, #Hics⟩
  unfold grpcMethodOk
  iintro %m %Φ %ci %cd %dec %ui !> %Ψ ⟨⟨HS, HRs⟩, #Hctx, #Hrc, #Hdec, #Hch, HSpec⟩ HΨ
  ihave #Hbl : iprop(□ ∀ l : Loc, l ↦ (zero_val etcdserverpb.TxnRequest) -∗
      (pbTxnRequest (GF := GF)).blank l) $$ []
  · iintro !> %l Hl; simp only [pbTxnRequest]; iexact Hl
  ihave #HQr : iprop(□ ∀ l : Loc, (pbTxnRequest (GF := GF)).recv l m -∗
      v3rpc.learnerReqOk (interface.mkOk (go.GoType.PointerType etcdserverpb.TxnRequest.ty) #l)) $$ []
  · iintro !> %l -
    iapply txnReq_learnerOk
  iapply (v3rpc.etcdserverpb.wp__KV_Txn_Handler pbTxnRequest pbTxnResponse (etcdTxnSpec E γw γr cid mid)
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty, #q⟩
    S ics Rs v3rpc.learnerReqOk m Φ ci cd dec ui rfl rfl v3rpc.QuotaKVServerIsKVServer.is_kv)
    $$ [HS HRs HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, HRs, Hres⟩
  iapply HΨ
  iframe

/-- **etcd's server serves its KV methods** (the server side, `grpc_serve_rpcs`; unit P3b: as grpc
runs them): the gRPC server at `addr` built with the chain `[il, im, iu]` (`v3rpc.Server`'s:
`newLogUnaryInterceptor(s)`'s, grpc-prometheus's, `newUnaryInterceptor(s)`'s) with the KV
service registered on the `*quotaKVServer` `q` (`RegisterKVServer(gs, NewQuotaKVServer(s))`:
`etcdKVRegs q` among the registered methods), that hands the runtime `N` run slots
(`etcdGrpcSlot`), registers etcd's `Put`, `Range` and `DeleteRange` specs at `addr` (`isGrpcRpc`).
Premises: the server's (`isServerReq`, `isServerRead`, its `*kvServer` `p`, the id budget
`□ |==> idCred ρ.ids 1` of `srvStarted`), the quota wrapper over `p` (`quotaKVServerAt`: what
`NewQuotaKVServer(s)` returns), the interceptors' contracts (`srvInterceptorOk`: what
`newLogUnaryInterceptor(s)` and `newUnaryInterceptor(s)` return, proved; grpc-prometheus's,
assumed), the method-set fact `QuotaKVServerIsKVServer`, the packages'. -/
theorem etcd_kv_served [v3rpc.QuotaKVServerIsKVServer] (addr : GoString) (p q s : Loc)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (cid mid n : w64) (il im iu : GoFunc)
    (regs : List (GoString × val × GoInterface)) (N : Nat)
    (hregs : ∀ x ∈ etcdKVRegs (GF := GF) q, x ∈ regs) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗
        v3rpc.kvServerAt p s (v3rpc.srvKVAns s E ρ γr (W64 0) [] .none) cid mid n ∗
        □ (|==> idCred ρ.ids 1) ∗
        v3rpc.quotaKVServerAt q
          ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩ s ∗
        srvInterceptorOk il (srvLgReader s) v3rpc.learnerReqOk ∗
        srvInterceptorOk im iprop(True) v3rpc.learnerReqOk ∗
        srvInterceptorOk iu iprop(True) v3rpc.learnerReqOk ∗
        grpcServerAt addr [il, im, iu] regs ∗
        ([∗list] _x ∈ List.replicate N (), etcdGrpcSlot s E γr) ⊢
      |={⊤}=> isGrpcRpc addr go!"/etcdserverpb.KV/Put" (etcdPutSpec E ρ.rd cid mid) ∗
        isGrpcRpc addr go!"/etcdserverpb.KV/Range" (etcdRangeSpec E γr cid mid) ∗
        isGrpcRpc addr go!"/etcdserverpb.KV/DeleteRange" (etcdDeleteSpec E ρ.rd cid mid) ∗
        isGrpcRpc addr go!"/etcdserverpb.KV/Txn" (etcdTxnSpec E ρ.rd γr cid mid) := by
  iintro ⟨#Pv, #Ps, #Hsrv, #Hsrd, #Hat, #HNR, #Hq, #Hil, #Him, #Hiu, Hl, Hslots⟩
  ihave #Hp := etcd_putHandlerOk p s E ρ γr cid mid n $$ []
  · iframe #
  ihave #Hr := etcd_rangeHandlerOk p s E ρ γr cid mid n $$ []
  · iframe #
  ihave #Hd := etcd_deleteHandlerOk p s E ρ γr cid mid n $$ []
  · iframe #
  ihave #Ht := etcd_txnHandlerOk p s E ρ γr cid mid n $$ []
  · iframe #
  ihave #Hqt := v3rpc.quotaKV_txnHandlerOk_of v3rpc.quotaKVServer.wp_Txn (etcdTxnSpec E ρ.rd γr cid mid) q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩ E ρ
    (etcdRunSlot s E γr) $$ []
  · iframe #
  ihave #Hqp := v3rpc.quotaKV_putHandlerOk_of v3rpc.quotaKVServer.wp_Put (etcdPutSpec E ρ.rd cid mid) q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩ E ρ
    (etcdRunSlot s E γr) $$ []
  · iframe #
  ihave #Hr' := grpcHandlerOk_frame _ _ iprop(srvLeadTimeReader s ∗ E.RD) (etcdRangeSpec E γr cid mid) $$ Hr
  ihave #Hd' := grpcHandlerOk_frame _ _ iprop(srvLeadTimeReader s ∗ E.RD) (etcdDeleteSpec E ρ.rd cid mid) $$ Hd
  ihave #Hqr := v3rpc.quotaKV_promotedHandlerOk (etcdRangeSpec E γr cid mid) q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩
    iprop(etcdRunSlot s E γr ∗ srvLeadTimeReader s ∗ E.RD) go!"Range" inferInstance $$ [Hq Hr']
  · iframe #
  ihave #Hqd := v3rpc.quotaKV_promotedHandlerOk (etcdDeleteSpec E ρ.rd cid mid) q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩
    iprop(etcdRunSlot s E γr ∗ srvLeadTimeReader s ∗ E.RD) go!"DeleteRange" inferInstance $$ [Hq Hd']
  · iframe #
  ihave #Hics : srvInterceptorsOk (GF := GF) v3rpc.learnerReqOk [il, im, iu] (etcdIcRs s) $$ []
  · unfold etcdIcRs srvInterceptorsOk srvInterceptorsOk srvInterceptorsOk srvInterceptorsOk
    iframe #
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  ihave #Hmp := etcd_putMethodOk q E ρ.rd cid mid _ _ _ $$ [Hqp Ppb Hics]
  · iframe #
  ihave #Hmr := etcd_rangeMethodOk q E γr cid mid _ _ _ $$ [Hqr Ppb Hics]
  · iframe #
  ihave #Hmd := etcd_deleteMethodOk q E ρ.rd cid mid _ _ _ $$ [Hqd Ppb Hics]
  · iframe #
  ihave #Hmt := etcd_txnMethodOk q E ρ.rd γr cid mid _ _ _ $$ [Hqt Ppb Hics]
  · iframe #
  imod (grpc_serve_rpcs addr [il, im, iu] regs (etcdKVMethods q E ρ.rd γr cid mid)
    (etcdGrpcSlot s E γr) N (by simp only [etcdKVMethods, List.map]; decide)
    (by
      intro x hx
      apply hregs
      simp only [etcdKVMethods, List.mem_cons, List.mem_nil_iff, _root_.or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> simp [etcdKVRegs])) $$ [Hl Hslots] with Hrpcs
  · iframe
    imodintro
    simp only [etcdKVMethods]
    unfold etcdGrpcSlot
    iframe #
    iapply BigSepL.bigSepL_nil.2
    itrivial
  simp only [etcdKVMethods]
  icases Hrpcs with ⟨#H1, #H2, #H3, #H4, -⟩
  imodintro
  iframe #

/-- **`client_put_end_to_end`** (see the file header): `kv.Put(ctx, key, val)` with no options
(`optsAt sl []`, e.g. `nil`) on a `*kv` over a connection to the server at `addr` (`kvObjAt`:
what `NewKV` returns, `v3.wp_NewKV`) whose `Put` is registered with etcd's spec (`isGrpcRpc`, what
`etcd_kv_served` gives): `nil` and the reply's message `m` with `putReplied` (`putReplyOk` and the
revision's token) for the put
`key ↦ val` the server decodes (no lease, no previous key-value, value and lease not ignored),
and (2026-10-15, unit T2) `□ Q` of the state at which the caller's persistent update over the
whole state, `kvOpAu (.put (putKeyOp key val)) Q`, linearized the put (unit W-M3: in
`putReplied`, the state of the log the put met); or an error and no reply.
Premises: the registration, the context's (`ctxErrClient`), the package's. -/
theorem client_put_end_to_end (api : Loc) (addr : GoString) (E : apply.AEnv GF) (γr : ReadNames)
    (cid mid : w64) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (key val : GoString)
    (sl : GoSlice) (Q : KVState → IProp GF) (F : mvcc.Log) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kvObjAt api addr ∗
        isGrpcRpc addr go!"/etcdserverpb.KV/Put" (etcdPutSpec E γr cid mid) ∗
        context.isContext ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
        kvOpAu γr.kv (.put (putKeyOp key val)) Q ∗ mvcc.idxCert E.γ.idx F ∗ emptyKeyIf key }}
      (App (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
          go!"Put")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #val)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : PutRespM, putRespMsg resp m ∗
            putReplied E γr F (txn.putOpOf key val (W64 0) false false false) Q cid mid m) ∨
          ⌜err ≠ GoInterface.nil ∧ resp = null⌝ }} := by
  iintro %Φ ⟨#Pc, #Hkv, #Hrpc, #Hctx, #Hce, #Hopts, #Hau, #HF, #Hek⟩ HΦ
  ihave #Hctx' := ctxOk_of_isContext ci cd $$ Hctx
  iclear Hctx
  ihave #Hek' : emptyKeyIf (opPutModel key val []).key $$ [Hek]
  · rw [show (opPutModel key val []).key = key from rfl]; iexact Hek
  iapply (v3.kv.wp_Put api addr ci cd key val sl [] (etcdPutSpec E γr cid mid)
    (fun m => iprop(putReplied E γr F (txn.putOpOf key val (W64 0) false false false) Q cid mid m)))
    $$ []
  · iframe #
    isplitl []
    · ipureintro
      refine ⟨?_, rfl⟩
      unfold opPutModel OpFull.putPanics opFold OpFull.putInit OpFull.newOp OpModel.zero
      simp
    · have Hw : putWireOf (opPutModel key val []) =
          txn.putOpOf key val (W64 0) false false false := rfl
      rw [Hw]
      imodintro
      inext
      unfold etcdPutSpec
      iexists F
      iframe HF
      iexists Q
      isplitr
      · ipureintro; rfl
      isplitr
      · iexact Hau
      iintro %m Hm
      iexact Hm
  inext
  iintro %resp %err Hout
  iapply HΦ
  iunfold putCallOut at Hout
  icases Hout with (⟨%Herr, %m, Hm, Hq⟩ | ⟨%Herr, -⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m
    iframe
  · iright
    ipureintro; exact ⟨Herr.1, Herr.2.2⟩

/-- **`client_get_end_to_end`** (see the file header): `kv.Get(ctx, key)` with no options on a
`*kv` over a connection to the server at `addr` whose `Range` is registered with etcd's spec, by
a client that knows the committed index `c` (`committedAtLeast γr c`; `0` is free): `nil` and the
reply's message `m` with `rangeReplyOk` for the get of `key` the server decodes (the key alone, at
the latest revision, linearizable: read after the read index, at a log extending the log applied
through an index at least `c`); or an error and no reply. -/
theorem client_get_end_to_end (api : Loc) (addr : GoString) (E : apply.AEnv GF) (γr : ReadNames)
    (c cid mid : w64) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (key : GoString) (sl : GoSlice) (Q : KVState → IProp GF) (F : mvcc.Log) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kvObjAt api addr ∗
        isGrpcRpc addr go!"/etcdserverpb.KV/Range" (etcdRangeSpec E γr cid mid) ∗
        context.isContext ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗ committedAtLeast γr c ∗
        (⌜Q = fun _ => iprop(True)⌝ ∨ kvReadAu γr.kv Q) ∗ mvcc.idxCert E.γ.idx F ∗ emptyKeyIf key }}
      (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
          go!"Get")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : RangeRespM, rangeRespMsg resp m ∗
            rangeReplyOk E γr c F (txn.rangeOpOf key [] (W64 0) (W64 0) (W32 0) (W32 0) false false
              false (W64 0) (W64 0) (W64 0) (W64 0)) cid mid Q m) ∨
          ⌜err ≠ GoInterface.nil ∧ resp = null⌝ }} := by
  iintro %Φ ⟨#Pc, #Hkv, #Hrpc, #Hctx, #Hce, #Hopts, #Hc0, #Hdq, #HF, #Hek⟩ HΦ
  ihave #Hctx' := ctxOk_of_isContext ci cd $$ Hctx
  iclear Hctx
  ihave #Hopts' := optsAt_res sl [] iprop(True) $$ Hopts
  ihave #Hek' : emptyKeyIf (opGetModel key []).key $$ [Hek]
  · rw [show (opGetModel key []).key = key from rfl]; iexact Hek
  iapply (v3.kv.wp_Get api addr ci cd key sl [] iprop(True) (etcdRangeSpec E γr cid mid)
    (rangeReplyOk E γr c F (txn.rangeOpOf key [] (W64 0) (W64 0) (W32 0) (W32 0) false false false
      (W64 0) (W64 0) (W64 0) (W64 0)) cid mid Q)) $$ []
  · iframe #
    isplitl []
    · rw [show (opGetModel key []).base.sortSet = false from rfl]
      iapply sortNamesIf_false
    isplitl []
    · ipureintro
      refine ⟨?_, rfl⟩
      unfold opGetPanics opFold OpFull.newOp
      simp
    · have Hw : rangeWireOf (opGetModel key []) = txn.rangeOpOf key [] (W64 0) (W64 0) (W32 0)
          (W32 0) false false false (W64 0) (W64 0) (W64 0) (W64 0) := rfl
      rw [Hw]
      imodintro
      inext
      unfold etcdRangeSpec
      iexists c, F, Q
      iframe Hc0 HF
      isplitr
      · icases Hdq with (%HQ | #Hau)
        · ileft; ipureintro; exact HQ
        · iright
          isplitr
          · ipureintro; rfl
          iexact Hau
      iintro %m Hm
      iexact Hm
  inext
  iintro %resp %err ⟨-, Hout⟩
  iapply HΦ
  iunfold rangeCallOut at Hout
  icases Hout with (⟨%Herr, %m, Hm, Hq⟩ | ⟨%Herr, -⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m
    iframe
  · iright
    ipureintro; exact ⟨Herr.1, Herr.2.2⟩

/-- **`client_delete_end_to_end`** (the vertical slice's unit V2; as `client_put_end_to_end`):
`kv.Delete(ctx, key)` with no options on a `*kv` over a connection to the server at `addr` whose
`DeleteRange` is registered with etcd's spec, by a client with the floor `F`: `nil` and the
reply's message `m` with `deleteReplied` for the delete of `key` the server decodes (the key
alone, no previous key-values) and (2026-10-15, unit T2) `□ Q` of the state at which the caller's
persistent update over the whole state, `kvOpAu (.deleteRange (txn.deleteOpOf key [] false)) Q`,
linearized the delete (unit W-M3: in `deleteReplied`, the state of the log the delete met); or an
error and no reply. -/
theorem client_delete_end_to_end (api : Loc) (addr : GoString) (E : apply.AEnv GF)
    (γr : ReadNames) (cid mid : w64) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (key : GoString) (sl : GoSlice) (Q : KVState → IProp GF) (F : mvcc.Log) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kvObjAt api addr ∗
        isGrpcRpc addr go!"/etcdserverpb.KV/DeleteRange" (etcdDeleteSpec E γr cid mid) ∗
        context.isContext ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗ mvcc.idxCert E.γ.idx F ∗
        kvOpAu γr.kv (.deleteRange (txn.deleteOpOf key [] false)) Q ∗ emptyKeyIf key }}
      (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
          go!"Delete")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : DelRespM, delRespMsg resp m ∗
            deleteReplied E γr F (txn.deleteOpOf key [] false) Q cid mid m) ∨
          ⌜err ≠ GoInterface.nil ∧ resp = null⌝ }} := by
  iintro %Φ ⟨#Pc, #Hkv, #Hrpc, #Hctx, #Hce, #Hopts, #HF, #Hnp, #Hek⟩ HΦ
  ihave #Hctx' := ctxOk_of_isContext ci cd $$ Hctx
  iclear Hctx
  ihave #Hek' : emptyKeyIf (opDeleteModel key []).key $$ [Hek]
  · rw [show (opDeleteModel key []).key = key from rfl]; iexact Hek
  iapply (v3.kv.wp_Delete api addr ci cd key sl [] (etcdDeleteSpec E γr cid mid)
    (fun m => iprop(deleteReplied E γr F (txn.deleteOpOf key [] false) Q cid mid m))) $$ []
  · iframe #
    isplitl []
    · ipureintro
      refine ⟨?_, rfl⟩
      simp [opGetModel, opFold, OpFull.getInit, OpFull.newOp, OpModel.zero, opDeleteModel,
        OpFull.deleteInit, opDeletePanics, opGetPanics, OpFull.deletePanics]
    · have Hw : deleteWireOf (opDeleteModel key []) = txn.deleteOpOf key [] false := rfl
      rw [Hw]
      imodintro
      inext
      unfold etcdDeleteSpec
      iexists F
      iframe HF
      iexists Q
      isplitr
      · ipureintro; simp [txn.deleteOpOf]
      isplitr
      · iexact Hnp
      iintro %m Hm
      iexact Hm
  inext
  iintro %resp %err Hout
  iapply HΦ
  iunfold deleteCallOut at Hout
  icases Hout with (⟨%Herr, %m, Hm, Hq⟩ | ⟨%Herr, -⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m
    iframe
  · iright
    ipureintro; exact ⟨Herr.1, Herr.2.2⟩

/-- **`client_txn_end_to_end`** (the vertical slice's unit V2): `Commit()` of the client's
transaction builder at the state `b` (`txnObjAt`: from `kv.Txn` on a `*kv` over a connection to
the server at `addr`, then `If`/`Then`/`Else`), whose operations are plain (as `Then`'s and
`Else`'s are, from `txnOpOf`: `txnOpOf_plain`) and, if read-only, within the txn package's model
(`txnModelIn`), with `Txn` registered with etcd's spec, by a client that knows the committed index
`c` and has the floor `F`: `nil` and the reply's message `m` with `txnReplied` at `c` and `F` for
the transaction the server decodes (`txnWireOf b.model`), with (2026-10-15, unit T2) `□ Q` of the
state at which the caller's persistent update over the whole state, `kvOpAu (.txn (txnWireOf
b.model)) Q`, linearized a writing transaction (plain in the KV model, `txn.txnPlain`, no range end
`[0]`; a read-only one takes no update, `Q` trivial; unit W-M3: in `txnReplied`, the state of
the log the transaction met); or an error and no reply. -/
theorem client_txn_end_to_end (tp : Loc) (addr : GoString) (E : apply.AEnv GF) (γw γr : ReadNames)
    (c cid mid : w64) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (b : TxnBuild)
    (F : mvcc.Log) (Q : KVState → IProp GF) (hp : TxnModel.plain b.model)
    (hin : txnModelIn (txnWireOf b.model)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ txnObjAt tp addr ci cd b ∗
        isGrpcRpc addr go!"/etcdserverpb.KV/Txn" (etcdTxnSpec E γw γr cid mid) ∗
        committedAtLeast γr c ∗ mvcc.idxCert E.γ.idx F ∗
        (⌜txn.txnReadonly (txnWireOf b.model) = true ∧ Q = fun _ => iprop(True)⌝ ∨
          (⌜txn.txnReadonly (txnWireOf b.model) = false ∧ txn.txnPlain (txnWireOf b.model) ∧
            txnNoZeroEnd (txnWireOf b.model)⌝ ∗ kvOpAu γw.kv (.txn (txnWireOf b.model)) Q)) }}
      (App (Val (tp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"Commit"))
        (Val #()))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : TxnRespM, txnRespMsg resp m ∗
            txnReplied E γw γr c F (txnWireOf b.model) Q cid mid m) ∨
          ⌜err ≠ GoInterface.nil ∧ resp = null⌝ }} := by
  iintro %Φ ⟨#Pc, Hobj, #Hrpc, #Hc0, #HF, #Hnp⟩ HΦ
  iapply (v3.txn.wp_Commit tp addr ci cd b (etcdTxnSpec E γw γr cid mid)
    (fun m => iprop(txnReplied E γw γr c F (txnWireOf b.model) Q cid mid m))) $$ [Hobj]
  · iframe
    iframe #
    imodintro
    inext
    unfold etcdTxnSpec
    isplitl []
    · ipureintro; exact ⟨txnWireOf_plain _ hp, hin⟩
    iexists Q
    isplitr
    · icases Hnp with (#H | #H)
      · ileft; iexact H
      · iright; iright; iexact H
    iexists c, F
    iframe #
    iintro %m Hm
    iexact Hm
  inext
  iintro %resp %err Hout
  iapply HΦ
  iunfold txnCallOut at Hout
  icases Hout with (⟨%Herr, %m, Hm, Hq⟩ | ⟨%Herr, -⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m
    iframe
  · iright
    ipureintro; exact ⟨Herr.1, Herr.2.2⟩

/-- **`client_get_after_put`** (unit C2a, 2026-10-14; see the file header): after a `kv.Put(ctx,
key, val)` that returned `nil` with the reply `mp` (`putReplyOk E γr`, `client_put_end_to_end`),
`kv.Get(ctx', key)` with no options on a `*kv` over a connection to the server at `addr` whose
`Range` is registered with etcd's spec at the same read names (`etcdRangeSpec E γr`): `nil` and the
reply's message `m` reading the put (`getAfterPutOk`: at a log extending the put's, its revision at
least the put's; the put's value if no later revision touched the key); or an error and no reply.
The get is linearizable: it asks the read index at the put's committed index (`appliedWit`'s `i`,
`committedAtLeast γr i`), so the log it reads extends the log applied through some index at least
`i` (`readLogOk`), which extends the put's (`appliedMono`). -/
theorem client_get_after_put (api : Loc) (addr : GoString) (E : apply.AEnv GF) (γr : ReadNames)
    (cid mid : w64) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (key val : GoString) (sl : GoSlice) (Fp : mvcc.Log) (mp : PutRespM) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kvObjAt api addr ∗
        isGrpcRpc addr go!"/etcdserverpb.KV/Range" (etcdRangeSpec E γr cid mid) ∗
        context.isContext ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
        putReplyOk E γr Fp (putKeyOp key val) cid mid mp ∗ emptyKeyIf key }}
      (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
          go!"Get")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : RangeRespM, rangeRespMsg resp m ∗
            getAfterPutOk E key val cid mid mp m) ∨
          ⌜err ≠ GoInterface.nil ∧ resp = null⌝ }} := by
  iintro %Φ ⟨#Pc, #Hkv, #Hrpc, #Hctx, #Hce, #Hopts, #Hput, #Hek⟩ HΦ
  iunfold putReplyOk at Hput
  icases Hput with ⟨%hm, %x, %x', %lp, %skip, %Hpp, #Hcx, #Hwit, -⟩
  iunfold appliedWit at Hwit
  icases Hwit with ⟨%i, #Hci, #HLi, #Hmono⟩
  have hx' := put_applied_log (putKeyOp key val) hm x x' lp skip Hpp.1
  iapply wp_fupd
  iapply (client_get_end_to_end api addr E γr i cid mid ci cd key sl (fun _ => iprop(True))
    x'.log) $$ []
  · iframe #
    ileft; ipureintro; rfl
  inext
  iintro %resp %err Hout
  icases Hout with (⟨%Herr, %m, Hm, #Hq⟩ | %Herr)
  · iunfold rangeReplyOk at Hq
    rw [show (txn.rangeOpOf key [] (W64 0) (W64 0) (W32 0) (W32 0) false false false (W64 0)
      (W64 0) (W64 0) (W64 0)).base.serializable = false from rfl]
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hq with ⟨%l, #Hcl, -, %Hl, #Hrl, -⟩
    iunfold readLogOk at Hrl
    icases Hrl with ⟨-, %ci₀, %L₀, %Hci₀, #HL₀, %HpL⟩
    iunfold appliedMono at Hmono
    imod Hmono $$ %i %ci₀ %x'.log %L₀ %Hci₀ HLi HL₀ with %Hmo
    ihave %Hcxl := mvcc.idxCert_prefix E.γ.idx x'.log l $$ [Hcx Hcl]
    · iframe Hcx Hcl
    imodintro
    iapply HΦ
    ileft
    isplitr
    · ipureintro; exact Herr
    iexists m
    iframe Hm
    iunfold getAfterPutOk
    iexists hm, x, x', lp, skip, l
    iframe Hcl
    ipureintro
    obtain ⟨hlen, hlen', hrev, hcid, hmid, -, hcount, hsel, -⟩ := Hl
    have hpre : x'.log <+: l := Hmo.trans HpL
    have hst : mvcc.stateAt l (sint.nat (mvcc.rangeRev m.hdr.revision (getKeyOp key).base.rev)) =
        mvcc.stateAfter l := by
      have h1 : mvcc.rangeRev m.hdr.revision (getKeyOp key).base.rev = m.hdr.revision := by
        simp [mvcc.rangeRev, txn.rangeOpOf]
      rw [h1, hrev]
      have h2 : sint.nat (W64 ((l.length : Int) - 1)) = l.length - 1 := by
        unfold sint.nat; word
      rw [h2, mvcc.stateAt_last]
    rw [hst] at hcount hsel
    have hxl : x'.log.length ≤ l.length := hpre.length_le
    have hxlen : x'.log.length = x.log.length + 1 := by rw [hx']; simp
    refine ⟨Hpp.1, hx', Hpp.2.1, hpre, hlen, hlen', hrev, hcid, hmid, ?_, hcount, hsel,
      fun hno => get_after_put_kvs key val x x' l m.kvs m.more hx' hpre hsel hno⟩
    rw [Hpp.2.1, hrev]
    word
  · imodintro
    iapply HΦ
    iright
    ipureintro; exact Herr

/-- **What a linearizable `Get` returns** (2026-10-14, unit T1; 2026-10-15, unit T2: the whole
state): the client's update `Q` was fired at a state `σ` (`□ Q σ`) whose value of the key is the
reply's (its first key-value's) and whose current revision is the reply's header revision. -/
theorem client_get_value (E : apply.AEnv GF) (γr : ReadNames) (c cid mid : w64) (key : GoString)
    (F : mvcc.Log) (Q : KVState → IProp GF) (m : RangeRespM) :
    rangeReplyOk E γr c F (getKeyOp key) cid mid Q m ⊢
      ∃ σ : KVState, □ Q σ ∗ ⌜m.kvs.head?.map EtcdKv.value = (mvcc.findKey key σ.kvs).map EtcdKv.value ∧
        m.hdr.revision = W64 (σ.rev : Int)⌝ := by
  iintro #H
  iunfold rangeReplyOk at H
  icases H with ⟨%l, -, -, %Hl, -, #HQ⟩
  have hs : (getKeyOp key).base.serializable = false := rfl
  have hk : (getKeyOp key).key = key := rfl
  simp only [hs, hk, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨hlen, hlen', hrev, -, -, -, -, hsel, -⟩ := Hl
  have hst : mvcc.stateAt l (sint.nat (mvcc.rangeRev m.hdr.revision (getKeyOp key).base.rev)) =
      mvcc.stateAfter l := by
    have h1 : mvcc.rangeRev m.hdr.revision (getKeyOp key).base.rev = m.hdr.revision := by
      simp [mvcc.rangeRev, txn.rangeOpOf]
    rw [h1, hrev]
    have h2 : sint.nat (W64 ((l.length : Int) - 1)) = l.length - 1 := by
      unfold sint.nat; word
    rw [h2, mvcc.stateAt_last]
  rw [hst] at hsel
  iexists kvStateOf l
  iframe HQ
  ipureintro
  refine ⟨getKey_value key l m.kvs m.more hsel, ?_⟩
  rw [hrev]
  unfold kvStateOf
  simp only
  congr 1
  omega

/-- **What a linearizable range returns** (2026-10-15, unit T2): for a range at the latest
revision (`rev = 0`), the client's read update `Q` was fired at a state `σ` (`□ Q σ`) whose
selection is the reply's key-values (`srvRangeOk`: the server's selection, sorted and limited as
asked), whose count is the reply's, and whose current revision is the reply's header revision. -/
theorem rangeReply_state (E : apply.AEnv GF) (γr : ReadNames) (c cid mid : w64) (o : OpFull)
    (F : mvcc.Log) (Q : KVState → IProp GF) (m : RangeRespM)
    (hser : o.base.serializable = false) (hrev : o.base.rev = W64 0) :
    rangeReplyOk E γr c F o cid mid Q m ⊢
      ∃ σ : KVState, □ Q σ ∗ ⌜m.hdr.revision = W64 (σ.rev : Int) ∧
        txn.srvRangeOk o σ.kvs m.kvs m.more ∧ m.count = txn.srvCount o σ.kvs true⌝ := by
  iintro #H
  iunfold rangeReplyOk at H
  simp only [hser, Bool.false_eq_true, ↓reduceIte]
  icases H with ⟨%l, -, -, %Hl, -, #HQ⟩
  obtain ⟨hlen, hlen', hr, -, -, -, hcount, hsel, -⟩ := Hl
  have hst : mvcc.stateAt l (sint.nat (mvcc.rangeRev m.hdr.revision o.base.rev)) =
      mvcc.stateAfter l := by
    have h1 : mvcc.rangeRev m.hdr.revision o.base.rev = m.hdr.revision := by
      simp [mvcc.rangeRev, hrev]
    rw [h1, hr]
    have h2 : sint.nat (W64 ((l.length : Int) - 1)) = l.length - 1 := by
      unfold sint.nat; word
    rw [h2, mvcc.stateAt_last]
  rw [hst] at hsel hcount
  iexists kvStateOf l
  iframe HQ
  ipureintro
  refine ⟨?_, hsel, hcount⟩
  rw [hr]
  unfold kvStateOf
  simp only
  congr 1
  omega

/-- **`client_range_end_to_end`** (2026-10-15, unit T2): `kv.Get(ctx, key, opts...)` with any
options that keep it a range (`opGetModel key gs`, e.g. `WithRange`, `WithPrefix`, `WithLimit`,
`WithSort`) on a `*kv` over a connection to the server at `addr` whose `Range` is registered with
etcd's spec, by a client that knows the committed index `c`, with its persistent read update over
the whole state `kvReadAu γr.kv Q` (a linearizable range; or none, `Q` trivial): `nil` and the
reply's message `m` with `rangeReplyOk` for the range the server decodes (`rangeWireOf`; at the
latest revision, `rangeReply_state` gives `□ Q σ` of the state whose selection the reply is); or an
error and no reply. -/
theorem client_range_end_to_end (api : Loc) (addr : GoString) (E : apply.AEnv GF)
    (γr : ReadNames) (c cid mid : w64) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (key : GoString) (sl : GoSlice) (gs : List (OpFull → OpFull)) (R : IProp GF)
    (Q : KVState → IProp GF) (F : mvcc.Log) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kvObjAt api addr ∗
        isGrpcRpc addr go!"/etcdserverpb.KV/Range" (etcdRangeSpec E γr cid mid) ∗
        context.isContext ci cd ∗ ctxErrClient ci cd ∗ optsAtRes sl gs R ∗ R ∗
        sortNamesIf (opGetModel key gs).base.sortSet ∗ emptyKeyIf (opGetModel key gs).key ∗
        ⌜¬ opGetPanics gs ∧ (opGetModel key gs).t = W64 1⌝ ∗ committedAtLeast γr c ∗
        (⌜Q = fun _ => iprop(True)⌝ ∨
          (⌜(rangeWireOf (opGetModel key gs)).base.serializable = false⌝ ∗ kvReadAu γr.kv Q)) ∗
        mvcc.idxCert E.γ.idx F }}
      (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
          go!"Get")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); R ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ m : RangeRespM, rangeRespMsg resp m ∗
            rangeReplyOk E γr c F (rangeWireOf (opGetModel key gs)) cid mid Q m) ∨
          ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }} := by
  iintro %Φ ⟨#Pc, #Hkv, #Hrpc, #Hctx, #Hce, Hopts, HR, Hsn, Hek, %Hg, #Hc0, #Hdq, #HF⟩ HΦ
  ihave #Hctx' := ctxOk_of_isContext ci cd $$ Hctx
  iclear Hctx
  iapply (v3.kv.wp_Get api addr ci cd key sl gs R (etcdRangeSpec E γr cid mid)
    (rangeReplyOk E γr c F (rangeWireOf (opGetModel key gs)) cid mid Q)) $$ [Hopts HR Hsn Hek]
  · iframe #
    iframe Hopts HR Hsn Hek
    isplitl []
    · ipureintro; exact Hg
    · imodintro
      inext
      unfold etcdRangeSpec
      iexists c, F, Q
      iframe Hc0 HF Hdq
      iintro %m Hm
      iexact Hm
  inext
  iintro %resp %err ⟨HR, Hout⟩
  iapply HΦ
  iframe HR
  iunfold rangeCallOut at Hout
  icases Hout with (⟨%Herr, %m, Hm, Hq⟩ | ⟨%Herr, -⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m
    iframe
  · iright
    ipureintro; exact ⟨Herr.1, Herr.2.2⟩

end proofs

section watch_stub
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **The generated Watch stub** (`watchClient.Watch`, linked; unit W-W): on a connection to a
server at `addr` that serves the method with the stream specification `Spec` and the client's
content `Up` (`isGrpcStream`, `etcd_watch_served` for etcd's server), it returns the client end
of a fresh watch stream (`v3rpc.cliWatchStreamIs`, both tokens at `[]`, `Spec γ Dn`), or a `nil`
stream and a client error; over grpc's `ClientConn.NewStream` and the generic client-stream
wrapper's methods (axioms). What the client's `watch.go` (unit W-C) uses. -/
theorem watchClient_Watch : EtcdGrove.watchClient.Watch.spec (GF := GF) (hG := hG) :=
  watchClient.wp_Watch

end watch_stub

section watcher
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **etcd's client's watcher meets the clients' range-watch contract** (unit W-C; the closable
one, `isEtcdRangeWatcher`, `cache/v3/InvEtcdTxn.lean`) at the server's model
(`v3rpc.etcdModelOfServer V.R.E`): `isEtcdRangeWatcher_of_watcher` at the linked
`watcher.Watch` (`watch.go`'s `Watch`, `run`, `serveSubstream`, ..., over the generated stub
`watchClient_Watch`). The watcher `isClientWatcher V w` rests on `watchConnFacts V`: the
registration `isGrpcStream … (watchUp V.R.γ) (watchSpec V.R)` at the connection's address, what
`v3rpc.etcd_watch_served_etcd_chain` gives for etcd's server; of the server facts W-C assumed,
S2 `srvProgressAllAnswers` and S3 `srvEventIdsAssigned` are theorems since unit W-M2
(`srvProgressAllAnswers_holds`, `srvEventIdsAssigned_holds`), and S4 since units W-M2b and W-M3:
the events are of a watched log (`mvcc.evLog`): sealed (`mvcc.idxSealed`, over which the clients'
model's `etcdState`/`EtcdStep` are stated) and certified by the apply thread before the store
notifies it (`certOk`, over which `etcdReached` is stated: the KV model of a committed raft
prefix), so a watch event's revision is reached (`ev_ok`); the remaining premises are the wire's,
`srvNoDupKeys`
(`issues/etcd-txn-check-intervals-sibling.md`), `noRetryableStreamErr` (the reconnection excluded:
`issues/etcd-watch-resume-closing-substream.md`), the watch-token supply, `srvLogsSmall`
(`srvLogsSmall_of_read`) and `V.R.γ.st = V.R.E.γ` (`watchSrvLink_of_server`). -/
theorem client_watcher_rangeWatcher (V : WEnv GF) (w : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.context ∗ isClientWatcher V w ⊢
    isEtcdRangeWatcher (EM := V.EM) (watcherIfaceOf w) V.pfx :=
  isEtcdRangeWatcher_of_watcher v3.watcher.wp_Watch V w

/-- **`NewWatcher(c)` returns a range watcher** (unit W-C): over a client `c` whose connection
satisfies `watchConnFacts V`, `NewWatcher` (linked) returns the `Watcher` interface of a
`*watcher` meeting the clients' closable range-watch contract at the server's model. -/
theorem client_newWatcher_rangeWatcher (V : WEnv GF) (c : Loc) (callSl : GoSlice)
    (vs : List GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
        isPkgInit (PROP := IProp GF) pkg_id.context ∗
        watchConnFacts V ∗ ⌜c ≠ null⌝ ∗
        structFieldRef go_etcd_io.etcd.client.v3.Client go!"conn" c ↦□ V.conn ∗
        structFieldRef go_etcd_io.etcd.client.v3.Client go!"callOpts" c ↦□ callSl ∗
        callSl ↦*□ vs ∗ callOptsOk vs ∗ isClientLogger c ∗ ⌜threadBound GF ≤ 2 ^ 31⌝ }}
      (App (Val (@! go_etcd_io.etcd.client.v3.NewWatcher)) (Val #c))
    {{ (wi : GoInterface), RET #wi; ∃ (w : Loc),
        ⌜wi = GoInterface.ok (watcherIfaceOf w)⌝ ∗
        isEtcdRangeWatcher (EM := V.EM) (watcherIfaceOf w) V.pfx }} := by
  iintro %Φ ⟨#P1, #P2, #P3, #Hf, %Hc, #Hconn, #Hcall, #Hvs, #Hok, #Hlg, %Hb⟩ HΦ
  iapply (v3.wp_NewWatcher V c callSl vs) $$ [] [HΦ]
  · iframe #; ipureintro; exact ⟨Hc, Hb⟩
  · iintro !> %wi ⟨%w, %wc, %lg, %Hwi, Hw⟩
    iapply HΦ
    iexists w
    isplitr; · ipureintro; exact Hwi
    iapply (client_watcher_rangeWatcher { V with wc := wc, lg := lg } w) $$ [Hw]
    iframe #; iexact Hw

end watcher

end client

#print axioms Perennial.EtcdGrove.client.client_get_value
#print axioms Perennial.EtcdGrove.client.rangeReply_state
#print axioms Perennial.EtcdGrove.client.client_range_end_to_end
#print axioms Perennial.EtcdGrove.client.client_put_end_to_end
#print axioms Perennial.EtcdGrove.client.client_get_end_to_end
#print axioms Perennial.EtcdGrove.client.client_get_after_put
#print axioms Perennial.EtcdGrove.client.client_delete_end_to_end
#print axioms Perennial.EtcdGrove.client.client_txn_end_to_end
#print axioms Perennial.EtcdGrove.client.etcd_txnHandlerOk
#print axioms Perennial.EtcdGrove.client.etcd_txnMethodOk
#print axioms Perennial.EtcdGrove.client.get_after_put_kvs
#print axioms Perennial.EtcdGrove.client.etcd_putHandlerOk
#print axioms Perennial.EtcdGrove.client.etcd_rangeHandlerOk
#print axioms Perennial.EtcdGrove.client.etcd_deleteHandlerOk
#print axioms Perennial.EtcdGrove.client.etcd_putMethodOk
#print axioms Perennial.EtcdGrove.client.etcd_rangeMethodOk
#print axioms Perennial.EtcdGrove.client.etcd_deleteMethodOk
#print axioms Perennial.EtcdGrove.client.etcd_kv_served
#print axioms Perennial.EtcdGrove.client.watchClient_Watch
#print axioms Perennial.EtcdGrove.client.client_watcher_rangeWatcher
#print axioms Perennial.EtcdGrove.client.client_newWatcher_rangeWatcher
#print axioms Perennial.EtcdGrove.client.v3.kv.wp_Put
#print axioms Perennial.EtcdGrove.client.v3.kv.wp_Get
#print axioms Perennial.EtcdGrove.client.v3.kv.wp_Do
#print axioms Perennial.EtcdGrove.client.v3.kv.wp_GetStream
#print axioms Perennial.EtcdGrove.client.v3.wp_NewKV
#print axioms Perennial.EtcdGrove.client.v3.wp_ContextError

end EtcdGrove
end Perennial
