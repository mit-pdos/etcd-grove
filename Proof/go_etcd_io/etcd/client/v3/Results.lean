/-
**The client meets the server** (unit C1, 2026-10-14; over the generic gRPC specification since
2026-10-14): the client's `kv.Put` and `kv.Get` on a `KV` made by `NewKV` over a connection to a
gRPC server, end to end through the transport (grpc's `ClientConn.Invoke`, the client side of the
trust boundary: `Spec/google_golang_org/grpc/ClientConn__Invoke.lean`; since unit P3a the
interceptor chain over grpc's invoker, which makes one attempt, the client's retry interceptor
proved and assumed of the connection, `isEtcdConn`, through `kvObjAt`:
`client/v3/EtcdInvoke.lean`), and etcd's gRPC handlers
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
is `etcdGrpcSlot` (`etcdRunSlot`, the quota check's reader slots of `lgMu` and `bemu`
(`v3rpc.quotaRd`), the log interceptor's of `lgMu`).

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
  for the get of `key`; or an error. `client_range_end_to_end` (any range options),
  `client_delete_end_to_end`, `client_txn_end_to_end` likewise.
* **`client_put_any`, `client_range_any`, `client_delete_any`, `client_txn_any`** (the client's
  calls, one family: "The client's KV calls" below): the same through a client of several
  members, each with its own registrations, the reply some member's; a write's update persistent
  or fired at most once (refusal-free members). The `client_*_end_to_end` results are their
  instances at one server's addresses.
* **`client_get_after_put`** (unit C2a, 2026-10-14; one server): after a `Put` of `key ↦ val`
  that returned `nil` (its reply's `putReplyOk E γr`, `client_put_end_to_end`'s `putReplied` with
  its token and its update's result dropped; with the witness `appliedWit γr` of the
  log after: applied through an index `i` of the committed log), `kv.Get(ctx', key)` with `Range`
  registered at the same read names: `nil` and a reply `m` that reads the put (`getAfterPutOk`:
  at a certified log extending the put's log after, its revision at least the put's; and, if no
  later revision touched `key`, exactly the put's key-value, `get_after_put_kvs`); or an error.
  The `Get` asks the read index at `i` (`committedAtLeast γr i`), so `readLogOk` gives a log
  extending the log applied through some index `≥ i`, which extends the put's (`appliedMono`).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.Link
public import Proof.go_etcd_io.etcd.client.v3.KVService
public import Proof.go_etcd_io.etcd.client.v3.LinkMembers
public import Proof.go_etcd_io.etcd.client.v3.ServerWatcher
public import Proof.go_etcd_io.etcd.client.v3.LeaseClient
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Results
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.QuotaLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.QuotaLeaseLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Link

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
        exact go.goStringLt_irrefl _ hlt
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

/-- A delete's count: `delCountT` and `v3rpc.delCount` agree (nested transactions included). -/
theorem delCount_toTxnOps (us : List v3rpc.ReqOp) (ops : List TxnOp)
    (h : v3rpc.ReqOp.toTxnOps us = some ops) : v3rpc.delCount us = delCountT ops := by
  induction us using v3rpc.delCount.induct generalizing ops with
  | case1 => simp only [v3rpc.ReqOp.toTxnOps, Option.some.injEq] at h; subst h; simp [v3rpc.delCount, delCountT]
  | case2 o us ih =>
    simp only [v3rpc.ReqOp.toTxnOps, v3rpc.ReqOp.toTxnOp] at h
    cases hb : v3rpc.ReqOp.toTxnOps us <;> simp only [hb] at h <;> try cases h
    simp only [v3rpc.delCount, delCountT, ih _ hb]
  | case3 cs ts es us ih1 ih2 ih3 =>
    simp only [v3rpc.ReqOp.toTxnOps, v3rpc.ReqOp.toTxnOp] at h
    cases ha : v3rpc.ReqOp.toTxnOps ts <;> cases hb : v3rpc.ReqOp.toTxnOps es <;>
      cases hc : v3rpc.ReqOp.toTxnOps us <;> simp only [ha, hb, hc] at h <;> try cases h
    simp only [v3rpc.delCount, delCountT, ih1 _ ha, ih2 _ hb, ih3 _ hc]
  | case4 u us hd ht ih =>
    simp only [v3rpc.ReqOp.toTxnOps] at h
    cases ha : v3rpc.ReqOp.toTxnOp u <;> cases hb : v3rpc.ReqOp.toTxnOps us <;>
      simp only [ha, hb] at h <;> try cases h
    rename_i a b
    have e : v3rpc.delCount (u :: us) = v3rpc.delCount us := by
      cases u with
      | delete o => exact absurd rfl (hd o)
      | txn cs ts es => exact absurd rfl (ht cs ts es)
      | _ => simp [v3rpc.delCount]
    have e' : delCountT (a :: b) = delCountT b := by
      cases u with
      | delete o => exact absurd rfl (hd o)
      | txn cs ts es => exact absurd rfl (ht cs ts es)
      | range o => simp only [v3rpc.ReqOp.toTxnOp, Option.some.injEq] at ha; subst ha; simp [delCountT]
      | put o =>
        simp only [v3rpc.ReqOp.toTxnOp, Option.some.injEq] at ha; subst ha
        unfold txn.putTxnOp
        by_cases h1 : o.ignoreValue = true <;> by_cases h2 : o.ignoreLease = true <;> simp [h1, h2, delCountT]
      | empty => simp [v3rpc.ReqOp.toTxnOp] at ha
    rw [e, e', ih _ hb]

section bridge
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

mutual
/-- **An operation of the server's copy is the handler's request operation** (nested ones
included, recursively): the txn package's `requestOpIs` of an operation is `v3rpc.reqOpIs` of a
request operation whose model it is. -/
theorem reqOp_of_requestOp (p : Loc) : ∀ op : TxnOp,
    txn.requestOpIs (GF := GF) p op ⊢ ∃ u : v3rpc.ReqOp, v3rpc.reqOpIs p u ∗ ⌜v3rpc.ReqOp.toTxnOp u = some op⌝
  | .txn cs ts es => by
    iintro #H
    iunfold txn.requestOpIs at H
    icases H with ⟨%Hn, %w, %r, #Hu, #Hw, %Hr, %csl, %ssl, %fsl, %cps, %sps, %fps, #Hc, #Hcs, #Hcm,
      #Hs, #Hss, #Hsm, #Hf, #Hfs, #Hfm⟩
    ihave ⟨%ts', #Hts, %Hts'⟩ := reqOps_of_requestOps sps ts $$ Hsm
    ihave ⟨%es', #Hes, %Hes'⟩ := reqOps_of_requestOps fps es $$ Hfm
    iexists (v3rpc.ReqOp.txn cs ts' es')
    isplitl
    · unfold v3rpc.reqOpIs
      imodintro
      isplitl
      · ipureintro; exact Hn
      iexists w, r
      isplitl []; · iexact Hu
      isplitl []; · iexact Hw
      isplitl []; · ipureintro; exact Hr
      iexists csl, ssl, fsl, cps, sps, fps
      iframe #
    · ipureintro; simp [v3rpc.ReqOp.toTxnOp, Hts', Hes']
  | .get o => by
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
  | .delete o => by
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
  | .put k v l => by
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
  | .putKeep k l => by
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
  | .putIgnVal k l => by
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

/-- **The operations of the server's copy are the handler's request operations** (in order). -/
theorem reqOps_of_requestOps : ∀ (ps : List Loc) (ops : List TxnOp),
    txn.requestOpsIs (GF := GF) ps ops ⊢
      ∃ us : List v3rpc.ReqOp, v3rpc.reqOpsIs ps us ∗ ⌜v3rpc.ReqOp.toTxnOps us = some ops⌝
  | [], [] => by
    iintro -
    iexists []
    unfold v3rpc.reqOpsIs
    isplitl; · itrivial
    ipureintro; rfl
  | p :: ps, op :: ops => by
    iintro H
    iunfold txn.requestOpsIs at H
    icases H with ⟨H1, H2⟩
    ihave ⟨%u, H1, %Hu⟩ := reqOp_of_requestOp p op $$ H1
    ihave ⟨%us, H2, %Hus⟩ := reqOps_of_requestOps ps ops $$ H2
    iexists u :: us
    rw [v3rpc.reqOpsIs.eq_2]
    iframe H1 H2
    ipureintro
    simp [v3rpc.ReqOp.toTxnOps, Hu, Hus]
  | [], _ :: _ => by iintro H; iunfold txn.requestOpsIs at H; iexfalso; iexact H
  | _ :: _, [] => by iintro H; iunfold txn.requestOpsIs at H; iexfalso; iexact H
end

/-- `delWireAtT` is persistent. -/
instance delWireAtT_persistent (p : Loc) (op : TxnOp) :
    Persistent (delWireAtT (GF := GF) p op) := by
  cases op <;> unfold delWireAtT <;> infer_instance

/-- `delWiresAtT` is persistent. -/
instance delWiresAtT_persistent (ps : List Loc) (ops : List TxnOp) :
    Persistent (delWiresAtT (GF := GF) ps ops) := by
  induction ops generalizing ps with
  | nil => cases ps <;> unfold delWiresAtT <;> infer_instance
  | cons op ops ih => cases ps <;> unfold delWiresAtT <;> infer_instance

mutual
/-- `delWiresAtT_reqOpsWire` at one operation. -/
theorem delWireAtT_reqOpWire (p : Loc) : ∀ (u : v3rpc.ReqOp) (op : TxnOp),
    v3rpc.ReqOp.toTxnOp u = some op → delWireAtT (GF := GF) p op ⊢ v3rpc.reqOpWire p u
  | .delete o, op, h => by
    simp only [v3rpc.ReqOp.toTxnOp, Option.some.injEq] at h; subst h
    unfold delWireAtT v3rpc.reqOpWire
    exact .rfl
  | .txn cs ts es, op, h => by
    simp only [v3rpc.ReqOp.toTxnOp] at h
    cases ha : v3rpc.ReqOp.toTxnOps ts <;> cases hb : v3rpc.ReqOp.toTxnOps es <;>
      simp only [ha, hb] at h <;> try cases h
    rename_i a b
    unfold delWireAtT v3rpc.reqOpWire
    iintro #H
    iintro !> %w %r %ssl %fsl %sps %fps #H1 #H2 #H3 #H4 #H5 #H6
    ihave ⟨#A, #B⟩ := H $$ %w %r %ssl %fsl %sps %fps H1 H2 H3 H4 H5 H6
    isplitl
    · iapply delWiresAtT_reqOpsWire sps ts a ha $$ A
    · iapply delWiresAtT_reqOpsWire fps es b hb $$ B
  | .range _, _, _ => by unfold v3rpc.reqOpWire; iintro -; itrivial
  | .put _, _, _ => by unfold v3rpc.reqOpWire; iintro -; itrivial
  | .empty, _, _ => by unfold v3rpc.reqOpWire; iintro -; itrivial

/-- **The client's wire facts of a transaction's operations are the handler's** (`notes/txn-nested.md`,
L12): `delWiresAtT` of the model is `v3rpc.reqOpsWire` of the request operations whose model it is. -/
theorem delWiresAtT_reqOpsWire (ps : List Loc) (us : List v3rpc.ReqOp) (ops : List TxnOp)
    (h : v3rpc.ReqOp.toTxnOps us = some ops) :
    delWiresAtT (GF := GF) ps ops ⊢ v3rpc.reqOpsWire ps us :=
  match ps, us, ops, h with
  | [], [], _, _ => by iintro -; unfold v3rpc.reqOpsWire; itrivial
  | [], _ :: _, _, _ => by iintro -; unfold v3rpc.reqOpsWire; itrivial
  | _ :: _, [], _, _ => by iintro -; unfold v3rpc.reqOpsWire; itrivial
  | p :: ps, u :: us, ops, h => by
    simp only [v3rpc.ReqOp.toTxnOps] at h
    cases ha : v3rpc.ReqOp.toTxnOp u <;> cases hb : v3rpc.ReqOp.toTxnOps us <;>
      simp only [ha, hb] at h <;> try cases h
    rename_i a b
    rw [v3rpc.reqOpsWire.eq_2]
    unfold delWiresAtT
    iintro ⟨#H1, #H2⟩
    isplitl
    · iapply delWireAtT_reqOpWire p u a ha $$ H1
    · iapply delWiresAtT_reqOpsWire ps us b hb $$ H2
end

/-- **The transport's request is the gRPC handler's** (see the file header): the server's copy of
a transaction `t` (nested ones included), as decoded (`txnRequestIs`, `txnWireOk`), is the handler's
request `txnReqIs r t.cmps ts es` with its wire facts, whose model is `t`. -/
theorem txnReq_of_requestIs (r : Loc) (t : TxnModel) :
    txn.txnRequestIs (GF := GF) r t ∗ txnWireOk r t ⊢
      ∃ ts es : List v3rpc.ReqOp, v3rpc.txnReqIs r t.cmps ts es ∗ v3rpc.txnReqWire r ts es ∗
        ⌜v3rpc.txnModelOf t.cmps ts es = some t⌝ := by
  iintro ⟨#Hreq, #Hw⟩
  iunfold txn.txnRequestIs at Hreq
  icases Hreq with ⟨%Hrn, Hreq⟩
  iunfold txn.txnFieldsIs at Hreq
  icases Hreq with ⟨%csl, %ssl, %fsl, %cps, %sps, %fps, #Hc, #Hcs, #Hcm, #Hs, #Hss, #Hsm,
    #Hf, #Hfs, #Hfm⟩
  ihave ⟨%ts, #Hts, %Hts'⟩ := reqOps_of_requestOps sps t.thenOps $$ Hsm
  ihave ⟨%es, #Hes, %Hes'⟩ := reqOps_of_requestOps fps t.elseOps $$ Hfm
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
      rw [delCount_toTxnOps ts _ Hts', delCount_toTxnOps es _ Hes']
      exact Hcnt
    iintro !> %ssl' %fsl' %sps' %fps' #Hs' #Hss' #Hf' #Hfs'
    ihave ⟨#A, #B⟩ := Hw $$ %ssl' %fsl' %sps' %fps' Hs' Hss' Hf' Hfs'
    isplitl
    · iapply delWiresAtT_reqOpsWire sps' ts _ Hts' $$ A
    · iapply delWiresAtT_reqOpsWire fps' es _ Hes' $$ B
  · ipureintro
    simp [v3rpc.txnModelOf, Hts', Hes']

end bridge

section resp
variable [GooseExts] [GooseSemantics] [GooseInterp]
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

theorem txnInModel_of (t : TxnModel) (cs : List CmpModel) (ts es : List v3rpc.ReqOp)
    (h : txn.txnReadonly t = true → txnModelIn t) (hm : v3rpc.txnModelOf cs ts es = some t) :
    v3rpc.txnInModel cs ts es := by
  intro t' ht'
  rw [hm] at ht'
  cases ht'
  exact h

/-- No get of a list of operations, none nested, sorts cut by a limit (D19c). -/
theorem opsNoCut_of_flat (ops : List TxnOp) (hp : ∀ op ∈ ops, TxnOp.plain op)
    (hc : ∀ o : OpFull, TxnOp.get o ∈ ops → ¬ txn.cutEarly o) : txn.OpsNoCut ops := by
  induction ops with
  | nil => trivial
  | cons op ops ih =>
    refine ⟨?_, ih (fun op' h => hp op' (List.mem_cons_of_mem _ h))
      (fun o h => hc o (List.mem_cons_of_mem _ h))⟩
    cases op with
    | get o => exact hc o List.mem_cons_self
    | txn _ _ _ => exact (hp _ List.mem_cons_self).elim
    | _ => trivial

/-- Operations whose model has no nested transaction are sibling-safe (D19c). -/
theorem siblingSafeL_of_flat : ∀ (us : List v3rpc.ReqOp) (ts : List TxnOp),
    v3rpc.ReqOp.toTxnOps us = some ts → (∀ op ∈ ts, TxnOp.plain op) → v3rpc.ReqOp.siblingSafeL us
  | [], _, _, _ => trivial
  | u :: us, ts, h, hp => by
    simp only [v3rpc.ReqOp.toTxnOps] at h
    split at h
    · rename_i t ts' h1 h2
      simp only [Option.some.injEq] at h; subst h
      have hu : ∀ cs ts0 es0, u ≠ .txn cs ts0 es0 := by
        rintro cs ts0 es0 rfl
        simp only [v3rpc.ReqOp.toTxnOp] at h1
        split at h1
        · simp only [Option.some.injEq] at h1; subst h1
          exact hp _ List.mem_cons_self
        · cases h1
      refine ⟨fun v _ => ?_, ?_, siblingSafeL_of_flat us ts' h2
        (fun op h' => hp op (List.mem_cons_of_mem _ h'))⟩
      · cases u with
        | txn cs ts0 es0 => exact absurd rfl (hu cs ts0 es0)
        | _ => trivial
      · cases u with
        | txn cs ts0 es0 => exact absurd rfl (hu cs ts0 es0)
        | _ => trivial
    · cases h


section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
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

/-- **etcd's KV methods** as registered (unit P3b): `Put`, `Range` and `DeleteRange`, the generated
handlers of `KV_ServiceDesc` (`rpc_grpc.pb.go`) with the service value `RegisterKVServer` is
given (`v3rpc.Server`: `NewQuotaKVServer(s)`, the `*quotaKVServer` `q`), with etcd's specs (the
`Put`'s witness at the request path's read names `γw`, 2026-10-14, unit C2a). -/
def etcdKVMethods (q : Loc) (E : apply.AEnv GF) (γw γr : ReadNames) (cid mid : w64) :
    List (GrpcMethod GF) :=
  [⟨go!"/etcdserverpb.KV/Put", pbPutRequest, pbPutResponse, GrpcSpec.md (etcdPutSpec E γw cid mid),
     (@! etcdserverpb._KV_Put_Handler),
     interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty) #q⟩,
   ⟨go!"/etcdserverpb.KV/Range", pbRangeRequest, pbRangeResponse, GrpcSpec.md (etcdRangeSpec E γr cid mid),
     (@! etcdserverpb._KV_Range_Handler),
     interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty) #q⟩,
   ⟨go!"/etcdserverpb.KV/DeleteRange", pbDeleteRangeRequest, pbDeleteRangeResponse,
     GrpcSpec.md (etcdDeleteSpec E γw cid mid), (@! etcdserverpb._KV_DeleteRange_Handler),
     interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty) #q⟩,
   ⟨go!"/etcdserverpb.KV/Txn", pbTxnRequest, pbTxnResponse,
     GrpcSpec.md (etcdTxnSpec E γw γr cid mid), (@! etcdserverpb._KV_Txn_Handler),
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
quota check's reader slots of `s.lgMu` and `s.bemu` (`v3rpc.quotaRd`: its `newBackendQuota` over
the current backend, D22g (A); until then a reader slot of `s.leadTimeMu` and `E.RD`, for its
NOSPACE alarm's `raftRequest`), and the interceptors' (`etcdIcRs`). -/
def etcdGrpcSlot (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  iprop((etcdRunSlot s E γr ∗ v3rpc.quotaRd s) ∗ [∗list] R ∈ etcdIcRs s, R)

end defs

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
  · icases Hspec with ⟨%Q, %Hpl, Hau, Hk⟩
    iexists (.op1 (.put o) Q)
    rw [show v3rpc.kvDepOwn (GF := GF) ρ γr (.op1 (.put o) Q) = kvOpAu1 ρ.kv (.put o) Q from rfl]
    isplitl [Hau]
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
      icases Hap with ⟨%hm, %x, %x', %l, %skip, %Hst, Hout, #Hcert, Htok, #Hwit, #Hcok, HQv⟩
      imod read_keys s E γr x'.log $$ Hsrd Hcert Hcok with %Hkeys
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
        iframe Htok HQv
        iframe #
        ipureintro
        exact ⟨⟨Hst.1, rfl, rfl, rfl, rfl, Hst.2.2⟩, Hkeys⟩
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
      imod read_keys s E γr log $$ Hsrd Hcert Hcok with %Hkeys
      ihave #HQl' := rangeQ_of_ans γr d Q o log Hdd $$ HQl
      icases Hres with ⟨%crev, Hres⟩
      iunfold txn.rangeResult at Hres
      icases Hres with (⟨%Hx, -⟩ | ⟨%Hx, -⟩ | ⟨%Hx, %kvs, %more, #Hrr, %Hsel⟩ | ⟨%Hx, -⟩)
      · exact absurd Hx.2 Hrn
      · exact absurd Hx.2.2.2.1 Hrn
      rotate_left
      · exact absurd Hx.2.2 Hrn
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
        exact ⟨Hkeys, Hlog.1, Hlog.2.1, rfl, rfl, rfl, Hx.1, rfl, Hsel, Hlog.2.2.2⟩
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
  icases Hspec with ⟨%F, #HF, %Q, %Hz, Hau, Hk⟩
  rw [kvServerAt_srvKVAns p s E ρ γr (W64 0) (W64 0) cid mid n [] F .none
    (.op1 (.deleteRange o) Q)]
  iunfold etcdRunSlot at Hslot
  icases Hslot with ⟨Hlt, Hsr, Hlg, Hrd, Hard⟩
  ihave Hu := HNR
  imod Hu with Hid
  imod (monoNatLbOwn_0 (GF := GF) γr.committed) with #H0
  iapply wp_fupd
  iapply (v3rpc.deleteRange_end_to_end p s E ρ γr (W64 0) cid mid n (GoInterface.ok ci) r o F
      (.op1 (.deleteRange o) Q)) $$ [Hlt Hsr Hlg Hrd Hard Hid Hau]
  · rw [show v3rpc.kvDepOwn (GF := GF) ρ γr (.op1 (.deleteRange o) Q) = kvOpAu1 ρ.kv (.deleteRange o) Q from rfl]
    iframe # Hau
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
        HQv⟩
      imod read_keys s E γr x'.log $$ Hsrd Hcert Hcok with %Hkeys
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
        iframe Htok HQv
        iframe #
        ipureintro
        exact ⟨⟨Hst.1, Hst.2.1, Hst.2.2.1, Hst.2.2.2.1, rfl, rfl, rfl, rfl, rfl, Hst.2.2.2.2.2⟩,
          Hkeys⟩
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
  ihave ⟨%ts, %es, #Htq, #Htw, %Hmod⟩ := txnReq_of_requestIs r t $$ [$Hreq $Hw]
  -- the deposit (unit T2): none, or (unit W-M3) a linearizable read-only transaction's read
  -- update, or a writing one's update
  ihave ⟨%d, Hdep, %Hdp, %HdQ⟩ : iprop(∃ d : v3rpc.KVDep GF, v3rpc.kvDepOwn ρ γr d ∗
      ⌜v3rpc.kvDepPre d (.txn t.cmps ts es)⌝ ∗
      ⌜(txn.txnReadonly t = true ∧ ((d = .none ∧ Q = fun _ => iprop(True)) ∨ d = .read Q)) ∨
        (txn.txnReadonly t = false ∧ d = .op1 (.txn t) Q)⌝) $$ [Hnp]
  · icases Hnp with (%Hro | ⟨%Hrs, #Hau⟩ | ⟨%Hw, Hau⟩)
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
    · iexists (.op1 (.txn t) Q)
      rw [show v3rpc.kvDepOwn (GF := GF) ρ γr (.op1 (.txn t) Q) = kvOpAu1 ρ.kv (.txn t) Q from rfl]
      iframe Hau
      ipureintro
      refine ⟨?_, Or.inr ⟨Hw.1, rfl⟩⟩
      intro t' ht'
      rw [Hmod] at ht'
      cases ht'
      right
      have hfl := v3rpc.txnModelOf_ops Hmod
      exact ⟨⟨Q, rfl⟩, Hw.2.1, Hw.2.2,
        siblingSafeL_of_flat ts t.thenOps hfl.1 hp.1,
        siblingSafeL_of_flat es t.elseOps hfl.2 hp.2,
        opsNoCut_of_flat _ hp.1 (fun o h => (hin o (List.mem_append_left _ h)).2),
        opsNoCut_of_flat _ hp.2 (fun o h => (hin o (List.mem_append_right _ h)).2)⟩
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
    · ipureintro; exact txnInModel_of t _ _ _ (fun _ => hin) Hmod
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
        imod read_keys s E γr log $$ Hsrd Hcert Hcok with %Hkeys
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
        refine ⟨Hkeys, Hlog.1, Hlog.2.1, Hlog.2.2.2, ?_, h2, h3, h4, ?_⟩
        · rw [h1]
        · rw [h4]; exact h5
      | false =>
        simp only [hro, Bool.false_eq_true, ↓reduceIte]
        iunfold v3rpc.txnAppliedAns at Hans
        icases Hans with ⟨%tw, %hm, %rq', %t'', %x, %x', %l, %skip, %Hst, Hout, #Hcert, HMint, #Hwit,
          #Hcok, HQv⟩
        imod read_keys s E γr x'.log $$ Hsrd Hcert Hcok with %Hkeys
        have hdq : d = .op1 (.txn t) Q := by
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
        iexists tw, hm, rq', t'', x, x', l, skip
        iframe Hcert HMint Hwit Hcok HQv
        ipureintro
        obtain ⟨h1, h2, h3, h4, h5⟩ := Hmm
        obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9⟩ := Hst
        refine ⟨⟨s0, s1, s2, s3, s4, ?_, h2, h3, s6, s7, s8, h4, ?_, s9⟩, Hkeys⟩
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
theorem etcd_putMethodOk (q : Loc) (E : apply.AEnv GF)
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
  ihave #Hh' := (grpcHandlerOk_md _ _ _).1 $$ Hh
  iapply (v3rpc.etcdserverpb.wp__KV_Put_Handler pbPutRequest pbPutResponse
    (GrpcSpec.md (etcdPutSpec E γr cid mid))
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty, #q⟩
    S ics Rs v3rpc.learnerReqOk m Φ ci cd dec ui rfl rfl v3rpc.QuotaKVServerIsKVServer.is_kv)
    $$ [HS HRs HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, HRs, Hres⟩
  iapply HΨ
  iframe

/-- **etcd's `Range`, as grpc runs it** (as `etcd_putMethodOk`). -/
theorem etcd_rangeMethodOk (q : Loc) (E : apply.AEnv GF)
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
  ihave #Hh' := (grpcHandlerOk_md _ _ _).1 $$ Hh
  iapply (v3rpc.etcdserverpb.wp__KV_Range_Handler pbRangeRequest pbRangeResponse
    (GrpcSpec.md (etcdRangeSpec E γr cid mid))
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty, #q⟩
    S ics Rs v3rpc.learnerReqOk m Φ ci cd dec ui rfl rfl v3rpc.QuotaKVServerIsKVServer.is_kv)
    $$ [HS HRs HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, HRs, Hres⟩
  iapply HΨ
  iframe

/-- **etcd's `DeleteRange`, as grpc runs it** (as `etcd_putMethodOk`). -/
theorem etcd_deleteMethodOk (q : Loc) (E : apply.AEnv GF)
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
  ihave #Hh' := (grpcHandlerOk_md _ _ _).1 $$ Hh
  iapply (v3rpc.etcdserverpb.wp__KV_DeleteRange_Handler pbDeleteRangeRequest pbDeleteRangeResponse
    (GrpcSpec.md (etcdDeleteSpec E γr cid mid))
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
theorem etcd_txnMethodOk (q : Loc) (E : apply.AEnv GF)
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
  ihave #Hh' := (grpcHandlerOk_md _ _ _).1 $$ Hh
  iapply (v3rpc.etcdserverpb.wp__KV_Txn_Handler pbTxnRequest pbTxnResponse
    (GrpcSpec.md (etcdTxnSpec E γw γr cid mid))
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
theorem etcd_kv_served (addr : GoString) (p q s : Loc)
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
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩
    (etcdRunSlot s E γr) $$ []
  · iframe #
  ihave #Hqp := v3rpc.quotaKV_putHandlerOk_of v3rpc.quotaKVServer.wp_Put (etcdPutSpec E ρ.rd cid mid) q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩
    (etcdRunSlot s E γr) $$ []
  · iframe #
  ihave #Hr' := grpcHandlerOk_frame _ _ (v3rpc.quotaRd s) (etcdRangeSpec E γr cid mid) $$ Hr
  ihave #Hd' := grpcHandlerOk_frame _ _ (v3rpc.quotaRd s) (etcdDeleteSpec E ρ.rd cid mid) $$ Hd
  ihave #Hqr := v3rpc.quotaKV_promotedHandlerOk (etcdRangeSpec E γr cid mid) q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩
    iprop(etcdRunSlot s E γr ∗ v3rpc.quotaRd s) go!"Range" inferInstance $$ [Hq Hr']
  · iframe #
  ihave #Hqd := v3rpc.quotaKV_promotedHandlerOk (etcdDeleteSpec E ρ.rd cid mid) q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩
    iprop(etcdRunSlot s E γr ∗ v3rpc.quotaRd s) go!"DeleteRange" inferInstance $$ [Hq Hd']
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
  ihave #Hmp' := (grpcMethodOk_md _ _ _ _ _).1 $$ Hmp
  ihave #Hmr' := (grpcMethodOk_md _ _ _ _ _).1 $$ Hmr
  ihave #Hmd' := (grpcMethodOk_md _ _ _ _ _).1 $$ Hmd
  ihave #Hmt' := (grpcMethodOk_md _ _ _ _ _).1 $$ Hmt
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
  ihave #H1' := (isGrpcRpc_md _ _ _).2 $$ H1
  ihave #H2' := (isGrpcRpc_md _ _ _).2 $$ H2
  ihave #H3' := (isGrpcRpc_md _ _ _).2 $$ H3
  ihave #H4' := (isGrpcRpc_md _ _ _).2 $$ H4
  imodintro
  iframe #

end proofs

/-! ## The client's KV calls (2026-10-21, `notes/client-cut-plan.md` K4, `notes/decisions.md` D27)

**A client of several members.** A client configured with several members' endpoints
(`clientCfgOk cfg eps`) sends each attempt to one of them, grpc's balancer's choice: a call needs its
method registered at every endpoint with one spec (`isGrpcRpcs`). Each member registers etcd's specs
at its own apply environment, read names and ids (`SrvAt`, `kvRegsAt`: `etcd_kv_started`'s), so a
call through the client passes the conjunction of the members' specs (`anySpec`), and the reply is
that member's. Since D44 (2026-10-25) this is the specs of the `*kv`'s calls themselves (`kv.Put`,
`kv.Get`, `kv.Delete`, `txn.Commit`, over `isKV`: `KVService.lean`); the results
`client_put_any`, `client_range_any`, `client_delete_any` and `client_txn_any` are those specs with
no options, the error a client error (`kvErr`), and the caller's side spelled out.

**The update.** A write's update over the whole state, one per member (`[∧ list]`: only the member
the attempt reaches fires its own), is persistent (`□`: fired at each committed occurrence, any
client), or fired at most once on a client that sends a write at most once (`writeOnce`, D29: a
client of refusal-free members, whose retry interceptor never sends a write again,
`noRefusalAt`). A read's update is persistent.

**Members that refuse** (2026-10-25, the auth plan's E2d; `notes/decisions.md`, "E2d of the auth
plan"): the persistent case needs no `noRefusalAt`, so it is the write path of a client of members
that may refuse, an auth-enabled member's (`"etcdserver: invalid auth token"`, `"user name is
empty"`, `"revision of auth store is old"`): the retry interceptor's contract for any number of
attempts (`etcdInterceptorOk`, proved over the token refresh, `refreshToken`/`getToken`) sends the
write again after each refusal, and the update fires at each committed occurrence, none for a
refused attempt. A refusal, a permission error and any other error alike end in an error result
(`kvErr`) with nothing about the write; that nothing was applied for a refused principal is the
server's (its permission check at apply), not the client's.

**One server over its endpoints** (`srvsAt addr E γr cid mid`: every address of `addr` a member at
one environment, read names and ids) is the `client_*_end_to_end` results' case: they are the
`_any` results there, with a persistent update (one family since 2026-10-22, D35).
-/

section e2e
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **`kv.Put(ctx, key, val)` through a client of the members `ms`** (see the section header;
`kv.Put.spec` with no options): etcd's KV specs registered at the members, their floor `F` and the
caller's updates, one per member, persistent or on a client that sends a write at most once; `nil`
and the reply with `putReplied` of some member, or an error. -/
theorem client_put_any (api : Loc) (ms : List (SrvAt GF)) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key val : GoString) (sl : GoSlice)
    (Q : KVState → IProp GF) (F : mvcc.Log) (hsz : opSizeOk (opPutModel key val [])) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        kvObjAt api (ms.map SrvAt.addr) ∗ ([∗list] x ∈ ms, kvRegsAt x) ∗
        ([∗list] x ∈ ms, mvcc.idxCert x.E.γ.idx F) ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
        (□ ([∧list] x ∈ ms, kvOpAu1 x.γr.kv (.put (putKeyOp key val)) Q) ∨
          (writeOnce api (ms.map SrvAt.addr) ∗
            [∧list] x ∈ ms, kvOpAu1 x.γr.kv (.put (putKeyOp key val)) Q)) }}
      (App (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
          go!"Put")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #val)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : PutRespM, putRespMsg resp m ∗ ∃ x : SrvAt GF, ⌜x ∈ ms⌝ ∗
            putReplied x.E x.γr F (txn.putOpOf key val (W64 0) false false false) Q x.cid x.mid m) ∨
          (⌜err ≠ GoInterface.nil ∧ resp = null⌝ ∗ kvErr err) }} := by
  iintro %Φ ⟨#Pc, #Hkv, #Hregs, #HF, #Hctx', #Hce, #Hopts, Hau⟩ HΦ
  have Hpm : ¬ (opPutModel key val []).putPanics ∧ (opPutModel key val []).t = W64 2 ∧
      (putWireOf (opPutModel key val [])).leaseID = W64 0 := by
    refine ⟨?_, rfl, rfl⟩
    unfold opPutModel OpFull.putPanics opFold OpFull.putInit OpFull.newOp OpModel.zero
    simp
  iapply (v3.kv.wp_PutM api ms ci cd key val sl [] Q F) $$ [Hau]
  · iframe #
    isplitl []
    · unfold isKV kvRegs; iframe #
    isplitl []
    · ipureintro; exact Hpm
    isplitl []
    · iunfold floorsAt; iframe #
    isplitl [Hau]; rotate_left
    · ipureintro; exact hsz
    unfold kvReqPre putUpd
    icases Hau with (#Hau | ⟨#Ho, Hau⟩)
    · ileft
      imodintro
      inext
      iExactEq Hau; rfl
    · iright
      iunfold writeOnce at Ho
      icases Ho with %Hnr
      isplitl []
      · ipureintro; exact Hnr
      inext
      iExactEq Hau; rfl
  inext
  iintro %resp %err Hout
  iapply HΦ
  iunfold putCallOut at Hout
  icases Hout with (⟨%Herr, %m, Hm, Hq⟩ | ⟨%Herr, #Hse, #Hcl⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m
    iframe Hm
    iunfold putAns at Hq
    iExactEq Hq; rfl
  · iright
    isplitl
    · ipureintro; exact ⟨Herr.1, Herr.2.2⟩
    · iunfold kvErr; iframe #; ipureintro; exact Herr.2.1

/-- **`kv.Get(ctx, key, opts...)` through a client of the members `ms`** (see the section
header; `kv.Get.spec`): etcd's KV specs registered at the members, their committed indices at
least `c` and floor `F`, and the caller's read update at each member's names, persistent (`□ [∧
list]`: a read may be answered by any member); `R` back, and `nil` with the reply's
`rangeReplyOk` of some member, or an error. -/
theorem client_range_any (api : Loc) (ms : List (SrvAt GF)) (c : w64) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key : GoString) (sl : GoSlice)
    (gs : List (OpFull → OpFull)) (R : IProp GF) (Q : KVState → IProp GF) (F : mvcc.Log)
    (hsz : opSizeOk (opGetModel key gs)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        kvObjAt api (ms.map SrvAt.addr) ∗ ([∗list] x ∈ ms, kvRegsAt x) ∗
        ([∗list] x ∈ ms, committedAtLeast x.γr c ∗ mvcc.idxCert x.E.γ.idx F) ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAtRes sl gs R ∗ R ∗
        sortNamesIf (opGetModel key gs).base.sortSet ∗
        ⌜¬ opGetPanics gs ∧ (opGetModel key gs).t = W64 1⌝ ∗
        □ ([∧list] x ∈ ms, ⌜Q = fun _ => iprop(True)⌝ ∨
          (⌜(rangeWireOf (opGetModel key gs)).base.serializable = false⌝ ∗ kvReadAu x.γr.kv Q)) }}
      (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
          go!"Get")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); R ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ m : RangeRespM, rangeRespMsg resp m ∗ ∃ x : SrvAt GF,
            ⌜x ∈ ms⌝ ∗ rangeReplyOk x.E x.γr c F (rangeWireOf (opGetModel key gs)) x.cid x.mid Q m) ∨
          (⌜err ≠ GoInterface.nil ∧ resp = null⌝ ∗ kvErr err)) }} := by
  iintro %Φ ⟨#Pc, #Hkv, #Hregs, #Hfacts, #Hctx', #Hce, Hopts, HR, Hsn, %Hg, #Hdq⟩ HΦ
  iapply (v3.kv.wp_GetM api ms ci cd key sl gs R c F Q) $$ [Hopts HR Hsn]
  · iframe #
    iframe Hopts HR Hsn
    isplitl []
    · unfold isKV kvRegs; iframe #
    isplitl []
    · ipureintro; exact Hg
    isplitl []
    · iunfold knownAt; iframe #
    isplitl []; rotate_left
    · ipureintro; exact hsz
    iunfold rangeUpd
    iexact Hdq
  inext
  iintro %resp %err ⟨HR, Hout⟩
  iapply HΦ
  iframe HR
  iunfold rangeCallOut at Hout
  icases Hout with (⟨%Herr, %m, Hm, Hq⟩ | ⟨%Herr, #Hse, #Hcl⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m
    iframe Hm
    iunfold rangeAns at Hq
    iexact Hq
  · iright
    isplitl
    · ipureintro; exact ⟨Herr.1, Herr.2.2⟩
    · iunfold kvErr; iframe #; ipureintro; exact Herr.2.1

/-- **`kv.Delete(ctx, key)` through a client of the members `ms`** (as `client_put_any`;
`kv.Delete.spec` with no options). -/
theorem client_delete_any (api : Loc) (ms : List (SrvAt GF)) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key : GoString) (sl : GoSlice)
    (Q : KVState → IProp GF) (F : mvcc.Log) (hsz : opSizeOk (opDeleteModel key [])) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        kvObjAt api (ms.map SrvAt.addr) ∗ ([∗list] x ∈ ms, kvRegsAt x) ∗
        ([∗list] x ∈ ms, mvcc.idxCert x.E.γ.idx F) ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
        (□ ([∧list] x ∈ ms, kvOpAu1 x.γr.kv (.deleteRange (txn.deleteOpOf key [] false)) Q) ∨
          (writeOnce api (ms.map SrvAt.addr) ∗
            [∧list] x ∈ ms, kvOpAu1 x.γr.kv (.deleteRange (txn.deleteOpOf key [] false)) Q)) }}
      (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
          go!"Delete")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : DelRespM, delRespMsg resp m ∗ ∃ x : SrvAt GF, ⌜x ∈ ms⌝ ∗
            deleteReplied x.E x.γr F (txn.deleteOpOf key [] false) Q x.cid x.mid m) ∨
          (⌜err ≠ GoInterface.nil ∧ resp = null⌝ ∗ kvErr err) }} := by
  iintro %Φ ⟨#Pc, #Hkv, #Hregs, #HF, #Hctx', #Hce, #Hopts, Hau⟩ HΦ
  iapply (v3.kv.wp_DeleteM api ms ci cd key sl [] Q F) $$ [Hau]
  · iframe #
    isplitl []
    · unfold isKV kvRegs; iframe #
    isplitl []
    · ipureintro
      refine ⟨?_, rfl, ?_⟩
      · simp [op_simps, opDeletePanics, opGetPanics, OpFull.deletePanics]
      · simp [op_simps, deleteWireOf, txn.deleteOpOf]
    isplitl []
    · iunfold floorsAt; iframe #
    isplitl [Hau]; rotate_left
    · ipureintro; exact hsz
    unfold kvReqPre delUpd
    icases Hau with (#Hau | ⟨#Ho, Hau⟩)
    · ileft
      imodintro
      inext
      iExactEq Hau; rfl
    · iright
      iunfold writeOnce at Ho
      icases Ho with %Hnr
      isplitl []
      · ipureintro; exact Hnr
      inext
      iExactEq Hau; rfl
  inext
  iintro %resp %err Hout
  iapply HΦ
  iunfold deleteCallOut at Hout
  icases Hout with (⟨%Herr, %m, Hm, Hq⟩ | ⟨%Herr, #Hse, #Hcl⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m
    iframe Hm
    iunfold delAns at Hq
    iExactEq Hq; rfl
  · iright
    isplitl
    · ipureintro; exact ⟨Herr.1, Herr.2.2⟩
    · iunfold kvErr; iframe #; ipureintro; exact Herr.2.1

/-- **`Commit()` through a client of the members `ms`** (see the section header;
`txn.Commit.spec`): etcd's KV specs registered at the members, their committed indices at least
`c` and floor `F`, and the caller's update at each member's names (`[∧ list]`), persistent or on a
builder that sends a write at most once; `nil` with the reply's `txnReplied` of some member, or an
error. -/
theorem client_txn_any (tp : Loc) (ms : List (SrvAt GF)) (c : w64)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (b : TxnBuild)
    (Q : KVState → IProp GF) (F : mvcc.Log)
    (hp : TxnModel.plain b.model) (hin : txnModelIn (txnWireOf b.model))
    (hsz : txnSizeOk (txnWireOf b.model)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        txnObjAt tp (ms.map SrvAt.addr) ci cd b ∗ ([∗list] x ∈ ms, kvRegsAt x) ∗
        ([∗list] x ∈ ms, committedAtLeast x.γr c ∗ mvcc.idxCert x.E.γ.idx F) ∗
        (□ ([∧list] x ∈ ms, txnUpdAt x.γr x.γr (txnWireOf b.model) Q) ∨
          (txnWriteOnce tp (ms.map SrvAt.addr) ∗
            [∧list] x ∈ ms, txnUpdAt x.γr x.γr (txnWireOf b.model) Q)) }}
      (App (Val (tp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"Commit"))
        (Val #()))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : TxnRespM, txnRespMsg resp m ∗ ∃ x : SrvAt GF, ⌜x ∈ ms⌝ ∗
            txnReplied x.E x.γr x.γr c F (txnWireOf b.model) Q x.cid x.mid m) ∨
          (⌜err ≠ GoInterface.nil ∧ resp = null⌝ ∗ kvErr err) }} := by
  iintro %Φ ⟨#Pc, Hobj, #Hregs, #Hfacts, Hnp⟩ HΦ
  iapply (v3.txn.wp_CommitM tp ms ci cd b c F Q) $$ [Hobj Hnp]
  · iframe Hobj
    iframe #
    isplitl []
    · iunfold kvRegs; iframe #
    isplitl []
    · ipureintro; exact ⟨hp, hin⟩
    isplitl []
    · iunfold knownAt; iframe #
    isplitl [Hnp]; rotate_left
    · ipureintro; exact hsz
    unfold txnReqPre txnUpd
    icases Hnp with (#Hu | ⟨Ho, Hu⟩)
    · ileft
      imodintro
      inext
      iexact Hu
    · iright
      iunfold txnWriteOnce at Ho
      icases Ho with %Hnr
      isplitl []
      · ipureintro; exact Hnr
      inext
      iexact Hu
  inext
  iintro %resp %err Hout
  iapply HΦ
  iunfold txnCallOut at Hout
  icases Hout with (⟨%Herr, %m, Hm, Hq⟩ | ⟨%Herr, #Hse, #Hcl⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m
    iframe Hm
    iunfold txnAns at Hq
    iexact Hq
  · iright
    isplitl
    · ipureintro; exact ⟨Herr.1, Herr.2.2⟩
    · iunfold kvErr; iframe #; ipureintro; exact Herr.2.1

end e2e

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **A put's or a delete's update, as `client_put_end_to_end` and `client_delete_end_to_end` take
it** (D21i): persistent (fired at each committed occurrence: any client). A write's update fired at
most once is the `_any` results' other case (`writeOnce`, refusal-free members). -/
def putAuOk (api : Loc) (addr : List GoString) (γk : KVNames) (op : KVOp) (Q : KVState → IProp GF) :
    IProp GF :=
  iprop(□ kvOpAu1 γk op Q)

/-- A persistent update is a put's update, its result persistent. -/
theorem putAuOk_of_box (api : Loc) (addr : List GoString) (γk : KVNames) (op : KVOp)
    (Q : KVState → IProp GF) :
    kvOpAu (GF := GF) γk op Q ⊢ putAuOk api addr γk op (fun σ => iprop(□ Q σ)) := by
  iintro #H
  unfold putAuOk
  iintro !>
  iapply kvOpAu_one $$ H

/-- **A writing transaction's update, as `client_txn_end_to_end` takes it** (`putAuOk`'s, on a
`*txn`): persistent. -/
def txnAuOk (tp : Loc) (addr : List GoString) (γk : KVNames) (op : KVOp) (Q : KVState → IProp GF) :
    IProp GF :=
  iprop(□ kvOpAu1 γk op Q)

/-- **`client_put_end_to_end`** (see the file header): `kv.Put(ctx, key, val)` with no options
(`optsAt sl []`, e.g. `nil`) on a `*kv` over a connection to the server at `addr` (`kvObjAt`:
what `NewKV` returns, `v3.wp_NewKV`) whose `Put` is registered with etcd's spec (`isGrpcRpc`, what
`etcd_kv_served` gives): `nil` and the reply's message `m` with `putReplied` (`putReplyOk` and the
revision's token) for the put
`key ↦ val` the server decodes (no lease, no previous key-value, value and lease not ignored),
and (2026-10-15, unit T2) `Q` of the state at which the caller's update over the whole state
fired, linearizing the put (unit W-M3: in `putReplied`, the state of the log the put met); or an
error and no reply. The update is `putAuOk`: persistent. Premises: the registration, the
context's (`ctxErrClient`), the package's. `client_put_any` at one server's members
(`srvsAt addr E γr cid mid`), its update persistent. -/
theorem client_put_end_to_end (api : Loc) (addr : List GoString) (E : apply.AEnv GF) (γr : ReadNames)
    (cid mid : w64) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (key val : GoString)
    (sl : GoSlice) (Q : KVState → IProp GF) (F : mvcc.Log) (hsz : opSizeOk (opPutModel key val [])) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kvObjAt api addr ∗
        kvRegs (srvsAt addr E γr cid mid) ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
        putAuOk api addr γr.kv (.put (putKeyOp key val)) Q ∗ mvcc.idxCert E.γ.idx F }}
      (App (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
          go!"Put")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #val)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : PutRespM, putRespMsg resp m ∗
            putReplied E γr F (txn.putOpOf key val (W64 0) false false false) Q cid mid m) ∨
          ⌜err ≠ GoInterface.nil ∧ resp = null⌝ }} := by
  iintro %Φ ⟨#Pc, #Hkv, #Hrpc, #Hctx', #Hce, #Hopts, Hau, #HF⟩ HΦ
  iunfold putAuOk at Hau
  icases Hau with #Hau
  iunfold kvRegs at Hrpc
  ihave #Hfs := srvsAt_sep addr E γr cid mid (mvcc.idxCert E.γ.idx F)
    (fun x : SrvAt GF => mvcc.idxCert x.E.γ.idx F) (fun _ _ => .rfl) $$ HF
  ihave #Hus := srvsAt_box addr E γr cid mid (kvOpAu1 γr.kv (.put (putKeyOp key val)) Q)
    (fun x : SrvAt GF => kvOpAu1 x.γr.kv (.put (putKeyOp key val)) Q) (fun _ _ => .rfl) $$ Hau
  iapply (client_put_any api (srvsAt addr E γr cid mid) ci cd key val sl Q F hsz) $$ []
  · rw [srvsAt_addr]
    iframe #
  inext
  iintro %resp %err Hout
  iapply HΦ
  icases Hout with (⟨%Herr, %m, Hm, %x, %hx, Hr⟩ | ⟨%Herr, -⟩)
  · obtain ⟨a, -, rfl⟩ := srvsAt_mem hx
    ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m
    iframe Hm
    iexact Hr
  · iright
    ipureintro; exact Herr

/-- **`client_range_end_to_end`** (2026-10-15, unit T2): `kv.Get(ctx, key, opts...)` with any
options that keep it a range (`opGetModel key gs`, e.g. `WithRange`, `WithPrefix`, `WithLimit`,
`WithSort`) on a `*kv` over a connection to the server at `addr` whose `Range` is registered with
etcd's spec, by a client that knows the committed index `c`, with its persistent read update over
the whole state `kvReadAu γr.kv Q` (a linearizable range; or none, `Q` trivial): `nil` and the
reply's message `m` with `rangeReplyOk` for the range the server decodes (`rangeWireOf`; at the
latest revision, `rangeReply_state` gives `□ Q σ` of the state whose selection the reply is); or an
error and no reply. Any context a client call takes (`ctxOk`). `client_range_any` at one server's
members (`srvsAt addr E γr cid mid`). -/
theorem client_range_end_to_end (api : Loc) (addr : List GoString) (E : apply.AEnv GF)
    (γr : ReadNames) (c cid mid : w64) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (key : GoString) (sl : GoSlice) (gs : List (OpFull → OpFull)) (R : IProp GF)
    (Q : KVState → IProp GF) (F : mvcc.Log) (hsz : opSizeOk (opGetModel key gs)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kvObjAt api addr ∗
        kvRegs (srvsAt addr E γr cid mid) ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAtRes sl gs R ∗ R ∗
        sortNamesIf (opGetModel key gs).base.sortSet ∗
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
  iintro %Φ ⟨#Pc, #Hkv, #Hrpc, #Hctx', #Hce, Hopts, HR, Hsn, %Hg, #Hc0, #Hdq, #HF⟩ HΦ
  iunfold kvRegs at Hrpc
  ihave #Hfs := srvsAt_sep addr E γr cid mid iprop(committedAtLeast γr c ∗ mvcc.idxCert E.γ.idx F)
    (fun x : SrvAt GF => iprop(committedAtLeast x.γr c ∗ mvcc.idxCert x.E.γ.idx F))
    (fun _ _ => .rfl) $$ []
  · iframe #
  ihave #Hus := srvsAt_box addr E γr cid mid iprop(⌜Q = fun _ => iprop(True)⌝ ∨
      (⌜(rangeWireOf (opGetModel key gs)).base.serializable = false⌝ ∗ kvReadAu γr.kv Q))
    (fun x : SrvAt GF => iprop(⌜Q = fun _ => iprop(True)⌝ ∨
      (⌜(rangeWireOf (opGetModel key gs)).base.serializable = false⌝ ∗ kvReadAu x.γr.kv Q)))
    (fun _ _ => .rfl) $$ Hdq
  iapply (client_range_any api (srvsAt addr E γr cid mid) c ci cd key sl gs R Q F hsz)
    $$ [Hopts HR Hsn]
  · rw [srvsAt_addr]
    iframe #
    iframe Hopts HR Hsn
    ipureintro; exact Hg
  inext
  iintro %resp %err ⟨HR, Hout⟩
  iapply HΦ
  iframe HR
  icases Hout with (⟨%Herr, %m, Hm, %x, %hx, Hq⟩ | ⟨%Herr, -⟩)
  · obtain ⟨a, -, rfl⟩ := srvsAt_mem hx
    ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m
    iframe Hm
    iexact Hq
  · iright
    ipureintro; exact Herr


/-- **`client_get_end_to_end`** (see the file header): `kv.Get(ctx, key)` with no options on a
`*kv` over a connection to the server at `addr` whose `Range` is registered with etcd's spec, by
a client that knows the committed index `c` (`committedAtLeast γr c`; `0` is free): `nil` and the
reply's message `m` with `rangeReplyOk` for the get of `key` the server decodes (the key alone, at
the latest revision, linearizable: read after the read index, at a log extending the log applied
through an index at least `c`); or an error and no reply. `client_range_end_to_end` with no
options. -/
theorem client_get_end_to_end (api : Loc) (addr : List GoString) (E : apply.AEnv GF) (γr : ReadNames)
    (c cid mid : w64) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (key : GoString) (sl : GoSlice) (Q : KVState → IProp GF) (F : mvcc.Log)
    (hsz : opSizeOk (opGetModel key [])) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kvObjAt api addr ∗
        kvRegs (srvsAt addr E γr cid mid) ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗ committedAtLeast γr c ∗
        (⌜Q = fun _ => iprop(True)⌝ ∨ kvReadAu γr.kv Q) ∗ mvcc.idxCert E.γ.idx F }}
      (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
          go!"Get")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : RangeRespM, rangeRespMsg resp m ∗
            rangeReplyOk E γr c F (txn.rangeOpOf key [] (W64 0) (W64 0) (W32 0) (W32 0) false false
              false (W64 0) (W64 0) (W64 0) (W64 0)) cid mid Q m) ∨
          ⌜err ≠ GoInterface.nil ∧ resp = null⌝ }} := by
  iintro %Φ ⟨#Pc, #Hkv, #Hrpc, #Hctx', #Hce, #Hopts, #Hc0, #Hdq, #HF⟩ HΦ
  ihave #Hopts' := optsAt_res sl [] iprop(True) $$ Hopts
  iapply (client_range_end_to_end api addr E γr c cid mid ci cd key sl [] iprop(True) Q F hsz) $$ []
  · iframe #
    isplitl []
    · rw [show (opGetModel key []).base.sortSet = false from rfl]
      iapply sortNamesIf_false
    isplitl []
    · ipureintro
      refine ⟨?_, rfl⟩
      unfold opGetPanics opFold OpFull.newOp
      simp
    icases Hdq with (%HQ | #Hau)
    · ileft; ipureintro; exact HQ
    · iright
      isplitr
      · ipureintro; rfl
      iexact Hau
  inext
  iintro %resp %err ⟨-, Hout⟩
  iapply HΦ
  rw [show rangeWireOf (opGetModel key []) = txn.rangeOpOf key [] (W64 0) (W64 0) (W32 0) (W32 0)
    false false false (W64 0) (W64 0) (W64 0) (W64 0) from rfl] at *
  iexact Hout

/-- **`client_delete_end_to_end`** (the vertical slice's unit V2; as `client_put_end_to_end`):
`kv.Delete(ctx, key)` with no options on a `*kv` over a connection to the server at `addr` whose
`DeleteRange` is registered with etcd's spec, by a client with the floor `F`: `nil` and the
reply's message `m` with `deleteReplied` for the delete of `key` the server decodes (the key
alone, no previous key-values) and (2026-10-15, unit T2) `□ Q` of the state at which the caller's
update over the whole state, `kvOpAu1 (.deleteRange (txn.deleteOpOf key [] false)) Q`,
linearized the delete (unit W-M3: in `deleteReplied`, the state of the log the delete met); or an
error and no reply. The update is `putAuOk`: persistent; the reply gives `Q`, not `□ Q`; any
context a client call takes (`ctxOk`: `Background()` too). `client_delete_any` at one server's
members (`srvsAt addr E γr cid mid`), its update persistent. -/
theorem client_delete_end_to_end (api : Loc) (addr : List GoString) (E : apply.AEnv GF)
    (γr : ReadNames) (cid mid : w64) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (key : GoString) (sl : GoSlice) (Q : KVState → IProp GF) (F : mvcc.Log)
    (hsz : opSizeOk (opDeleteModel key [])) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kvObjAt api addr ∗
        kvRegs (srvsAt addr E γr cid mid) ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗ mvcc.idxCert E.γ.idx F ∗
        putAuOk api addr γr.kv (.deleteRange (txn.deleteOpOf key [] false)) Q }}
      (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
          go!"Delete")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : DelRespM, delRespMsg resp m ∗
            deleteReplied E γr F (txn.deleteOpOf key [] false) Q cid mid m) ∨
          ⌜err ≠ GoInterface.nil ∧ resp = null⌝ }} := by
  iintro %Φ ⟨#Pc, #Hkv, #Hrpc, #Hctx', #Hce, #Hopts, #HF, Hau⟩ HΦ
  iunfold putAuOk at Hau
  icases Hau with #Hau
  iunfold kvRegs at Hrpc
  ihave #Hfs := srvsAt_sep addr E γr cid mid (mvcc.idxCert E.γ.idx F)
    (fun x : SrvAt GF => mvcc.idxCert x.E.γ.idx F) (fun _ _ => .rfl) $$ HF
  ihave #Hus := srvsAt_box addr E γr cid mid
    (kvOpAu1 γr.kv (.deleteRange (txn.deleteOpOf key [] false)) Q)
    (fun x : SrvAt GF => kvOpAu1 x.γr.kv (.deleteRange (txn.deleteOpOf key [] false)) Q)
    (fun _ _ => .rfl) $$ Hau
  iapply (client_delete_any api (srvsAt addr E γr cid mid) ci cd key sl Q F hsz) $$ []
  · rw [srvsAt_addr]
    iframe #
  inext
  iintro %resp %err Hout
  iapply HΦ
  icases Hout with (⟨%Herr, %m, Hm, %x, %hx, Hr⟩ | ⟨%Herr, -⟩)
  · obtain ⟨a, -, rfl⟩ := srvsAt_mem hx
    ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m
    iframe Hm
    iexact Hr
  · iright
    ipureintro; exact Herr

/-- **`client_txn_end_to_end`** (the vertical slice's unit V2): `Commit()` of the client's
transaction builder at the state `b` (`txnObjAt`: from `kv.Txn` on a `*kv` over a connection to
the server at `addr`, then `If`/`Then`/`Else`), whose operations are plain (as `Then`'s and
`Else`'s are, from `txnOpOf`: `txnOpOf_plain`) and, if read-only, within the txn package's model
(`txnModelIn`), with `Txn` registered with etcd's spec, by a client that knows the committed index
`c` and has the floor `F`: `nil` and the reply's message `m` with `txnReplied` at `c` and `F` for
the transaction the server decodes (`txnWireOf b.model`), with (2026-10-15, unit T2) `Q` of the
state at which the caller's update over the whole state, `kvOpAu1 (.txn (txnWireOf b.model)) Q`,
linearized a writing transaction (plain in the KV model, `txn.txnPlain`, no range end `[0]`; a
read-only one takes no update, `Q` trivial; unit W-M3: in `txnReplied`, the state of the log the
transaction met); or an error and no reply. A writing transaction's update is `txnAuOk`:
persistent; a linearizable read-only one may take a read update (`kvReadAu`), whose `□ Q` at the
state of the log read `txnReplied` carries. `client_txn_any` at one server's members
(`srvsAt addr E γr cid mid`; one set of read names since D44, a started server's request
path's and read loop's being the same, `ρ.rd = γr`), its update persistent. -/
theorem client_txn_end_to_end (tp : Loc) (addr : List GoString) (E : apply.AEnv GF) (γr : ReadNames)
    (c cid mid : w64) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (b : TxnBuild)
    (F : mvcc.Log) (Q : KVState → IProp GF) (hp : TxnModel.plain b.model)
    (hin : txnModelIn (txnWireOf b.model)) (hsz : txnSizeOk (txnWireOf b.model)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ txnObjAt tp addr ci cd b ∗
        kvRegs (srvsAt addr E γr cid mid) ∗
        committedAtLeast γr c ∗ mvcc.idxCert E.γ.idx F ∗
        (⌜txn.txnReadonly (txnWireOf b.model) = true ∧ Q = fun _ => iprop(True)⌝ ∨
          -- (2026-10-20, linkv-txn stage B2) a linearizable read-only one's read update
          (⌜txn.txnReadonly (txnWireOf b.model) = true ∧
            txn.txnSerializable (txnWireOf b.model) = false⌝ ∗ kvReadAu γr.kv Q) ∨
          (⌜txn.txnReadonly (txnWireOf b.model) = false ∧ txn.txnPlain (txnWireOf b.model) ∧
            txnNoZeroEnd (txnWireOf b.model)⌝ ∗ txnAuOk tp addr γr.kv (.txn (txnWireOf b.model)) Q)) }}
      (App (Val (tp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"Commit"))
        (Val #()))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : TxnRespM, txnRespMsg resp m ∗
            txnReplied E γr γr c F (txnWireOf b.model) Q cid mid m) ∨
          ⌜err ≠ GoInterface.nil ∧ resp = null⌝ }} := by
  iintro %Φ ⟨#Pc, Hobj, #Hrpc, #Hc0, #HF, Hnp⟩ HΦ
  ihave #Hu : □ txnUpdAt γr γr (txnWireOf b.model) Q $$ [Hnp]
  · icases Hnp with (%H | ⟨%H, #Ha⟩ | ⟨%H, Hau⟩)
    · imodintro; iunfold txnUpdAt; ileft; ipureintro; exact H
    · imodintro; iunfold txnUpdAt; iright; ileft; iframe Ha; ipureintro; exact H
    · iunfold txnAuOk at Hau
      icases Hau with #Hau
      imodintro
      iunfold txnUpdAt
      iright; iright
      iframe Hau
      ipureintro; exact H
  iunfold kvRegs at Hrpc
  ihave #Hfs := srvsAt_sep addr E γr cid mid iprop(committedAtLeast γr c ∗ mvcc.idxCert E.γ.idx F)
    (fun x : SrvAt GF => iprop(committedAtLeast x.γr c ∗ mvcc.idxCert x.E.γ.idx F))
    (fun _ _ => .rfl) $$ []
  · iframe #
  ihave #Hus := srvsAt_box addr E γr cid mid (txnUpdAt γr γr (txnWireOf b.model) Q)
    (fun x : SrvAt GF => txnUpdAt x.γr x.γr (txnWireOf b.model) Q) (fun _ _ => .rfl) $$ Hu
  iapply (client_txn_any tp (srvsAt addr E γr cid mid) c ci cd b Q F hp hin hsz)
    $$ [Hobj]
  · rw [srvsAt_addr]
    iframe Hobj
    iframe #
  inext
  iintro %resp %err Hout
  iapply HΦ
  icases Hout with (⟨%Herr, %m, Hm, %x, %hx, Hr⟩ | ⟨%Herr, -⟩)
  · obtain ⟨a, -, rfl⟩ := srvsAt_mem hx
    ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m
    iframe Hm
    iexact Hr
  · iright
    ipureintro; exact Herr

/-- **`client_get_after_put`** (unit C2a, 2026-10-14; see the file header): after a `kv.Put(ctx,
key, val)` that returned `nil` with the reply `mp` (`putReplyOk E γr`, `client_put_end_to_end`),
`kv.Get(ctx', key)` with no options on a `*kv` over a connection to the server at `addr` whose
`Range` is registered with etcd's spec at the same read names (`etcdRangeSpec E γr`): `nil` and the
reply's message `m` reading the put (`getAfterPutOk`: at a log extending the put's, its revision at
least the put's; the put's value if no later revision touched the key); or an error and no reply.
The get is linearizable: it asks the read index at the put's committed index (`appliedWit`'s `i`,
`committedAtLeast γr i`), so the log it reads extends the log applied through some index at least
`i` (`readLogOk`), which extends the put's (`appliedMono`). -/
theorem client_get_after_put (api : Loc) (addr : List GoString) (E : apply.AEnv GF) (γr : ReadNames)
    (cid mid : w64) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (key val : GoString) (sl : GoSlice) (Fp : mvcc.Log) (mp : PutRespM)
    (hsz : opSizeOk (opGetModel key [])) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kvObjAt api addr ∗
        kvRegs (srvsAt addr E γr cid mid) ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
        putReplyOk E γr Fp (putKeyOp key val) cid mid mp }}
      (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
          go!"Get")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : RangeRespM, rangeRespMsg resp m ∗
            getAfterPutOk E key val cid mid mp m) ∨
          ⌜err ≠ GoInterface.nil ∧ resp = null⌝ }} := by
  iintro %Φ ⟨#Pc, #Hkv, #Hrpc, #Hctx, #Hce, #Hopts, #Hput⟩ HΦ
  iunfold putReplyOk at Hput
  icases Hput with ⟨%hm, %x, %x', %lp, %skip, %Hpp, #Hcx, #Hwit, -⟩
  iunfold appliedWit at Hwit
  icases Hwit with ⟨%i, #Hci, #HLi, #Hmono⟩
  have hx' := put_applied_log (putKeyOp key val) hm x x' lp skip Hpp.1
  iapply wp_fupd
  iapply (client_get_end_to_end api addr E γr i cid mid ci cd key sl (fun _ => iprop(True))
    x'.log hsz) $$ []
  · iframe #
    ileft; ipureintro; rfl
  inext
  iintro %resp %err Hout
  icases Hout with (⟨%Herr, %m, Hm, #Hq⟩ | %Herr)
  · iunfold rangeReplyOk at Hq
    rw [show (txn.rangeOpOf key [] (W64 0) (W64 0) (W32 0) (W32 0) false false false (W64 0)
      (W64 0) (W64 0) (W64 0)).base.serializable = false from rfl]
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hq with ⟨%l, #Hcl, -, -, %Hl, #Hrl, -⟩
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
  icases H with ⟨%l, -, -, -, %Hl, -, #HQ⟩
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
  try rw [kvStateOf_kvs]
  refine ⟨getKey_value key l m.kvs m.more hsel, ?_⟩
  rw [hrev]
  simp only [kvStateOf_rev, kvStateOf_kvs]
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
  icases H with ⟨%l, -, -, -, %Hl, -, #HQ⟩
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
  try rw [kvStateOf_kvs]
  refine ⟨?_, hsel, hcount⟩
  rw [hr]
  simp only [kvStateOf_rev, kvStateOf_kvs]
  congr 1
  omega

end proofs

section watch_stub
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **etcd's client's watcher is the cache's progress notifier** (K2e-9): `RequestProgress`
(linked) returns an error whose `Error()` gives a string; the progress notification itself shows
up on the watch channels (`client_watcher_etcdWatcher`). -/
theorem client_watcher_progressNotifier (V : WEnv GF) (w : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.context ∗ isClientWatcher V w ⊢
    isEtcdProgressNotifier (watcherIfaceOf w) :=
  isEtcdProgressNotifier_of_watcher v3.watcher.wp_RequestProgress V w

end watcher

/-! ## etcd's KV service, started (item 4 of the client→server path, 2026-10-17)

What `v3rpc.Server` (proved, `v3rpc/Link.lean`'s `v3rpc.wp_Server`), `net.Listen`
and grpc's start (`grpc.start`, `Proof/google_golang_org/grpc/InvGrpcServer.lean`) give the
client: the premises `isGrpcRpc addr "/etcdserverpb.KV/Put" (etcdPutSpec ...)` and the
`Range`/`DeleteRange`/`Txn` analogues of `client_put_end_to_end`, ... (above).

A program starts the server as etcd's `embed` does: `gs := v3rpc.Server(s, nil, nil)`,
`lis, err := net.Listen("tcp", addr)`, `go gs.Serve(lis)`. `etcd_kv_started` is the ghost step
between the `Listen` and the `go`: from `Server`'s postcondition (the server being built with
etcd's chains, the KV methods among its registrations, the quota wrapper and the interceptors'
contracts) and `Listen`'s (`netListenerAt lis addr`), it gives the right to serve
(`grpcServeTok gs lis`, what `Serve` takes: `grpc.Server.Serve.spec`, in the forked goroutine),
the stream registrations (for `etcd_watch_served_chain`), and etcd's four KV specs at `addr`,
given the server's request-path premises `etcd_kv_served` takes (`isServerReq`, `isServerRead`,
the id budget, `N` run slots).
-/

section start
open Iris.ProofMode
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem etcdKVRegs_eq (q : Loc) : etcdKVRegs (GF := GF) q = v3rpc.kvRegs q := rfl

/-- `Server`'s `kvServerIs` holds `kvServerAt` (its contract dropped). -/
theorem kvServerAt_of_is (p s : Loc) (A : v3rpc.KVAns GF) (cid mid n : w64) :
    v3rpc.kvServerIs (GF := GF) p s A cid mid n ⊢ v3rpc.kvServerAt p s A cid mid n := by
  iintro #H
  iunfold v3rpc.kvServerIs at H
  icases H with ⟨%Hp, #Hh, #Hk, #Hn, %Hmx, -⟩
  iunfold v3rpc.kvServerAt
  iframe #
  ipureintro; exact ⟨Hp, Hmx⟩

/-- **etcd's KV service, started** (see the file header): the server `v3rpc.Server` built
(`grpcSrvNew` with its chains and registrations, the KV methods `kvRegs q` among them, the quota
wrapper `q` over `p`, the interceptors' contracts) and a listener at `addr` become, in a ghost
step, the right to serve `gs` on `lis`, the stream registrations at `addr`, and etcd's specs of
`Put`, `Range`, `DeleteRange` and `Txn` registered at `addr` (`isGrpcRpc`), given the server's
request-path premises (`etcd_kv_served`'s). -/
theorem etcd_kv_started (addr : GoString) (gs q p s : Loc)
    (lis : GoInterface) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (cid mid n : w64)
    (il im iu ims is : GoFunc) (svcs : List GoString)
    (regs sregs : List (GoString × val × GoInterface)) (N : Nat)
    (hregs : ∀ x ∈ v3rpc.kvRegs q, x ∈ regs) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗
        v3rpc.kvServerAt p s (v3rpc.srvKVAns s E ρ γr (W64 0) [] .none) cid mid n ∗
        □ (|==> idCred ρ.ids 1) ∗
        v3rpc.quotaKVServerAt q
          ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩ s ∗
        (□ ∀ Q : GoInterface → IProp GF, srvInterceptorOk il (srvLgReader s) Q) ∗
        (□ ∀ Q : GoInterface → IProp GF, srvInterceptorOk im iprop(True) Q) ∗
        srvInterceptorOk iu iprop(True) v3rpc.learnerReqOk ∗
        grpcSrvNew gs [il, im, iu] [ims, is] svcs regs sregs ∗ netListenerAt lis addr ∗
        ([∗list] _x ∈ List.replicate N (), etcdGrpcSlot s E γr) ⊢
      |={⊤}=> grpcServeTok gs lis ∗ grpcStreamServerAt addr [ims, is] sregs ∗
        isGrpcRpc addr go!"/etcdserverpb.KV/Put" (etcdPutSpec E ρ.rd cid mid) ∗
        isGrpcRpc addr go!"/etcdserverpb.KV/Range" (etcdRangeSpec E γr cid mid) ∗
        isGrpcRpc addr go!"/etcdserverpb.KV/DeleteRange" (etcdDeleteSpec E ρ.rd cid mid) ∗
        isGrpcRpc addr go!"/etcdserverpb.KV/Txn" (etcdTxnSpec E ρ.rd γr cid mid) := by
  iintro ⟨#Pv, #Ps, #Hsrv, #Hsrd, #Hat, #HNR, #Hq, #Hil, #Him, #Hiu, Hgs, Hlis, Hslots⟩
  imod (grpc.start gs lis addr [il, im, iu] [ims, is] svcs regs sregs) $$ [Hgs Hlis] with ⟨Hat', Hst, Htok⟩
  · iframe
  ihave #Hil' := Hil $$ %v3rpc.learnerReqOk
  ihave #Him' := Him $$ %v3rpc.learnerReqOk
  imod (etcd_kv_served addr p q s E ρ γr cid mid n il im iu regs N
    (by rw [etcdKVRegs_eq]; exact hregs)) $$ [Hat' Hslots] with H
  · iframe; iframe #
  imodintro
  iframe

end start

section lease
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [EM : EtcdModel GF]

/-- **etcd's client's lessor meets the clients' lease contract** (item 1, the client lease,
2026-10-18; `LeaseClient.lean`): a `*lessor` over a connection to a server registering etcd's specs
of `LeaseGrant` and `LeaseRevoke` and serving the keep-alive stream meets `isEtcdLease`
(`lessor.Grant`, `lessor.Revoke`, `lessor.KeepAlive` and its goroutines, linked). -/
theorem client_lessor_isEtcdLease (l : Loc) (addr : GoString) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ lessorAt l [addr] ∗
      isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseGrant" etcdLeaseGrantSpec ∗
      isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseRevoke" etcdLeaseRevokeSpec ∗
      leaseKAStreamOk addr ∗ client.eofOk ∗ client.ctxErrClientAll ∗ ctxErrTargets ⊢
    isEtcdLease (lessorIfaceOf l) :=
  isEtcdLease_of_lessor v3.lessor.wp_Grant v3.lessor.wp_Revoke v3.lessor.wp_KeepAlive l addr

/-- **`clientv3.New`'s client has the clients' lease contract** (`isEtcdLeaseClient`; item 1):
its `Lease` field holds `NewLease(c)`'s `*lessor` (`isNewClient`), which meets `isEtcdLease`
under `client_lessor_isEtcdLease`'s premises. -/
theorem client_new_isEtcdLeaseClient
    [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (cl : Loc) (ep : GoString) (V : WEnv GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isNewClient cl [ep] V ∗
      isGrpcRpc ep go!"/etcdserverpb.Lease/LeaseGrant" etcdLeaseGrantSpec ∗
      isGrpcRpc ep go!"/etcdserverpb.Lease/LeaseRevoke" etcdLeaseRevokeSpec ∗
      leaseKAStreamOk ep ∗ client.eofOk ∗ client.ctxErrClientAll ∗ ctxErrTargets ⊢
    isEtcdLeaseClient cl :=
  isEtcdLeaseClient_of_new v3.lessor.wp_Grant v3.lessor.wp_Revoke v3.lessor.wp_KeepAlive cl ep V

end lease

/-! ## etcd's Lease service, served (the client lease's stage (c), its workload-free half,
2026-10-18)

From the gRPC handler down to the server's lessor (`v3rpc/InvLease.lean`): the generated
`_Lease_LeaseGrant_Handler`/`_Lease_LeaseRevoke_Handler` on the `*quotaLeaseServer` `q` that
`RegisterLeaseServer` is given (`NewQuotaLeaseServer(s)`: its `LeaseGrant` checks the quota first,
its `LeaseRevoke` is the embedded `*LeaseServer` `lp`'s, promoted), `LeaseServer.LeaseGrant` and
`LeaseServer.LeaseRevoke` (the server's call, then the header filled), over the server's lease
methods taken as a contract (`v3rpc.raftLessor s E S`, a premise, as the KV's `raftKV`), meet
the client's specs `etcdLeaseGrantSpec`/`etcdLeaseRevokeSpec` at the server's model of etcd
(`v3rpc.etcdModelOfServer E`): `etcd_lease_served` registers them at `addr`, and
`client_lessor_isEtcdLease_served`/`client_new_isEtcdLeaseClient_served` restate the client's
lease results over those premises instead of the registrations (the keep-alive stream,
`leaseKAStreamOk`, still a premise). `etcd_kv_lease_served` serves the KV's and the Lease's unary
methods together (one `grpc.serve`: the run slot `etcdGrpcSlot`, the lessor contract at the KV
handlers' slot `etcdRunSlot`). The server side (`EtcdServer.LeaseGrant`/`LeaseRevoke` through
`raftRequest`, meeting `raftLessor`) is not done: blocked on the lease workload's design.
-/

section lease_served
open Iris.ProofMode
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **etcd's `LeaseGrant` handler meets etcd's `LeaseGrant` spec** (`grpcHandlerOk`) at the
server's model, with the lessor contract's run resource `S`: `LeaseServer.LeaseGrant`'s answer, its
header persisted, is the reply's message. -/
theorem etcd_leaseGrantHandlerOk (lp s : Loc) (A : v3rpc.KVAns GF) (cid mid : w64)
    (E : apply.AEnv GF) (S : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        v3rpc.leaseServerAt lp s A cid mid ∗ v3rpc.raftLessor s E S ⊢
      grpcHandlerOk (lp @!! go.GoType.PointerType
          go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty @!! go!"LeaseGrant") S
        (etcdLeaseGrantSpec (EM := v3rpc.etcdModelOfServer E)) := by
  iintro ⟨#Pv, #Hat, #HL⟩
  unfold grpcHandlerOk
  iintro %m %Φ %ci %cd %r !> %Ψ ⟨HS, #Hctx, #Hrc, #Hr, Hspec⟩ HΨ
  rw [show (pbLeaseGrantRequest (GF := GF)).recv r m = v3rpc.leaseGrantReqIs r m from rfl]
  iapply wp_fupd
  iapply (v3rpc.LeaseServer.wp_LeaseGrant lp s A cid mid E S ci cd r m) $$ [HS]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, Hout⟩
  iunfold v3rpc.leaseGrantOut at Hout
  icases Hout with (⟨%Hok, Hh, #Hf⟩ | %Herr)
  · iunfold v3rpc.leaseHdrOut at Hh
    icases Hh with ⟨%h, %rv, #Hhf, Hfd, -, #Hrev, #Hreach⟩
    iunfold v3rpc.hdrFilled at Hfd
    icases Hfd with ⟨%Hhn, %t, %ld, Hcid, Hmid, Ht, Hl⟩
    ipersist Hcid
    ipersist Hmid
    ipersist Ht
    ipersist Hl
    iunfold v3rpc.leaseGrantFields at Hf
    icases Hf with ⟨%id, %ttl, %e, #Hid, %Hid0, #Httl, #He⟩
    imodintro
    iapply HΨ
    iframe HS
    iintro -
    iexists (LeaseGrantRespM.mk (HdrM.mk cid mid rv t ld) id ttl e)
    isplitl []
    · simp only [pbLeaseGrantResponse]
      unfold leaseGrantRespMsg hdrFull
      isplitl []
      · ipureintro; exact Hok.2
      iexists h
      iframe #
      ipureintro; exact Hhn
    · iunfold etcdLeaseGrantSpec at Hspec
      iapply Hspec
      · ipureintro; exact Hid0
      · iexact Hreach
  · imodintro
    iapply HΨ
    iframe HS
    iintro %Hnil
    exact absurd Hnil Herr.2

/-- **etcd's `LeaseRevoke` handler meets etcd's `LeaseRevoke` spec** (as
`etcd_leaseGrantHandlerOk`). -/
theorem etcd_leaseRevokeHandlerOk (lp s : Loc) (A : v3rpc.KVAns GF) (cid mid : w64)
    (E : apply.AEnv GF) (S : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        v3rpc.leaseServerAt lp s A cid mid ∗ v3rpc.raftLessor s E S ⊢
      grpcHandlerOk (lp @!! go.GoType.PointerType
          go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty @!! go!"LeaseRevoke") S
        (etcdLeaseRevokeSpec (EM := v3rpc.etcdModelOfServer E)) := by
  iintro ⟨#Pv, #Hat, #HL⟩
  unfold grpcHandlerOk
  iintro %m %Φ %ci %cd %r !> %Ψ ⟨HS, #Hctx, #Hrc, #Hr, Hspec⟩ HΨ
  rw [show (pbLeaseRevokeRequest (GF := GF)).recv r m = v3rpc.leaseRevokeReqIs r m from rfl]
  iapply wp_fupd
  iapply (v3rpc.LeaseServer.wp_LeaseRevoke lp s A cid mid E S ci cd r m) $$ [HS]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, Hout⟩
  iunfold v3rpc.leaseRevokeOut at Hout
  icases Hout with (⟨%Hok, Hh⟩ | %Herr)
  · iunfold v3rpc.leaseHdrOut at Hh
    icases Hh with ⟨%h, %rv, #Hhf, Hfd, -, #Hrev, #Hreach⟩
    iunfold v3rpc.hdrFilled at Hfd
    icases Hfd with ⟨%Hhn, %t, %ld, Hcid, Hmid, Ht, Hl⟩
    ipersist Hcid
    ipersist Hmid
    ipersist Ht
    ipersist Hl
    imodintro
    iapply HΨ
    iframe HS
    iintro -
    iexists (LeaseRevokeRespM.mk (HdrM.mk cid mid rv t ld))
    isplitl []
    · simp only [pbLeaseRevokeResponse]
      unfold leaseRevokeRespMsg hdrFull
      isplitl []
      · ipureintro; exact Hok.2
      iexists h
      iframe #
      ipureintro; exact Hhn
    · iunfold etcdLeaseRevokeSpec at Hspec
      iapply Hspec
      iexact Hreach
  · imodintro
    iapply HΨ
    iframe HS
    iintro %Hnil
    exact absurd Hnil Herr.2

/-- The lease requests at a pointer: the learner check reads nothing of them. -/
theorem leaseGrantReq_learnerOk (l : Loc) :
    ⊢ v3rpc.learnerReqOk (GF := GF)
      (interface.mkOk (go.GoType.PointerType etcdserverpb.LeaseGrantRequest.ty) #l) :=
  v3rpc.learnerReqOk_ptr _ l (by
    simp [etcdserverpb.LeaseGrantRequest.ty, etcdserverpb.RangeRequest.ty])

theorem leaseRevokeReq_learnerOk (l : Loc) :
    ⊢ v3rpc.learnerReqOk (GF := GF)
      (interface.mkOk (go.GoType.PointerType etcdserverpb.LeaseRevokeRequest.ty) #l) :=
  v3rpc.learnerReqOk_ptr _ l (by
    simp [etcdserverpb.LeaseRevokeRequest.ty, etcdserverpb.RangeRequest.ty])

/-- **etcd's `LeaseGrant`, as grpc runs it** (`grpcMethodOk`; as `etcd_putMethodOk`): the
generated `_Lease_LeaseGrant_Handler` on the `*quotaLeaseServer` `q` whose `LeaseGrant` meets
`Spec`, under a chain of transparent interceptors. -/
theorem etcd_leaseGrantMethodOk (q : Loc)
    (Spec : GrpcSpec (GF := GF) pbLeaseGrantRequest pbLeaseGrantResponse) (S : IProp GF)
    (ics : List GoFunc) (Rs : List (IProp GF)) :
    grpcHandlerOk (q @!! go.GoType.PointerType
          go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty @!! go!"LeaseGrant")
        S Spec ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
        srvInterceptorsOk v3rpc.learnerReqOk ics Rs ⊢
      grpcMethodOk (@! etcdserverpb._Lease_LeaseGrant_Handler)
        (interface.mkOk (go.GoType.PointerType
          go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty) #q)
        ics iprop(S ∗ [∗list] R ∈ Rs, R) Spec := by
  iintro ⟨#Hh, #Ppb, #Hics⟩
  unfold grpcMethodOk
  iintro %m %Φ %ci %cd %dec %ui !> %Ψ ⟨⟨HS, HRs⟩, #Hctx, #Hrc, #Hdec, #Hch, HSpec⟩ HΨ
  ihave #Hbl : iprop(□ ∀ l : Loc, l ↦ (zero_val etcdserverpb.LeaseGrantRequest) -∗
      (pbLeaseGrantRequest (GF := GF)).blank l) $$ []
  · iintro !> %l Hl; simp only [pbLeaseGrantRequest]; iexact Hl
  ihave #HQr : iprop(□ ∀ l : Loc, (pbLeaseGrantRequest (GF := GF)).recv l m -∗
      v3rpc.learnerReqOk
        (interface.mkOk (go.GoType.PointerType etcdserverpb.LeaseGrantRequest.ty) #l)) $$ []
  · iintro !> %l -
    iapply leaseGrantReq_learnerOk
  iapply (v3rpc.etcdserverpb.wp__Lease_LeaseGrant_Handler pbLeaseGrantRequest pbLeaseGrantResponse
    Spec ⟨go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty, #q⟩
    S ics Rs v3rpc.learnerReqOk m Φ ci cd dec ui rfl rfl v3rpc.ServerMethodSets.lease_impl)
    $$ [HS HRs HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, HRs, Hres⟩
  iapply HΨ
  iframe

/-- **etcd's `LeaseRevoke`, as grpc runs it** (as `etcd_leaseGrantMethodOk`). -/
theorem etcd_leaseRevokeMethodOk (q : Loc)
    (Spec : GrpcSpec (GF := GF) pbLeaseRevokeRequest pbLeaseRevokeResponse) (S : IProp GF)
    (ics : List GoFunc) (Rs : List (IProp GF)) :
    grpcHandlerOk (q @!! go.GoType.PointerType
          go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty @!! go!"LeaseRevoke")
        S Spec ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
        srvInterceptorsOk v3rpc.learnerReqOk ics Rs ⊢
      grpcMethodOk (@! etcdserverpb._Lease_LeaseRevoke_Handler)
        (interface.mkOk (go.GoType.PointerType
          go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty) #q)
        ics iprop(S ∗ [∗list] R ∈ Rs, R) Spec := by
  iintro ⟨#Hh, #Ppb, #Hics⟩
  unfold grpcMethodOk
  iintro %m %Φ %ci %cd %dec %ui !> %Ψ ⟨⟨HS, HRs⟩, #Hctx, #Hrc, #Hdec, #Hch, HSpec⟩ HΨ
  ihave #Hbl : iprop(□ ∀ l : Loc, l ↦ (zero_val etcdserverpb.LeaseRevokeRequest) -∗
      (pbLeaseRevokeRequest (GF := GF)).blank l) $$ []
  · iintro !> %l Hl; simp only [pbLeaseRevokeRequest]; iexact Hl
  ihave #HQr : iprop(□ ∀ l : Loc, (pbLeaseRevokeRequest (GF := GF)).recv l m -∗
      v3rpc.learnerReqOk
        (interface.mkOk (go.GoType.PointerType etcdserverpb.LeaseRevokeRequest.ty) #l)) $$ []
  · iintro !> %l -
    iapply leaseRevokeReq_learnerOk
  iapply (v3rpc.etcdserverpb.wp__Lease_LeaseRevoke_Handler pbLeaseRevokeRequest
    pbLeaseRevokeResponse Spec ⟨go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty, #q⟩
    S ics Rs v3rpc.learnerReqOk m Φ ci cd dec ui rfl rfl v3rpc.ServerMethodSets.lease_impl)
    $$ [HS HRs HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, HRs, Hres⟩
  iapply HΨ
  iframe

/-- **etcd's Lease methods** as registered: `LeaseGrant` and `LeaseRevoke`, the generated
handlers of `Lease_ServiceDesc` with the service value `RegisterLeaseServer` is given
(`NewQuotaLeaseServer(s)`, the `*quotaLeaseServer` `q`), with etcd's specs at the server's model of
the apply environment `E`. -/
def etcdLeaseMethods (q : Loc) (E : apply.AEnv GF) : List (GrpcMethod GF) :=
  [⟨go!"/etcdserverpb.Lease/LeaseGrant", pbLeaseGrantRequest, pbLeaseGrantResponse,
     GrpcSpec.md (etcdLeaseGrantSpec (EM := v3rpc.etcdModelOfServer E)),
     (@! etcdserverpb._Lease_LeaseGrant_Handler),
     interface.mkOk (go.GoType.PointerType
       go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty) #q⟩,
   ⟨go!"/etcdserverpb.Lease/LeaseRevoke", pbLeaseRevokeRequest, pbLeaseRevokeResponse,
     GrpcSpec.md (etcdLeaseRevokeSpec (EM := v3rpc.etcdModelOfServer E)),
     (@! etcdserverpb._Lease_LeaseRevoke_Handler),
     interface.mkOk (go.GoType.PointerType
       go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty) #q⟩]

/-- **What `RegisterLeaseServer(gs, q)` registers of the Lease service's unary methods we
specify** (`LeaseGrant`, `LeaseRevoke`). -/
def etcdLeaseRegs (q : Loc) : List (GoString × val × GoInterface) :=
  [(go!"/etcdserverpb.Lease/LeaseGrant", (@! etcdserverpb._Lease_LeaseGrant_Handler),
     interface.mkOk (go.GoType.PointerType
       go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty) #q),
   (go!"/etcdserverpb.Lease/LeaseRevoke", (@! etcdserverpb._Lease_LeaseRevoke_Handler),
     interface.mkOk (go.GoType.PointerType
       go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty) #q)]

/-- **A Lease run's slot, as grpc's runtime holds it**: the lessor contract's `S`, the quota
check's reader slots (`v3rpc.quotaRd`, `LeaseGrant`'s check; until D22g (A) a reader slot of
`s.leadTimeMu` and `E.RD`, for its alarm), the interceptors' (`etcdIcRs`); at
`S := etcdRunSlot s E γr` it is the KV's `etcdGrpcSlot`. -/
def etcdLeaseSlot (s : Loc) (S : IProp GF) : IProp GF :=
  iprop((S ∗ v3rpc.quotaRd s) ∗ [∗list] R ∈ etcdIcRs s, R)

theorem etcdGrpcSlot_eq (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    etcdGrpcSlot (GF := GF) s E γr = etcdLeaseSlot s (etcdRunSlot s E γr) := rfl

/-- **The Lease methods as grpc runs them**, from the server's facts and the lessor contract
(what `etcd_lease_served` and `etcd_kv_lease_served` serve). -/
theorem etcd_leaseMethodsOk (lp q s : Loc) (A : v3rpc.KVAns GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (cid mid : w64) (S : IProp GF) (il im iu : GoFunc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ □ (|==> idCred ρ.ids 1) ∗
        v3rpc.leaseServerAt lp s A cid mid ∗ v3rpc.raftLessor s E S ∗
        v3rpc.quotaLeaseServerAt q
          ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty, #lp⟩ s ∗
        srvInterceptorOk il (srvLgReader s) v3rpc.learnerReqOk ∗
        srvInterceptorOk im iprop(True) v3rpc.learnerReqOk ∗
        srvInterceptorOk iu iprop(True) v3rpc.learnerReqOk ⊢
      [∗list] m ∈ etcdLeaseMethods q E,
        grpcMethodOkMd m.handler m.srv [il, im, iu] (etcdLeaseSlot s S) m.spec := by
  iintro ⟨#Pv, #Ps, #Hsrv, #HNR, #Hat, #HL, #Hq, #Hil, #Him, #Hiu⟩
  ihave #Hg := etcd_leaseGrantHandlerOk lp s A cid mid E S $$ []
  · iframe #
  ihave #Hr := etcd_leaseRevokeHandlerOk lp s A cid mid E S $$ []
  · iframe #
  ihave #Hqg := v3rpc.quotaLease_grantHandlerOk_of v3rpc.quotaLeaseServer.wp_LeaseGrant
    (etcdLeaseGrantSpec (EM := v3rpc.etcdModelOfServer E)) q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty, #lp⟩
    S $$ []
  · iframe #
  ihave #Hr' := grpcHandlerOk_frame _ _ (v3rpc.quotaRd s)
    (etcdLeaseRevokeSpec (EM := v3rpc.etcdModelOfServer E)) $$ Hr
  ihave #Hqr := v3rpc.quotaLease_revokeHandlerOk
    (etcdLeaseRevokeSpec (EM := v3rpc.etcdModelOfServer E)) q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty, #lp⟩
    iprop(S ∗ v3rpc.quotaRd s) $$ [Hq Hr']
  · iframe #
  ihave #Hics : srvInterceptorsOk (GF := GF) v3rpc.learnerReqOk [il, im, iu] (etcdIcRs s) $$ []
  · unfold etcdIcRs srvInterceptorsOk srvInterceptorsOk srvInterceptorsOk srvInterceptorsOk
    iframe #
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  ihave #Hmg := etcd_leaseGrantMethodOk q _ _ _ _ $$ [Hqg Ppb Hics]
  · iframe #
  ihave #Hmr := etcd_leaseRevokeMethodOk q _ _ _ _ $$ [Hqr Ppb Hics]
  · iframe #
  ihave #Hmg' := (grpcMethodOk_md _ _ _ _ _).1 $$ Hmg
  ihave #Hmr' := (grpcMethodOk_md _ _ _ _ _).1 $$ Hmr
  simp only [etcdLeaseMethods]
  unfold etcdLeaseSlot
  iframe #
  iapply BigSepL.bigSepL_nil.2
  itrivial

/-- **etcd's server serves its Lease methods** (the server side; as `etcd_kv_served`): the gRPC
server at `addr` built with etcd's chain of interceptors, with the Lease service registered on
the `*quotaLeaseServer` `q` over the `*LeaseServer` `lp` (`etcdLeaseRegs q` among the registered
methods), that hands the runtime `N` run slots (`etcdLeaseSlot`), registers etcd's `LeaseGrant` and
`LeaseRevoke` specs at `addr` at the server's model of etcd (`isGrpcRpc`), given the server's lease
methods' contract (`raftLessor s E S`, a premise: the server side through raft is not done). -/
theorem etcd_lease_served (addr : GoString) (lp q s : Loc)
    (A : v3rpc.KVAns GF) (E : apply.AEnv GF) (ρ : ReqNames) (cid mid : w64) (S : IProp GF)
    (il im iu : GoFunc) (regs : List (GoString × val × GoInterface)) (N : Nat)
    (hregs : ∀ x ∈ etcdLeaseRegs (GF := GF) q, x ∈ regs) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ □ (|==> idCred ρ.ids 1) ∗
        v3rpc.leaseServerAt lp s A cid mid ∗ v3rpc.raftLessor s E S ∗
        v3rpc.quotaLeaseServerAt q
          ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty, #lp⟩ s ∗
        srvInterceptorOk il (srvLgReader s) v3rpc.learnerReqOk ∗
        srvInterceptorOk im iprop(True) v3rpc.learnerReqOk ∗
        srvInterceptorOk iu iprop(True) v3rpc.learnerReqOk ∗
        grpcServerAt addr [il, im, iu] regs ∗
        ([∗list] _x ∈ List.replicate N (), etcdLeaseSlot s S) ⊢
      |={⊤}=> isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseGrant"
          (etcdLeaseGrantSpec (EM := v3rpc.etcdModelOfServer E)) ∗
        isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseRevoke"
          (etcdLeaseRevokeSpec (EM := v3rpc.etcdModelOfServer E)) := by
  iintro ⟨#Pv, #Ps, #Hsrv, #HNR, #Hat, #HL, #Hq, #Hil, #Him, #Hiu, Hl, Hslots⟩
  ihave #Hms := etcd_leaseMethodsOk lp q s A E ρ cid mid S il im iu $$ []
  · iframe #
  imod (grpc_serve_rpcs addr [il, im, iu] regs (etcdLeaseMethods q E)
    (etcdLeaseSlot s S) N (by simp only [etcdLeaseMethods, List.map]; decide)
    (by
      intro x hx
      apply hregs
      simp only [etcdLeaseMethods, List.mem_cons, List.mem_nil_iff, _root_.or_false] at hx
      rcases hx with rfl | rfl <;> simp [etcdLeaseRegs])) $$ [Hl Hslots] with Hrpcs
  · iframe
    iexact Hms
  simp only [etcdLeaseMethods]
  icases Hrpcs with ⟨#H1, #H2, -⟩
  ihave #H1' := (isGrpcRpc_md _ _ _).2 $$ H1
  ihave #H2' := (isGrpcRpc_md _ _ _).2 $$ H2
  imodintro
  iframe #

/-- **etcd's server serves its KV and Lease methods** (one gRPC server: `etcd_kv_served` and
`etcd_lease_served` together, as `grpc.serve` takes every served method at once): the run slot is
the KV's `etcdGrpcSlot`, and the lessor contract is at the KV handlers' slot `etcdRunSlot s E γr`
(what the server-side proof of `raftLessor` must meet). -/
theorem etcd_kv_lease_served (addr : GoString) (p q lp ql s : Loc)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (cid mid n lcid lmid : w64)
    (il im iu : GoFunc) (regs : List (GoString × val × GoInterface)) (N : Nat)
    (hregs : ∀ x ∈ etcdKVRegs (GF := GF) q ++ etcdLeaseRegs (GF := GF) ql, x ∈ regs) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗
        v3rpc.kvServerAt p s (v3rpc.srvKVAns s E ρ γr (W64 0) [] .none) cid mid n ∗
        □ (|==> idCred ρ.ids 1) ∗
        v3rpc.quotaKVServerAt q
          ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩ s ∗
        v3rpc.leaseServerAt lp s (v3rpc.srvKVAns s E ρ γr (W64 0) [] .none) lcid lmid ∗
        v3rpc.raftLessor s E (etcdRunSlot s E γr) ∗
        v3rpc.quotaLeaseServerAt ql
          ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty, #lp⟩ s ∗
        srvInterceptorOk il (srvLgReader s) v3rpc.learnerReqOk ∗
        srvInterceptorOk im iprop(True) v3rpc.learnerReqOk ∗
        srvInterceptorOk iu iprop(True) v3rpc.learnerReqOk ∗
        grpcServerAt addr [il, im, iu] regs ∗
        ([∗list] _x ∈ List.replicate N (), etcdGrpcSlot s E γr) ⊢
      |={⊤}=> isGrpcRpc addr go!"/etcdserverpb.KV/Put" (etcdPutSpec E ρ.rd cid mid) ∗
        isGrpcRpc addr go!"/etcdserverpb.KV/Range" (etcdRangeSpec E γr cid mid) ∗
        isGrpcRpc addr go!"/etcdserverpb.KV/DeleteRange" (etcdDeleteSpec E ρ.rd cid mid) ∗
        isGrpcRpc addr go!"/etcdserverpb.KV/Txn" (etcdTxnSpec E ρ.rd γr cid mid) ∗
        isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseGrant"
          (etcdLeaseGrantSpec (EM := v3rpc.etcdModelOfServer E)) ∗
        isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseRevoke"
          (etcdLeaseRevokeSpec (EM := v3rpc.etcdModelOfServer E)) := by
  iintro ⟨#Pv, #Ps, #Hsrv, #Hsrd, #Hat, #HNR, #Hq, #Hlat, #HL, #Hql, #Hil, #Him, #Hiu, Hl,
    Hslots⟩
  ihave #Hp := etcd_putHandlerOk p s E ρ γr cid mid n $$ []
  · iframe #
  ihave #Hr := etcd_rangeHandlerOk p s E ρ γr cid mid n $$ []
  · iframe #
  ihave #Hd := etcd_deleteHandlerOk p s E ρ γr cid mid n $$ []
  · iframe #
  ihave #Ht := etcd_txnHandlerOk p s E ρ γr cid mid n $$ []
  · iframe #
  ihave #Hqt := v3rpc.quotaKV_txnHandlerOk_of v3rpc.quotaKVServer.wp_Txn (etcdTxnSpec E ρ.rd γr cid mid) q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩
    (etcdRunSlot s E γr) $$ []
  · iframe #
  ihave #Hqp := v3rpc.quotaKV_putHandlerOk_of v3rpc.quotaKVServer.wp_Put (etcdPutSpec E ρ.rd cid mid) q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩
    (etcdRunSlot s E γr) $$ []
  · iframe #
  ihave #Hr' := grpcHandlerOk_frame _ _ (v3rpc.quotaRd s) (etcdRangeSpec E γr cid mid) $$ Hr
  ihave #Hd' := grpcHandlerOk_frame _ _ (v3rpc.quotaRd s) (etcdDeleteSpec E ρ.rd cid mid) $$ Hd
  ihave #Hqr := v3rpc.quotaKV_promotedHandlerOk (etcdRangeSpec E γr cid mid) q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩
    iprop(etcdRunSlot s E γr ∗ v3rpc.quotaRd s) go!"Range" inferInstance $$ [Hq Hr']
  · iframe #
  ihave #Hqd := v3rpc.quotaKV_promotedHandlerOk (etcdDeleteSpec E ρ.rd cid mid) q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩
    iprop(etcdRunSlot s E γr ∗ v3rpc.quotaRd s) go!"DeleteRange" inferInstance $$ [Hq Hd']
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
  ihave #Hmp' := (grpcMethodOk_md _ _ _ _ _).1 $$ Hmp
  ihave #Hmr' := (grpcMethodOk_md _ _ _ _ _).1 $$ Hmr
  ihave #Hmd' := (grpcMethodOk_md _ _ _ _ _).1 $$ Hmd
  ihave #Hmt' := (grpcMethodOk_md _ _ _ _ _).1 $$ Hmt
  ihave #Hms := etcd_leaseMethodsOk lp ql s _ E ρ lcid lmid (etcdRunSlot s E γr) il im iu $$ []
  · iframe #
  imod (grpc_serve_rpcs addr [il, im, iu] regs (etcdKVMethods q E ρ.rd γr cid mid ++
      etcdLeaseMethods ql E)
    (etcdGrpcSlot s E γr) N
    (by simp only [etcdKVMethods, etcdLeaseMethods, List.map, List.cons_append, List.nil_append]
        decide)
    (by
      intro x hx
      apply hregs
      simp only [etcdKVMethods, etcdLeaseMethods, List.cons_append, List.nil_append,
        List.mem_cons, List.mem_nil_iff, _root_.or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [etcdKVRegs, etcdLeaseRegs]))
    $$ [Hl Hslots] with Hrpcs
  · iframe
    imodintro
    iapply BigSepL.bigSepL_append.2
    isplitl []
    · simp only [etcdKVMethods]
      unfold etcdGrpcSlot
      iframe #
      iapply BigSepL.bigSepL_nil.2
      itrivial
    · rw [etcdGrpcSlot_eq]
      iexact Hms
  ihave Hrpcs := BigSepL.bigSepL_append.1 $$ Hrpcs
  icases Hrpcs with ⟨Hkv, Hle⟩
  simp only [etcdKVMethods, etcdLeaseMethods]
  icases Hkv with ⟨#H1, #H2, #H3, #H4, -⟩
  icases Hle with ⟨#H5, #H6, -⟩
  ihave #H1' := (isGrpcRpc_md _ _ _).2 $$ H1
  ihave #H2' := (isGrpcRpc_md _ _ _).2 $$ H2
  ihave #H3' := (isGrpcRpc_md _ _ _).2 $$ H3
  ihave #H4' := (isGrpcRpc_md _ _ _).2 $$ H4
  ihave #H5' := (isGrpcRpc_md _ _ _).2 $$ H5
  ihave #H6' := (isGrpcRpc_md _ _ _).2 $$ H6
  imodintro
  iframe #

/-- **The client's lessor meets the clients' lease contract against etcd's server**
(`client_lessor_isEtcdLease` at the server's model, its registrations from `etcd_lease_served`):
the premises are the server's (built with the Lease service on `q` over `lp`, the lessor contract
`raftLessor s E S`, `N` run slots) and the keep-alive stream's (`leaseKAStreamOk`, still a
premise). -/
theorem client_lessor_isEtcdLease_served (l : Loc) (addr : GoString)
    (lp q s : Loc) (A : v3rpc.KVAns GF) (E : apply.AEnv GF) (ρ : ReqNames) (cid mid : w64)
    (S : IProp GF) (il im iu : GoFunc) (regs : List (GoString × val × GoInterface)) (N : Nat)
    (hregs : ∀ x ∈ etcdLeaseRegs (GF := GF) q, x ∈ regs) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ lessorAt l [addr] ∗
        leaseKAStreamOk addr ∗ client.eofOk ∗ client.ctxErrClientAll ∗ ctxErrTargets ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ □ (|==> idCred ρ.ids 1) ∗
        v3rpc.leaseServerAt lp s A cid mid ∗ v3rpc.raftLessor s E S ∗
        v3rpc.quotaLeaseServerAt q
          ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty, #lp⟩ s ∗
        srvInterceptorOk il (srvLgReader s) v3rpc.learnerReqOk ∗
        srvInterceptorOk im iprop(True) v3rpc.learnerReqOk ∗
        srvInterceptorOk iu iprop(True) v3rpc.learnerReqOk ∗
        grpcServerAt addr [il, im, iu] regs ∗
        ([∗list] _x ∈ List.replicate N (), etcdLeaseSlot s S) ⊢
      |={⊤}=> isEtcdLease (EM := v3rpc.etcdModelOfServer E) (lessorIfaceOf l) := by
  iintro ⟨#Pc, Hl, #Hka, #Heof, #Hce, #Hct, Hsrv⟩
  imod (etcd_lease_served addr lp q s A E ρ cid mid S il im iu regs N hregs) $$ Hsrv
    with ⟨#Hg, #Hr⟩
  imodintro
  iapply (client_lessor_isEtcdLease (EM := v3rpc.etcdModelOfServer E) l addr)
  iframe
  iframe #

/-- **`clientv3.New`'s client has the clients' lease contract against etcd's server**
(`client_new_isEtcdLeaseClient` at the server's model, its registrations from
`etcd_lease_served`; as `client_lessor_isEtcdLease_served`). -/
theorem client_new_isEtcdLeaseClient_served (cl : Loc) (ep : GoString)
    (V : WEnv GF) (lp q s : Loc) (A : v3rpc.KVAns GF) (E : apply.AEnv GF) (ρ : ReqNames)
    (cid mid : w64) (S : IProp GF) (il im iu : GoFunc)
    (regs : List (GoString × val × GoInterface)) (N : Nat)
    (hregs : ∀ x ∈ etcdLeaseRegs (GF := GF) q, x ∈ regs) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isNewClient cl [ep] V ∗
        leaseKAStreamOk ep ∗ client.eofOk ∗ client.ctxErrClientAll ∗ ctxErrTargets ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ □ (|==> idCred ρ.ids 1) ∗
        v3rpc.leaseServerAt lp s A cid mid ∗ v3rpc.raftLessor s E S ∗
        v3rpc.quotaLeaseServerAt q
          ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty, #lp⟩ s ∗
        srvInterceptorOk il (srvLgReader s) v3rpc.learnerReqOk ∗
        srvInterceptorOk im iprop(True) v3rpc.learnerReqOk ∗
        srvInterceptorOk iu iprop(True) v3rpc.learnerReqOk ∗
        grpcServerAt ep [il, im, iu] regs ∗
        ([∗list] _x ∈ List.replicate N (), etcdLeaseSlot s S) ⊢
      |={⊤}=> isEtcdLeaseClient (EM := v3rpc.etcdModelOfServer E) cl := by
  iintro ⟨#Pc, Hn, #Hka, #Heof, #Hce, #Hct, Hsrv⟩
  imod (etcd_lease_served ep lp q s A E ρ cid mid S il im iu regs N hregs) $$ Hsrv
    with ⟨#Hg, #Hr⟩
  imodintro
  iapply (client_new_isEtcdLeaseClient (EM := v3rpc.etcdModelOfServer E) cl ep V)
  iframe
  iframe #

end lease_served

end client

#print axioms Perennial.EtcdGrove.client.client_get_value
#print axioms Perennial.EtcdGrove.client.rangeReply_state
#print axioms Perennial.EtcdGrove.client.client_put_any
#print axioms Perennial.EtcdGrove.client.client_range_any
#print axioms Perennial.EtcdGrove.client.client_delete_any
#print axioms Perennial.EtcdGrove.client.client_txn_any
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
#print axioms Perennial.EtcdGrove.client.client_watcher_progressNotifier
#print axioms Perennial.EtcdGrove.client.client_lessor_isEtcdLease
#print axioms Perennial.EtcdGrove.client.client_new_isEtcdLeaseClient
#print axioms Perennial.EtcdGrove.client.etcd_leaseGrantHandlerOk
#print axioms Perennial.EtcdGrove.client.etcd_leaseRevokeHandlerOk
#print axioms Perennial.EtcdGrove.client.etcd_lease_served
#print axioms Perennial.EtcdGrove.client.etcd_kv_lease_served
#print axioms Perennial.EtcdGrove.client.client_lessor_isEtcdLease_served
#print axioms Perennial.EtcdGrove.client.client_new_isEtcdLeaseClient_served
#print axioms Perennial.EtcdGrove.client.v3.kv.wp_Put
#print axioms Perennial.EtcdGrove.client.v3.kv.wp_Get
#print axioms Perennial.EtcdGrove.client.v3.kv.wp_Do
#print axioms Perennial.EtcdGrove.client.v3.wp_NewKV
#print axioms Perennial.EtcdGrove.client.v3.wp_ContextError
#print axioms Perennial.EtcdGrove.client.etcd_kv_started
#print axioms Perennial.EtcdGrove.v3rpc.wp_Server

end EtcdGrove
end Perennial
