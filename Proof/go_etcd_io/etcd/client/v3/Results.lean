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
    rcases h with ⟨-, h⟩ | ⟨-, -, h⟩ | h
    · cases h
    · cases h
    · cases h; rfl
  | .corrupt c, h => by
    simp only [apply.chainStep, hk, apply.corruptRejects, ↓reduceIte] at h
    cases h
  | .capped c, h => by
    simp only [apply.chainStep, hk, apply.cappedRejects, ↓reduceIte] at h
    cases h
  | .auth c, h => by
    unfold apply.chainStep at h
    split at h
    · rcases h with h | h
      · cases h
      · exact chainStep_put_applied op rq hk hop log l c h
    · exact chainStep_put_applied op rq hk hop log l c h
  | .quota c, h => by
    unfold apply.chainStep at h
    split at h
    · obtain ⟨o', h', ho⟩ := h
      rcases ho with rfl | ⟨l', -, ho⟩
      · exact chainStep_put_applied op rq hk hop log l c h'
      · cases ho
    · exact chainStep_put_applied op rq hk hop log l c h

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

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A run's slot** (see the file header): the reader slots a run of etcd's KV handlers holds
and gives back: `s.leadTimeMu`'s (`srvCall`'s), the store's, the logger's and the read loop's
(`srvRdCall`'s). The server hands the gRPC runtime a number of them when it serves (bounded
`RWMutex` slots: at most that many runs at a time). -/
def etcdRunSlot (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  iprop(srvLeadTimeReader s ∗ mvcc.storeReader E.s E.γ ∗ srvLgReader s ∗ srvReadReader s γr)

/-- **What a successful `Put` of `o` tells the client** about the reply's message `m` (persistent;
see the file header): since 2026-10-14 (unit C2a) with the witness that the log after is applied
through an index of the committed log at the read names `γr` (`appliedWit`: a linearizable read
at that index reads a log extending it, `client_get_after_put`). -/
def putReplyOk (E : apply.AEnv GF) (γr : ReadNames) (o : OpFull) (cid mid : w64) (m : PutRespM) :
    IProp GF :=
  iprop(∃ (hm : apply.HeaderModel) (x x' : apply.ApplyKV) (l : mvcc.Log) (skip : Bool),
    ⌜apply.applyStep (apply.withHeader (irrPut o) hm) true x x'
        (.dispatched (.applied l false) skip) ∧
      m.hdr.revision = W64 (x.log.length : Int) ∧ m.hdr.clusterId = cid ∧ m.hdr.memberId = mid ∧
      m.prev = (if o.base.prevKV then mvcc.findKey o.key (mvcc.stateAfter x.log) else none)⌝ ∗
    mvcc.idxCert E.γ.idx x'.log ∗ appliedWit γr x'.log)

instance putReplyOk_persistent (E : apply.AEnv GF) (γr : ReadNames) (o : OpFull) (cid mid : w64)
    (m : PutRespM) : Persistent (putReplyOk E γr o cid mid m) := by
  unfold putReplyOk; infer_instance

/-- **What a successful `Get` of `o` tells the client** about the reply's message `m`
(persistent; see the file header). -/
def rangeReplyOk (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (o : OpFull) (cid mid : w64)
    (m : RangeRespM) : IProp GF :=
  iprop(∃ log : mvcc.Log, mvcc.idxCert E.γ.idx log ∗
    ⌜2 ≤ log.length ∧ log.length + 3 ≤ 2 ^ 63 ∧
      m.hdr.revision = W64 ((log.length : Int) - 1) ∧ m.hdr.clusterId = cid ∧
      m.hdr.memberId = mid ∧ sint.Z o.base.rev ≤ sint.Z m.hdr.revision ∧
      m.count = txn.srvCount o
        (mvcc.stateAt log (sint.nat (mvcc.rangeRev m.hdr.revision o.base.rev))) true ∧
      txn.srvRangeOk o (mvcc.stateAt log (sint.nat (mvcc.rangeRev m.hdr.revision o.base.rev)))
        m.kvs m.more⌝ ∗
    (if o.base.serializable then iprop(True) else readLogOk γr c log))

instance rangeReplyOk_persistent (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (o : OpFull)
    (cid mid : w64) (m : RangeRespM) : Persistent (rangeReplyOk E γr c o cid mid m) := by
  unfold rangeReplyOk; split <;> infer_instance

/-- **What a successful `Put` of `o` delivers to the client** with the reply's message `m`
(the merge of the generic gRPC specification with the slice's unit V1, 2026-10-14): `putReplyOk`'s
knowledge (with its witness at the read names `γr`, unit C2a) and the token of the revision the
put made (`revMinted`, exclusive: a reply's `Φ` is delivered once, so the generic spec carries it;
`putReplied_ok` drops it). -/
def putReplied (E : apply.AEnv GF) (γr : ReadNames) (o : OpFull) (cid mid : w64) (m : PutRespM) :
    IProp GF :=
  iprop(∃ (hm : apply.HeaderModel) (x x' : apply.ApplyKV) (l : mvcc.Log) (skip : Bool),
    ⌜apply.applyStep (apply.withHeader (irrPut o) hm) true x x'
        (.dispatched (.applied l false) skip) ∧
      m.hdr.revision = W64 (x.log.length : Int) ∧ m.hdr.clusterId = cid ∧ m.hdr.memberId = mid ∧
      m.prev = (if o.base.prevKV then mvcc.findKey o.key (mvcc.stateAfter x.log) else none)⌝ ∗
    mvcc.idxCert E.γ.idx x'.log ∗ revMinted E x.log x'.log ∗ appliedWit γr x'.log)

open Iris.ProofMode in
/-- The knowledge of a delivered put (its token dropped; the witness kept). -/
theorem putReplied_ok (E : apply.AEnv GF) (γr : ReadNames) (o : OpFull) (cid mid : w64)
    (m : PutRespM) : putReplied E γr o cid mid m ⊢ putReplyOk E γr o cid mid m := by
  iintro H
  unfold putReplied putReplyOk
  icases H with ⟨%hm, %x, %x', %l, %skip, %Hp, #Hc, -, #Hw⟩
  iexists hm, x, x', l, skip
  iframe Hc Hw
  ipureintro; exact Hp

/-- **etcd's spec of the KV service's `Put`** (a predicate transformer; see the file header): a
caller asking the put `o` gets a reply message `m` with `putReplied` (`putReplyOk`, with its
witness at the read names `γr` (2026-10-14, unit C2a), and the revision's token). -/
def etcdPutSpec (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64) :
    GrpcSpec (GF := GF) pbPutRequest pbPutResponse :=
  fun (o : OpFull) (Φ : PutRespM → IProp GF) =>
    iprop(∀ m : PutRespM, putReplied E γr o cid mid m -∗ Φ m)

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
`rangeReplyOk` at `c`. -/
def etcdRangeSpec (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64) :
    GrpcSpec (GF := GF) pbRangeRequest pbRangeResponse :=
  fun (o : OpFull) (Φ : RangeRespM → IProp GF) =>
    iprop(∃ c : w64, committedAtLeast γr c ∗ ∀ m : RangeRespM, rangeReplyOk E γr c o cid mid m -∗ Φ m)

/-- **What a successful `DeleteRange` of `o` tells the client** about the reply's message `m`
(persistent): the apply thread's application of the delete `op'` the proposed data decode to
(`o` itself unless a range end is empty, `deleteRange_end_to_end`'s `deleteAppliedOk`), at the log
the entry met, the reply's header revision the delete's write revision, its ids the cluster's and
member's, `Deleted` the number of keys in the range, `PrevKvs` their key-values if asked;
mvcc's certificate of the log after. -/
def deleteReplyOk (E : apply.AEnv GF) (o : OpFull) (cid mid : w64) (m : DelRespM) : IProp GF :=
  iprop(∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel) (op' : OpFull) (x x' : apply.ApplyKV)
      (l : mvcc.Log) (skip : Bool),
    ⌜irrWireOf (apply.withHeader (irrDeleteRange o) hm) rq' ∧ rq'.deleteRange = some op' ∧
      (irrNoZeroEnd (irrDeleteRange o) → op' = o) ∧
      apply.applyStep rq' true x x' (.dispatched (.applied l false) skip) ∧
      m.hdr.revision =
        W64 ((mvcc.writeRev x.log (txn.delChanges (mvcc.stateAfter x.log) op') : Nat) : Int) ∧
      m.hdr.clusterId = cid ∧ m.hdr.memberId = mid ∧
      m.deleted = W64 ((rangeIn (mvcc.stateAfter x.log) op').length : Int) ∧
      m.prevs = (if op'.base.prevKV then rangeIn (mvcc.stateAfter x.log) op' else [])⌝ ∗
    mvcc.idxCert E.γ.idx x'.log)

instance deleteReplyOk_persistent (E : apply.AEnv GF) (o : OpFull) (cid mid : w64)
    (m : DelRespM) : Persistent (deleteReplyOk E o cid mid m) := by
  unfold deleteReplyOk; infer_instance

/-- **What a successful `DeleteRange` of `o` delivers to the client** (as `putReplied`):
`deleteReplyOk`'s knowledge and the revision's token (`revMinted`; none minted if nothing was
deleted). -/
def deleteReplied (E : apply.AEnv GF) (o : OpFull) (cid mid : w64) (m : DelRespM) : IProp GF :=
  iprop(∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel) (op' : OpFull) (x x' : apply.ApplyKV)
      (l : mvcc.Log) (skip : Bool),
    ⌜irrWireOf (apply.withHeader (irrDeleteRange o) hm) rq' ∧ rq'.deleteRange = some op' ∧
      (irrNoZeroEnd (irrDeleteRange o) → op' = o) ∧
      apply.applyStep rq' true x x' (.dispatched (.applied l false) skip) ∧
      m.hdr.revision =
        W64 ((mvcc.writeRev x.log (txn.delChanges (mvcc.stateAfter x.log) op') : Nat) : Int) ∧
      m.hdr.clusterId = cid ∧ m.hdr.memberId = mid ∧
      m.deleted = W64 ((rangeIn (mvcc.stateAfter x.log) op').length : Int) ∧
      m.prevs = (if op'.base.prevKV then rangeIn (mvcc.stateAfter x.log) op' else [])⌝ ∗
    mvcc.idxCert E.γ.idx x'.log ∗ revMinted E x.log x'.log)

open Iris.ProofMode in
/-- The knowledge of a delivered delete (its token dropped). -/
theorem deleteReplied_ok (E : apply.AEnv GF) (o : OpFull) (cid mid : w64) (m : DelRespM) :
    deleteReplied E o cid mid m ⊢ deleteReplyOk E o cid mid m := by
  iintro H
  unfold deleteReplied deleteReplyOk
  icases H with ⟨%hm, %rq', %op', %x, %x', %l, %skip, %Hp, #Hc, -⟩
  iexists hm, rq', op', x, x', l, skip
  iframe Hc
  ipureintro; exact Hp

/-- **etcd's spec of the KV service's `DeleteRange`**: a caller asking the delete `o` gets a
reply message `m` with `deleteReplied` (`deleteReplyOk` and the revision's token). -/
def etcdDeleteSpec (E : apply.AEnv GF) (cid mid : w64) :
    GrpcSpec (GF := GF) pbDeleteRangeRequest pbDeleteRangeResponse :=
  fun (o : OpFull) (Φ : DelRespM → IProp GF) =>
    iprop(∀ m : DelRespM, deleteReplied E o cid mid m -∗ Φ m)

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
     etcdDeleteSpec E cid mid, (@! etcdserverpb._KV_DeleteRange_Handler),
     interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty) #q⟩]

/-- **What `RegisterKVServer(gs, q)` registers of the KV service's unary methods we specify**
(the `ServiceDesc`'s `MethodDesc`s under `"/etcdserverpb.KV/"`, with the service value). -/
def etcdKVRegs (q : Loc) : List (GoString × val × GoInterface) :=
  [(go!"/etcdserverpb.KV/Put", (@! etcdserverpb._KV_Put_Handler),
     interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty) #q),
   (go!"/etcdserverpb.KV/Range", (@! etcdserverpb._KV_Range_Handler),
     interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty) #q),
   (go!"/etcdserverpb.KV/DeleteRange", (@! etcdserverpb._KV_DeleteRange_Handler),
     interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty) #q)]

/-- **The interceptors' per-run resources** (`v3rpc.Server`'s chain: `newLogUnaryInterceptor`'s
reader slot of `s.lgMu`, the metrics interceptor's and `newUnaryInterceptor`'s none). -/
def etcdIcRs (s : Loc) : List (IProp GF) := [srvLgReader s, iprop(True), iprop(True)]

/-- **A run's slot, as grpc's runtime holds it** (unit P3b): the handlers' (`etcdRunSlot`), the
quota wrapper's reader slot of `s.leadTimeMu` (its NOSPACE alarm's `raftRequest`), and the
interceptors' (`etcdIcRs`). -/
def etcdGrpcSlot (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  iprop((etcdRunSlot s E γr ∗ srvLeadTimeReader s) ∗ [∗list] R ∈ etcdIcRs s, R)

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
    (c c' cid mid n : w64) :
    v3rpc.kvServerAt (GF := GF) p s (v3rpc.srvKVAns s E ρ γr c) cid mid n =
      v3rpc.kvServerAt p s (v3rpc.srvKVAns s E ρ γr c') cid mid n := rfl

/-- A run's call resources give back its slot (the committed index dropped). -/
theorem etcdRunSlot_back (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (c : w64) :
    srvLeadTimeReader (GF := GF) s ∗ srvRdCall s E γr c ⊢ etcdRunSlot s E γr := by
  iintro ⟨Hlt, Hrd⟩
  unfold srvRdCall etcdRunSlot
  icases Hrd with ⟨Hsr, Hlg, -, Hrr⟩
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
        v3rpc.kvServerAt p s (v3rpc.srvKVAns s E ρ γr (W64 0)) cid mid n ∗
        □ (|==> idCred ρ.ids 1) ⊢
      grpcHandlerOk (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!!
      go!"Put") (etcdRunSlot s E γr) (etcdPutSpec E ρ.rd cid mid) := by
  iintro ⟨#Pv, #Ps, #Hsrv, #Hsrd, #Hat, #HNR⟩
  unfold grpcHandlerOk
  iintro %o %Φ %ci %cd %r !> %Ψ ⟨Hslot, #Hctx, #Hrc, #Hr, Hspec⟩ HΨ
  ihave #Htr := ctxTraceIs_none_of_runCtx ci $$ Hrc
  rw [show (pbPutRequest (GF := GF)).recv r o = txn.putRequestIs r o from rfl]
  iunfold etcdRunSlot at Hslot
  icases Hslot with ⟨Hlt, Hsr, Hlg, Hrd⟩
  ihave Hu := HNR
  imod Hu with Hid
  imod (monoNatLbOwn_0 (GF := GF) γr.committed) with #H0
  iapply wp_fupd
  iapply (v3rpc.put_end_to_end p s E ρ γr (W64 0) cid mid n (GoInterface.ok ci) r o) $$
    [Hlt Hsr Hlg Hrd Hid]
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
  inext
  iintro %resp %err Hpost
  cases hc : v3rpc.putCheck o with
  | some e =>
    icases Hpost with ⟨#Hco, Hc, Hc0⟩
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
      icases Hap with ⟨%hm, %x, %x', %l, %skip, %Hst, Hout, #Hcert, Htok, #Hwit⟩
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
      · iunfold etcdPutSpec at Hspec
        iapply Hspec
        unfold putReplied
        iexists hm, x, x', l, skip
        iframe Htok
        iframe #
        ipureintro
        exact ⟨Hst.1, rfl, rfl, rfl, rfl⟩
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
        v3rpc.kvServerAt p s (v3rpc.srvKVAns s E ρ γr (W64 0)) cid mid n ∗
        □ (|==> idCred ρ.ids 1) ⊢
      grpcHandlerOk (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!!
      go!"Range") (etcdRunSlot s E γr) (etcdRangeSpec E γr cid mid) := by
  iintro ⟨#Pv, #Ps, #Hsrv, #Hsrd, #Hat, #HNR⟩
  unfold grpcHandlerOk
  iintro %o %Φ %ci %cd %r !> %Ψ ⟨Hslot, #Hctx, #Hrc, #Hr, Hspec⟩ HΨ
  ihave #Htr := ctxTraceIs_none_of_runCtx ci $$ Hrc
  rw [show (pbRangeRequest (GF := GF)).recv r o = txn.rangeRequestIs r o from rfl]
  iunfold etcdRangeSpec at Hspec
  icases Hspec with ⟨%c, #Hc0, Hspec⟩
  rw [kvServerAt_srvKVAns p s E ρ γr (W64 0) c]
  iunfold etcdRunSlot at Hslot
  icases Hslot with ⟨Hlt, Hsr, Hlg, Hrd⟩
  ihave Hu := HNR
  imod Hu with Hid
  iapply wp_fupd
  iapply (v3rpc.range_end_to_end p s E ρ γr c cid mid n (GoInterface.ok ci) r o) $$
    [Hlt Hsr Hlg Hrd Hid]
  · iframe #
    unfold v3rpc.srvCall srvRdCall
    isplitl [Hlt Hid]
    · iexists ci, cd
      iframe
      iframe #
      ipureintro; rfl
    iframe
    iframe Hc0
  inext
  iintro %resp %err Hpost
  cases hc : v3rpc.rangeCheck o with
  | some e =>
    icases Hpost with ⟨#Hco, Hc, Hcr⟩
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
      icases Hans with ⟨%log, #Hcert, %Hlog, #Hrl, Hres⟩
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
      · iapply Hspec
        unfold rangeReplyOk
        iexists log
        iframe #
        ipureintro
        exact ⟨Hlog.1, Hlog.2.1, rfl, rfl, rfl, Hx.1, rfl, Hsel⟩
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
        v3rpc.kvServerAt p s (v3rpc.srvKVAns s E ρ γr (W64 0)) cid mid n ∗
        □ (|==> idCred ρ.ids 1) ⊢
      grpcHandlerOk
        (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!!
          go!"DeleteRange")
        (etcdRunSlot s E γr) (etcdDeleteSpec E cid mid) := by
  iintro ⟨#Pv, #Ps, #Hsrv, #Hsrd, #Hat, #HNR⟩
  unfold grpcHandlerOk
  iintro %o %Φ %ci %cd %r !> %Ψ ⟨Hslot, #Hctx, #Hrc, #Hr, Hspec⟩ HΨ
  ihave #Htr := ctxTraceIs_none_of_runCtx ci $$ Hrc
  rw [show (pbDeleteRangeRequest (GF := GF)).recv r o = txn.deleteRangeRequestIs r o from rfl]
  iunfold etcdRunSlot at Hslot
  icases Hslot with ⟨Hlt, Hsr, Hlg, Hrd⟩
  ihave Hu := HNR
  imod Hu with Hid
  imod (monoNatLbOwn_0 (GF := GF) γr.committed) with #H0
  iapply wp_fupd
  iapply (v3rpc.deleteRange_end_to_end p s E ρ γr (W64 0) cid mid n (GoInterface.ok ci) r o) $$
    [Hlt Hsr Hlg Hrd Hid]
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
  inext
  iintro %resp %err Hpost
  cases hc : v3rpc.deleteCheck o with
  | some e =>
    icases Hpost with ⟨#Hco, Hc, Hc0⟩
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
      icases Hap with ⟨%hm, %rq', %op', %x, %x', %l, %skip, %Hst, Hout, #Hcert, Htok⟩
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
      · iunfold etcdDeleteSpec at Hspec
        iapply Hspec
        unfold deleteReplied
        iexists hm, rq', op', x, x', l, skip
        iframe Htok
        iframe #
        ipureintro
        exact ⟨Hst.1, Hst.2.1, Hst.2.2.1, Hst.2.2.2.1, rfl, rfl, rfl, rfl, rfl⟩
    · iunfold v3rpc.deleteErrOk at Hep
      icases Hep with ⟨Hlt, -⟩
      imodintro
      iapply HΨ
      isplitl [Hlt Hc0]
      · iapply etcdRunSlot_back s E γr (W64 0)
        iframe
      iintro %Hnil
      exact absurd Hnil Herr.2

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
    (cid mid : w64) (S : IProp GF) (ics : List GoFunc) (Rs : List (IProp GF)) :
    grpcHandlerOk (q @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty @!! go!"DeleteRange")
        S (etcdDeleteSpec E cid mid) ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ srvInterceptorsOk v3rpc.learnerReqOk ics Rs ⊢
      grpcMethodOk (@! etcdserverpb._KV_DeleteRange_Handler)
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty) #q)
        ics iprop(S ∗ [∗list] R ∈ Rs, R) (etcdDeleteSpec E cid mid) := by
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
    (etcdDeleteSpec E cid mid)
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
        v3rpc.kvServerAt p s (v3rpc.srvKVAns s E ρ γr (W64 0)) cid mid n ∗
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
        isGrpcRpc addr go!"/etcdserverpb.KV/DeleteRange" (etcdDeleteSpec E cid mid) := by
  iintro ⟨#Pv, #Ps, #Hsrv, #Hsrd, #Hat, #HNR, #Hq, #Hil, #Him, #Hiu, Hl, Hslots⟩
  ihave #Hp := etcd_putHandlerOk p s E ρ γr cid mid n $$ []
  · iframe #
  ihave #Hr := etcd_rangeHandlerOk p s E ρ γr cid mid n $$ []
  · iframe #
  ihave #Hd := etcd_deleteHandlerOk p s E ρ γr cid mid n $$ []
  · iframe #
  ihave #Hqp := v3rpc.quotaKV_putHandlerOk_of v3rpc.quotaKVServer.wp_Put (etcdPutSpec E ρ.rd cid mid) q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩ E ρ
    (etcdRunSlot s E γr) $$ []
  · iframe #
  ihave #Hr' := grpcHandlerOk_frame _ _ (srvLeadTimeReader s) (etcdRangeSpec E γr cid mid) $$ Hr
  ihave #Hd' := grpcHandlerOk_frame _ _ (srvLeadTimeReader s) (etcdDeleteSpec E cid mid) $$ Hd
  ihave #Hqr := v3rpc.quotaKV_promotedHandlerOk (etcdRangeSpec E γr cid mid) q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩
    iprop(etcdRunSlot s E γr ∗ srvLeadTimeReader s) go!"Range" inferInstance $$ [Hq Hr']
  · iframe #
  ihave #Hqd := v3rpc.quotaKV_promotedHandlerOk (etcdDeleteSpec E cid mid) q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩
    iprop(etcdRunSlot s E γr ∗ srvLeadTimeReader s) go!"DeleteRange" inferInstance $$ [Hq Hd']
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
  ihave #Hmd := etcd_deleteMethodOk q E cid mid _ _ _ $$ [Hqd Ppb Hics]
  · iframe #
  imod (grpc_serve_rpcs addr [il, im, iu] regs (etcdKVMethods q E ρ.rd γr cid mid)
    (etcdGrpcSlot s E γr) N (by simp only [etcdKVMethods, List.map]; decide)
    (by
      intro x hx
      apply hregs
      simp only [etcdKVMethods, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp [etcdKVRegs])) $$ [Hl Hslots] with Hrpcs
  · iframe
    imodintro
    simp only [etcdKVMethods]
    unfold etcdGrpcSlot
    iframe #
    iapply BigSepL.bigSepL_nil.2
    itrivial
  simp only [etcdKVMethods]
  icases Hrpcs with ⟨#H1, #H2, #H3, -⟩
  imodintro
  iframe #

/-- **`client_put_end_to_end`** (see the file header): `kv.Put(ctx, key, val)` with no options
(`optsAt sl []`, e.g. `nil`) on a `*kv` over a connection to the server at `addr` (`kvObjAt`:
what `NewKV` returns, `v3.wp_NewKV`) whose `Put` is registered with etcd's spec (`isGrpcRpc`, what
`etcd_kv_served` gives): `nil` and the reply's message `m` with `putReplied` (`putReplyOk` and the
revision's token) for the put
`key ↦ val` the server decodes (no lease, no previous key-value, value and lease not ignored); or
an error and no reply. Premises: the registration, the context's (`ctxErrClient`), the package's.
-/
theorem client_put_end_to_end (api : Loc) (addr : GoString) (E : apply.AEnv GF) (γr : ReadNames)
    (cid mid : w64) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (key val : GoString)
    (sl : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kvObjAt api addr ∗
        isGrpcRpc addr go!"/etcdserverpb.KV/Put" (etcdPutSpec E γr cid mid) ∗
        context.isContext ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] }}
      (App (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
          go!"Put")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #val)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : PutRespM, putRespMsg resp m ∗
            putReplied E γr (txn.putOpOf key val (W64 0) false false false) cid mid m) ∨
          ⌜err ≠ GoInterface.nil ∧ resp = null⌝ }} := by
  iintro %Φ ⟨#Pc, #Hkv, #Hrpc, #Hctx, #Hce, #Hopts⟩ HΦ
  iapply (v3.kv.wp_Put api addr ci cd key val sl [] (etcdPutSpec E γr cid mid)
    (putReplied E γr (txn.putOpOf key val (W64 0) false false false) cid mid)) $$ []
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
    (key : GoString) (sl : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kvObjAt api addr ∗
        isGrpcRpc addr go!"/etcdserverpb.KV/Range" (etcdRangeSpec E γr cid mid) ∗
        context.isContext ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗ committedAtLeast γr c }}
      (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
          go!"Get")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : RangeRespM, rangeRespMsg resp m ∗
            rangeReplyOk E γr c (txn.rangeOpOf key [] (W64 0) (W64 0) (W32 0) (W32 0) false false
              false (W64 0) (W64 0) (W64 0) (W64 0)) cid mid m) ∨
          ⌜err ≠ GoInterface.nil ∧ resp = null⌝ }} := by
  iintro %Φ ⟨#Pc, #Hkv, #Hrpc, #Hctx, #Hce, #Hopts, #Hc0⟩ HΦ
  iapply (v3.kv.wp_Get api addr ci cd key sl [] (etcdRangeSpec E γr cid mid)
    (rangeReplyOk E γr c (txn.rangeOpOf key [] (W64 0) (W64 0) (W32 0) (W32 0) false false false
      (W64 0) (W64 0) (W64 0) (W64 0)) cid mid)) $$ []
  · iframe #
    isplitl []
    · ipureintro
      refine ⟨?_, rfl, rfl⟩
      unfold opGetPanics opFold OpFull.newOp
      simp
    · have Hw : rangeWireOf (opGetModel key []) = txn.rangeOpOf key [] (W64 0) (W64 0) (W32 0)
          (W32 0) false false false (W64 0) (W64 0) (W64 0) (W64 0) := rfl
      rw [Hw]
      imodintro
      inext
      unfold etcdRangeSpec
      iexists c
      iframe #
      iintro %m Hm
      iexact Hm
  inext
  iintro %resp %err Hout
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
    (key val : GoString) (sl : GoSlice) (mp : PutRespM) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kvObjAt api addr ∗
        isGrpcRpc addr go!"/etcdserverpb.KV/Range" (etcdRangeSpec E γr cid mid) ∗
        context.isContext ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
        putReplyOk E γr (putKeyOp key val) cid mid mp }}
      (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
          go!"Get")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : RangeRespM, rangeRespMsg resp m ∗
            getAfterPutOk E key val cid mid mp m) ∨
          ⌜err ≠ GoInterface.nil ∧ resp = null⌝ }} := by
  iintro %Φ ⟨#Pc, #Hkv, #Hrpc, #Hctx, #Hce, #Hopts, #Hput⟩ HΦ
  iunfold putReplyOk at Hput
  icases Hput with ⟨%hm, %x, %x', %lp, %skip, %Hpp, #Hcx, #Hwit⟩
  iunfold appliedWit at Hwit
  icases Hwit with ⟨%i, #Hci, #HLi, #Hmono⟩
  have hx' := put_applied_log (putKeyOp key val) hm x x' lp skip Hpp.1
  iapply wp_fupd
  iapply (client_get_end_to_end api addr E γr i cid mid ci cd key sl) $$ []
  · iframe #
  inext
  iintro %resp %err Hout
  icases Hout with (⟨%Herr, %m, Hm, #Hq⟩ | %Herr)
  · iunfold rangeReplyOk at Hq
    rw [show (txn.rangeOpOf key [] (W64 0) (W64 0) (W32 0) (W32 0) false false false (W64 0)
      (W64 0) (W64 0) (W64 0)).base.serializable = false from rfl]
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hq with ⟨%l, #Hcl, %Hl, #Hrl⟩
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
    obtain ⟨hlen, hlen', hrev, hcid, hmid, -, hcount, hsel⟩ := Hl
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

end proofs

end client

#print axioms Perennial.EtcdGrove.client.client_put_end_to_end
#print axioms Perennial.EtcdGrove.client.client_get_end_to_end
#print axioms Perennial.EtcdGrove.client.client_get_after_put
#print axioms Perennial.EtcdGrove.client.get_after_put_kvs
#print axioms Perennial.EtcdGrove.client.etcd_putHandlerOk
#print axioms Perennial.EtcdGrove.client.etcd_rangeHandlerOk
#print axioms Perennial.EtcdGrove.client.etcd_deleteHandlerOk
#print axioms Perennial.EtcdGrove.client.etcd_putMethodOk
#print axioms Perennial.EtcdGrove.client.etcd_rangeMethodOk
#print axioms Perennial.EtcdGrove.client.etcd_deleteMethodOk
#print axioms Perennial.EtcdGrove.client.etcd_kv_served
#print axioms Perennial.EtcdGrove.client.v3.kv.wp_Put
#print axioms Perennial.EtcdGrove.client.v3.kv.wp_Get
#print axioms Perennial.EtcdGrove.client.v3.kv.wp_Do
#print axioms Perennial.EtcdGrove.client.v3.wp_NewKV
#print axioms Perennial.EtcdGrove.client.v3.wp_ContextError

end EtcdGrove
end Perennial
