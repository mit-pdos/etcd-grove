/-
**The client meets the server** (unit C1, 2026-10-14; over the generic gRPC specification since
2026-10-14): the client's `kv.Put`, `kv.Get`, `kv.Delete` and `txn.Commit` on a `KV` made by
`NewKV` over a connection to a gRPC server, end to end through the transport (grpc's
`ClientConn.Invoke`, the client side of the trust boundary:
`Spec/google_golang_org/grpc/ClientConn__Invoke.lean`; since unit P3a the interceptor chain over
one attempt, the client's retry interceptor proved and assumed of the connection, `isEtcdConn`,
through `kvObjAt`: `client/v3/EtcdInvoke.lean`), and etcd's specs of the KV methods
(`v3rpc/InvKVService.lean`: `etcdPutSpec`, ...), which etcd's server registers at its address
(`v3rpc/KVServed.lean`: `etcd_kv_served`, over `grpc.serve`, the server side of the boundary),
with the trust base of each printed in the build log (`#print axioms`). The client's specs
(`Spec/go_etcd_io/etcd/client/v3/kv__Put.lean`, ...) hold for any method spec (`GrpcSpec`); the
results here instantiate them with etcd's. Lean-first (no Rocq counterpart); the design:
`notes/decisions.md`, "A generic gRPC specification".

The results:
* **`etcd_put_served`** (2026-10-15; the client's `kv.Put` connected to etcd's server): from
  `etcd_kv_served`'s premises (the server's facts and the gRPC server at `addr`), every
  `kv.Put(ctx, key, val, opts...)` on a `*kv` over a connection to `addr`, with options that make
  a put with no lease (`kv.Put`'s spec, `client_put_etcd`), returns `nil` and a reply with
  `putReplied` and `□ Q` of the state its persistent update linearized at, or an error.
* **`client_put_etcd`**: `kv.Put(ctx, key, val, opts...)` (`kv.Put.spec`, any options that make
  a put without a lease) on a connection to `addr` whose `Put` is registered with `etcdPutSpec`:
  `nil` and a reply holding a message `m` (`putRespMsg`) with `putReplied` for the put the server
  decodes (`putWireOf`), and `□ Q σ`; or an error.
* **`client_put_end_to_end`**: the same with no options (`client_put_etcd` at `[]`).
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
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.KVServed

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
open v3rpc (TxnModel.plain txnModelIn txnWireOf_plain txnReplied etcdTxnSpec putReplyOk rangeReplyOk
  putReplied etcdPutSpec etcdRangeSpec deleteReplied etcdDeleteSpec)

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


section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

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
end defs

section proofs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **`client_put_etcd`** (see the file header): `kv.Put(ctx, key, val, opts...)` (the client's
spec, `kv.Put.spec`, at etcd's spec of the method) on a `*kv` over a connection to the server at
`addr` (`kvObjAt`: what `NewKV` returns, `v3.wp_NewKV`) whose `Put` is registered with etcd's spec
(`isGrpcRpc`, what `v3rpc.etcd_kv_served` gives), with options (`optsAt sl gs`) that keep the
operation a put that does not panic and make a put with no lease (etcd's spec covers no leased
put yet: unit T3): `nil` and the reply's message `m` with `putReplied` (`putReplyOk` and the
revision's token) for the put the server decodes (`putWireOf`), and `□ Q` of the state at which
the caller's persistent update over the whole state, `kvOpAu (.put _) Q`, linearized the put; or
an error and no reply. Premises: the registration, the context's (`ctxErrClient`), the
package's. -/
theorem client_put_etcd (api : Loc) (addr : GoString) (E : apply.AEnv GF) (γr : ReadNames)
    (cid mid : w64) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (key val : GoString)
    (sl : GoSlice) (gs : List (OpFull → OpFull)) (Q : KVState → IProp GF) (F : mvcc.Log)
    (h : ¬ (opPutModel key val gs).putPanics ∧ (opPutModel key val gs).t = W64 2 ∧
      (putWireOf (opPutModel key val gs)).leaseID = W64 0) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kvObjAt api addr ∗
        isGrpcRpc addr go!"/etcdserverpb.KV/Put" (etcdPutSpec E γr cid mid) ∗
        context.isContext ci cd ∗ ctxErrClient ci cd ∗ optsAt sl gs ∗
        kvOpAu γr.kv (.put (putWireOf (opPutModel key val gs))) Q ∗ mvcc.idxCert E.γ.idx F }}
      (App (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
          go!"Put")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #val)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : PutRespM, putRespMsg resp m ∗
            putReplied E γr F (putWireOf (opPutModel key val gs)) cid mid m ∗
            ∃ σ : KVState, □ Q σ) ∨
          ⌜err ≠ GoInterface.nil ∧ resp = null⌝ }} := by
  iintro %Φ ⟨#Pc, #Hkv, #Hrpc, #Hctx, #Hce, #Hopts, #Hau, #HF⟩ HΦ
  obtain ⟨hpan, ht, hl⟩ := h
  ihave #Hctx' := ctxOk_of_isContext ci cd $$ Hctx
  iclear Hctx
  iapply (v3.kv.wp_Put api addr ci cd key val sl gs (etcdPutSpec E γr cid mid)
    (fun m => iprop(putReplied E γr F (putWireOf (opPutModel key val gs)) cid mid m ∗
      ∃ σ : KVState, □ Q σ))) $$ []
  · iframe #
    isplitl []
    · ipureintro; exact ⟨hpan, ht⟩
    · imodintro
      inext
      unfold etcdPutSpec
      iexists F
      iframe HF
      iexists Q
      isplitr
      · ipureintro; exact hl
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

/-- **`etcd_put_served`** (see the file header): the client's `kv.Put` connected to etcd's
server. From `v3rpc.etcd_kv_served`'s premises (the server's facts, its `*kvServer` `p` and quota
wrapper `q`, the interceptors' contracts, the gRPC server at `addr` and the run slots it hands
the runtime), every `kv.Put(ctx, key, val, opts...)` on a `*kv` over a connection to `addr`
meets `client_put_etcd`'s triple, its registration premise discharged by the server's
(`grpc.serve` on the server's side, `ClientConn.Invoke` on the client's: the two axioms of the
gRPC boundary). The put's update is at the write path's read names `ρ.rd` (the names
`etcd_kv_served` registers `Put` at). -/
theorem etcd_put_served [v3rpc.QuotaKVServerIsKVServer] (addr : GoString) (p q s : Loc)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (cid mid n : w64) (il im iu : GoFunc)
    (regs : List (GoString × val × GoInterface)) (N : Nat)
    (hregs : ∀ x ∈ v3rpc.etcdKVRegs (GF := GF) q, x ∈ regs) :
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
        ([∗list] _x ∈ List.replicate N (), v3rpc.etcdGrpcSlot s E γr) ⊢
      |={⊤}=> □ ∀ (api : Loc) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
          (key val : GoString) (sl : GoSlice) (gs : List (OpFull → OpFull))
          (Q : KVState → IProp GF) (F : mvcc.Log),
        {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kvObjAt api addr ∗
            ⌜¬ (opPutModel key val gs).putPanics ∧ (opPutModel key val gs).t = W64 2 ∧
              (putWireOf (opPutModel key val gs)).leaseID = W64 0⌝ ∗
            context.isContext ci cd ∗ ctxErrClient ci cd ∗ optsAt sl gs ∗
            kvOpAu ρ.rd.kv (.put (putWireOf (opPutModel key val gs))) Q ∗
            mvcc.idxCert E.γ.idx F }}
          (App (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
              go!"Put")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #val)) (Val #sl))
        {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
            (⌜err = GoInterface.nil⌝ ∗ ∃ m : PutRespM, putRespMsg resp m ∗
                putReplied E ρ.rd F (putWireOf (opPutModel key val gs)) cid mid m ∗
                ∃ σ : KVState, □ Q σ) ∨
              ⌜err ≠ GoInterface.nil ∧ resp = null⌝ }} := by
  iintro Hsrv
  imod (v3rpc.etcd_kv_served addr p q s E ρ γr cid mid n il im iu regs N hregs) $$ Hsrv
    with ⟨#Hput, -, -, -⟩
  imodintro
  iintro !> %api %ci %cd %key %val %sl %gs %Q %F !> %Φ ⟨#Pc, #Hkv, %h, #Hctx, #Hce, #Hopts, #Hau,
    #HF⟩ HΦ
  iapply (client_put_etcd api addr E ρ.rd cid mid ci cd key val sl gs Q F h) $$ []
  · iframe #
  inext
  iexact HΦ

/-- **`client_put_end_to_end`** (see the file header): `kv.Put(ctx, key, val)` with no options
(`optsAt sl []`, e.g. `nil`): `client_put_etcd` at `[]`, the put `key ↦ val` the server decodes
(no lease, no previous key-value, value and lease not ignored). -/
theorem client_put_end_to_end (api : Loc) (addr : GoString) (E : apply.AEnv GF) (γr : ReadNames)
    (cid mid : w64) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (key val : GoString)
    (sl : GoSlice) (Q : KVState → IProp GF) (F : mvcc.Log) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kvObjAt api addr ∗
        isGrpcRpc addr go!"/etcdserverpb.KV/Put" (etcdPutSpec E γr cid mid) ∗
        context.isContext ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
        kvOpAu γr.kv (.put (putKeyOp key val)) Q ∗ mvcc.idxCert E.γ.idx F }}
      (App (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
          go!"Put")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #val)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : PutRespM, putRespMsg resp m ∗
            putReplied E γr F (txn.putOpOf key val (W64 0) false false false) cid mid m ∗
            ∃ σ : KVState, □ Q σ) ∨
          ⌜err ≠ GoInterface.nil ∧ resp = null⌝ }} := by
  have Hw : putWireOf (opPutModel key val []) = txn.putOpOf key val (W64 0) false false false :=
    rfl
  have H := client_put_etcd api addr E γr cid mid ci cd key val sl [] Q F
    ⟨by
      unfold opPutModel OpFull.putPanics opFold OpFull.putInit OpFull.newOp OpModel.zero
      simp, rfl, rfl⟩
  rw [Hw] at H
  exact H

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
        (⌜Q = fun _ => iprop(True)⌝ ∨ kvReadAu γr.kv Q) ∗ mvcc.idxCert E.γ.idx F }}
      (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
          go!"Get")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : RangeRespM, rangeRespMsg resp m ∗
            rangeReplyOk E γr c F (txn.rangeOpOf key [] (W64 0) (W64 0) (W32 0) (W32 0) false false
              false (W64 0) (W64 0) (W64 0) (W64 0)) cid mid Q m) ∨
          ⌜err ≠ GoInterface.nil ∧ resp = null⌝ }} := by
  iintro %Φ ⟨#Pc, #Hkv, #Hrpc, #Hctx, #Hce, #Hopts, #Hc0, #Hdq, #HF⟩ HΦ
  ihave #Hctx' := ctxOk_of_isContext ci cd $$ Hctx
  iclear Hctx
  ihave #Hopts' := optsAt_res sl [] iprop(True) $$ Hopts
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
linearized the delete; or an error and no reply. -/
theorem client_delete_end_to_end (api : Loc) (addr : GoString) (E : apply.AEnv GF)
    (γr : ReadNames) (cid mid : w64) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (key : GoString) (sl : GoSlice) (Q : KVState → IProp GF) (F : mvcc.Log) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kvObjAt api addr ∗
        isGrpcRpc addr go!"/etcdserverpb.KV/DeleteRange" (etcdDeleteSpec E γr cid mid) ∗
        context.isContext ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗ mvcc.idxCert E.γ.idx F ∗
        kvOpAu γr.kv (.deleteRange (txn.deleteOpOf key [] false)) Q }}
      (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
          go!"Delete")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : DelRespM, delRespMsg resp m ∗
            deleteReplied E γr F (txn.deleteOpOf key [] false) cid mid m ∗ ∃ σ : KVState, □ Q σ) ∨
          ⌜err ≠ GoInterface.nil ∧ resp = null⌝ }} := by
  iintro %Φ ⟨#Pc, #Hkv, #Hrpc, #Hctx, #Hce, #Hopts, #HF, #Hnp⟩ HΦ
  ihave #Hctx' := ctxOk_of_isContext ci cd $$ Hctx
  iclear Hctx
  iapply (v3.kv.wp_Delete api addr ci cd key sl [] (etcdDeleteSpec E γr cid mid)
    (fun m => iprop(deleteReplied E γr F (txn.deleteOpOf key [] false) cid mid m ∗
      ∃ σ : KVState, □ Q σ))) $$ []
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
`[0]`; a read-only one takes no update, `Q` trivial); or an error and no reply. -/
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
            txnReplied E γw γr c F (txnWireOf b.model) cid mid m ∗ ∃ σ : KVState, □ Q σ) ∨
          ⌜err ≠ GoInterface.nil ∧ resp = null⌝ }} := by
  iintro %Φ ⟨#Pc, Hobj, #Hrpc, #Hc0, #HF, #Hnp⟩ HΦ
  iapply (v3.txn.wp_Commit tp addr ci cd b (etcdTxnSpec E γw γr cid mid)
    (fun m => iprop(txnReplied E γw γr c F (txnWireOf b.model) cid mid m ∗
      ∃ σ : KVState, □ Q σ))) $$ [Hobj]
  · iframe
    iframe #
    imodintro
    inext
    unfold etcdTxnSpec
    isplitl []
    · ipureintro; exact ⟨txnWireOf_plain _ hp, hin⟩
    iexists Q
    isplitr
    · iexact Hnp
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
        putReplyOk E γr Fp (putKeyOp key val) cid mid mp }}
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
    icases Hq with ⟨%l, #Hcl, %Hl, #Hrl, -⟩
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
  icases H with ⟨%l, -, %Hl, -, #HQ⟩
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
  icases H with ⟨%l, -, %Hl, -, #HQ⟩
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
  iintro %Φ ⟨#Pc, #Hkv, #Hrpc, #Hctx, #Hce, Hopts, HR, Hsn, %Hg, #Hc0, #Hdq, #HF⟩ HΦ
  ihave #Hctx' := ctxOk_of_isContext ci cd $$ Hctx
  iclear Hctx
  iapply (v3.kv.wp_Get api addr ci cd key sl gs R (etcdRangeSpec E γr cid mid)
    (rangeReplyOk E γr c F (rangeWireOf (opGetModel key gs)) cid mid Q)) $$ [Hopts HR Hsn]
  · iframe #
    iframe Hopts HR Hsn
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

end client

#print axioms Perennial.EtcdGrove.client.client_get_value
#print axioms Perennial.EtcdGrove.client.rangeReply_state
#print axioms Perennial.EtcdGrove.client.client_range_end_to_end
#print axioms Perennial.EtcdGrove.client.client_put_end_to_end
#print axioms Perennial.EtcdGrove.client.client_put_etcd
#print axioms Perennial.EtcdGrove.client.etcd_put_served
#print axioms Perennial.EtcdGrove.client.client_get_end_to_end
#print axioms Perennial.EtcdGrove.client.client_get_after_put
#print axioms Perennial.EtcdGrove.client.client_delete_end_to_end
#print axioms Perennial.EtcdGrove.client.client_txn_end_to_end
#print axioms Perennial.EtcdGrove.v3rpc.etcd_txnHandlerOk
#print axioms Perennial.EtcdGrove.v3rpc.etcd_txnMethodOk
#print axioms Perennial.EtcdGrove.client.get_after_put_kvs
#print axioms Perennial.EtcdGrove.v3rpc.etcd_putHandlerOk
#print axioms Perennial.EtcdGrove.v3rpc.etcd_rangeHandlerOk
#print axioms Perennial.EtcdGrove.v3rpc.etcd_deleteHandlerOk
#print axioms Perennial.EtcdGrove.v3rpc.etcd_putMethodOk
#print axioms Perennial.EtcdGrove.v3rpc.etcd_rangeMethodOk
#print axioms Perennial.EtcdGrove.v3rpc.etcd_deleteMethodOk
#print axioms Perennial.EtcdGrove.v3rpc.etcd_kv_served
#print axioms Perennial.EtcdGrove.client.watchClient_Watch
#print axioms Perennial.EtcdGrove.client.v3.kv.wp_Put
#print axioms Perennial.EtcdGrove.client.v3.kv.wp_Get
#print axioms Perennial.EtcdGrove.client.v3.kv.wp_Do
#print axioms Perennial.EtcdGrove.client.v3.wp_NewKV
#print axioms Perennial.EtcdGrove.client.v3.wp_ContextError

end EtcdGrove
end Perennial
