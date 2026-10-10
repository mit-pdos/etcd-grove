/-
`client/v3/concurrency`'s software transactional memory (`stm.go`): the vocabulary of
`Spec/go_etcd_io/etcd/client/v3/concurrency/{NewSTM,mkSTM,runSTM,stm__*,stmSerializable__*,
readSet__*,writeSet__*,...}.lean`. Lean-first (no Rocq counterpart). See `decisions.md`, "STM: a
higher-order closure spec, aborts as divergence, what each isolation level gives".

**The protocol.** `NewSTM(client, apply, opts...)` runs the user's closure `apply` against an
`STM` (an interface: `Get`, `Put`, `Rev`, `Del`; `commit` and `reset` internal) that buffers
the attempt's reads (`rset`: key ↦ the `*GetResponse` of its get) and writes (`wset`: key ↦ a
put or a delete), then commits the attempt with one transaction: `If(conflicts...)`,
`Then(writes...)` (and, for the serializable levels, `Else(gets of the read keys...)`, whose
responses become the next attempt's prefetched reads). A failed commit starts a new attempt.
The conflicts (`ConflictsOk`) are, per isolation level: `SerializableSnapshot` (`0`): every read
key still has the mod revision it was read with (`isKeyCurrent`), and every written key has a
mod revision at most `first()` (the least header revision of the reads); `Serializable` (`1`) and
`RepeatableReads` (`2`): the read keys' mod revisions; `ReadCommitted` (`3`): none. The
serializable levels read at the first read's revision (`WithRev`, serializable gets), the other
two at the member's latest (serializable gets).

**The model.** An attempt's state is `STMSt`: its reads (`ReadM`: the response's header
revision, the revision `rev` of the state the get read, and the key's key-value there) and
writes (`WriteM`). Each read carries `readFact`: etcd's state at `rev` has that key-value. A
commit's success gives `stmOutcome`: a revision `R`, the state `s` the transaction ran on
(etcd's at `R - 1` if it wrote, at `R` otherwise: `txnStates`), the state `s'` it left (etcd's at
`R`), and `STMCommitted`: `s'` is `s` with the writes applied, and (all levels but
`ReadCommitted`) every read is `s`'s key-value of its key (`ReadsAgree`, from the comparisons and
the mod-revision history law `etcdState_modrev_det`).

**The STM's state** (`stmState lvl pfx p st`, exclusive): the fields of the `*stm` (or of the
`*stmSerializable`'s embedded `stm`, and its `prefetch`) holding the attempt `st`, for the
client's prefix `pfx` (`isEtcdSTMClient`). `stmStale` is the state before `reset` (after `mkSTM`
the read and write sets are nil maps; after a failed `stmSerializable.commit` the read set is the
prefetch map). `stmMethods lvl pfx p` (persistent) are the triples of the interface's methods,
which `mkSTM` proves for both implementations.

**The closure** (`applySpec pfx apply Q`, persistent): for any STM (any level, any state) with
`stmMethods`, `apply` returns an error or `nil` with the attempt's state, and `nil` means the
attempt's state satisfies `Q`. `NewSTM` returns, on `nil`, a committed attempt's state `st`
with `Q st` and `stmOutcome`.

**Aborts.** `stm.fetch` and the commits `panic(stmError{err})` on a client error, which
`runSTM`'s deferred function recovers into the returned error. Perennial models neither `panic`
(stuck) nor `recover`: the two are the trust boundary here (`stmPanic.spec`: such a panic does
not return; `stmRecover.spec`: `recover()` returns nil), see `decisions.md`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvMutexLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

/-! ## Isolation levels -/

/-- `SerializableSnapshot` -/
abbrev isoSS : w64 := W64 0
/-- `Serializable` -/
abbrev isoS : w64 := W64 1
/-- `RepeatableReads` -/
abbrev isoRR : w64 := W64 2
/-- `ReadCommitted` -/
abbrev isoRC : w64 := W64 3

/-- The levels `mkSTM` supports (it panics on any other). -/
def isoValid (lvl : w64) : Prop := lvl = isoSS ∨ lvl = isoS ∨ lvl = isoRR ∨ lvl = isoRC

/-- The levels whose STM is a `*stmSerializable` (the others' is a `*stm`). -/
def isoSer (lvl : w64) : Bool := decide (lvl = isoSS ∨ lvl = isoS)

/-! ## The model: an attempt's reads and writes -/

/-- A read (one entry of the read set, a `*GetResponse` of a single-key get): the response
header's revision `hdr` (what `first()` takes the least of), the revision `rev` of the state the
get read, and the key's key-value there (`none`: absent). -/
structure ReadM where
  hdr : w64
  rev : w64
  kv : Option EtcdKv

/-- What a read returns (`respToValue`): the key's value, `""` if absent. -/
def ReadM.value (e : ReadM) : GoString := match e.kv with | some v => v.value | none => []

/-- The key's mod revision as read, `0` if absent (what `isKeyCurrent` compares). -/
def ReadM.modRev (e : ReadM) : w64 := match e.kv with | some v => v.modRev | none => W64 0

/-- A write (one entry of the write set): a put of a value with a lease (`0`: none), or a
delete. -/
inductive WriteM where
  | put (val : GoString) (lease : w64)
  | del

/-- What `Get` returns for a written key: the value put, `""` for a delete. -/
def WriteM.val : WriteM → GoString
  | .put v _ => v
  | .del => []

/-- The operation of the commit's `Then` for the write of `k`. -/
def WriteM.op (k : GoString) : WriteM → TxnOp
  | .put v l => .put k v l
  | .del => .delete (opDeleteModel k [])

/-- An attempt's reads and writes (the read set and the write set). -/
structure STMSt where
  reads : GMap GoString ReadM
  writes : GMap GoString WriteM

/-- A fresh attempt (after `reset`). -/
def STMSt.empty : STMSt := { reads := ∅, writes := ∅ }

/-- The key-value of `k` in the state `s` (`none`: absent). -/
def kvAt (s : List EtcdKv) (k : GoString) : Option EtcdKv := s.find? (fun v => decide (v.key = k))

/-- The mod revision of `k` in `s`, `0` if absent (what a `ModRevision(k)` comparison reads). -/
def modRevAt (s : List EtcdKv) (k : GoString) : w64 := ((kvAt s k).map EtcdKv.modRev).getD (W64 0)

/-- `ks` lists the keys of `m`, each once (a `for range` over a map's order). -/
def MapKeysList {V : Type} (m : GMap GoString V) (ks : List GoString) : Prop :=
  ks.Nodup ∧ ∀ k, k ∈ ks ↔ (m !! k).isSome

/-- Entries of `reads` added: `(k, e)` in order (a later one for the same key wins). -/
def readsAdd (reads : GMap GoString ReadM) (l : List (GoString × ReadM)) : GMap GoString ReadM :=
  l.foldl (fun m ke => GMap.insert ke.1 ke.2 m) reads

/-! ## The commit's comparisons and operations -/

/-- `isKeyCurrent(k, resp)`: `ModRevision(k) = ` the mod revision read (`0`: absent). -/
def readCmp (k : GoString) (e : ReadM) : CmpModel := compareM (cmpKeyM .mod k) .eq (.num e.modRev)

/-- `writeSet.cmps(rev)`'s comparison of `k`: `ModRevision(k) < rev`. -/
def writeCmp (rev : w64) (k : GoString) : CmpModel := compareM (cmpKeyM .mod k) .lt (.num rev)

/-- `readSet.first()`: the least header revision of the reads (signed), `math.MaxInt64 - 1` if
there is none (or if all are larger). -/
def FirstOk (reads : GMap GoString ReadM) (f : w64) : Prop :=
  sint.Z f ≤ 2 ^ 63 - 2 ∧ (∀ k e, reads !! k = some e → sint.Z f ≤ sint.Z e.hdr) ∧
    (f = W64 (2 ^ 63 - 2) ∨ ∃ k e, reads !! k = some e ∧ f = e.hdr)

/-- `readSet.cmps()`: one `readCmp` per read, in the map's order. -/
def ReadCmpsOk (reads : GMap GoString ReadM) (ms : List CmpModel) : Prop :=
  ∃ ks, MapKeysList reads ks ∧ ms = ks.filterMap (fun k => (reads !! k).map (readCmp k))

/-- `writeSet.cmps(rev)`: one `writeCmp rev` per written key, in the map's order. -/
def WriteCmpsOk (writes : GMap GoString WriteM) (rev : w64) (ms : List CmpModel) : Prop :=
  ∃ ks, MapKeysList writes ks ∧ ms = ks.map (writeCmp rev)

/-- `writeSet.puts()`: one operation per write, in the map's order. -/
def WriteOpsOk (writes : GMap GoString WriteM) (ops : List TxnOp) : Prop :=
  ∃ ks, MapKeysList writes ks ∧ ops = ks.filterMap (fun k => (writes !! k).map (WriteM.op k))

/-- **The conflicts** (`s.conflicts()`, `mkSTM`'s closure) of the level `lvl` for the reads and
writes: `SerializableSnapshot`, the reads' comparisons and the writes' against `first() + 1`;
`Serializable`, `RepeatableReads`, the reads'; `ReadCommitted`, none. -/
def ConflictsOk (lvl : w64) (reads : GMap GoString ReadM) (writes : GMap GoString WriteM)
    (ms : List CmpModel) : Prop :=
  (lvl = isoSS ∧ ∃ f m1 m2, FirstOk reads f ∧ ReadCmpsOk reads m1 ∧
      WriteCmpsOk writes (f + W64 1) m2 ∧ ms = m1 ++ m2) ∨
    ((lvl = isoS ∨ lvl = isoRR) ∧ ReadCmpsOk reads ms) ∨
    (lvl = isoRC ∧ ms = [])

/-- Every read is the key-value of its key in the state `s`. -/
def ReadsAgree (reads : GMap GoString ReadM) (s : List EtcdKv) : Prop :=
  ∀ k e, reads !! k = some e → kvAt s k = e.kv

/-- **A committed attempt** (pure): the commit's transaction ran at revision `R` on `s` (sorted,
under `pfx`) and left `s'`: `s'` is `s` with the writes' operations applied (in the write set's
order); `R` is at least `lo` if the transaction had an operation (it is then linearizable); all
levels but `ReadCommitted`: every read is `s`'s key-value of its key; `SerializableSnapshot`:
every written key's mod revision in `s` is at most `first()`. -/
def STMCommitted (pfx : GoString) (lvl lo : w64) (st : STMSt) (R : w64) (s s' : List EtcdKv)
    (ops : List TxnOp) : Prop :=
  EtcdStateWf pfx s ∧ s' = (runOps R s ops).1 ∧ WriteOpsOk st.writes ops ∧
    (ops ≠ [] → sint.Z lo ≤ sint.Z R) ∧ 0 < sint.Z R ∧ sint.Z R < 2 ^ 63 - 1 ∧
    (lvl ≠ isoRC → ReadsAgree st.reads s) ∧
    (lvl = isoSS → ∃ f, FirstOk st.reads f ∧
      ∀ k, (st.writes !! k).isSome → sint.Z (modRevAt s k) < sint.Z (f + W64 1))

/-- The reads grow from `reads` to `reads'`, by keys of `ks` only (an entry, once there, stays). -/
def ReadsGrow (reads reads' : GMap GoString ReadM) (ks : List GoString) : Prop :=
  (∀ k e, reads !! k = some e → reads' !! k = some e) ∧
    (∀ k, (reads' !! k).isSome → (reads !! k).isSome ∨ k ∈ ks)

/-- What `Get(keys...)` did, from `st` to `st'`, returning `v`: the writes are unchanged, the
reads grow (by keys of `keys` only); for no key `""`; otherwise `v` is, for some key `k` of
`keys`, its write's value, or (not written) its read's value. -/
def GetPost (ks : List GoString) (st : STMSt) (v : GoString) (st' : STMSt) : Prop :=
  st'.writes = st.writes ∧ ReadsGrow st.reads st'.reads ks ∧
    (ks = [] → v = []) ∧
    (ks ≠ [] → ∃ k ∈ ks, (∃ w, st.writes !! k = some w ∧ v = w.val) ∨
      (st.writes !! k = none ∧ ∃ e, st'.reads !! k = some e ∧ v = e.value))

/-- What `Rev(k)` did, from `st` to `st'`, returning `r`: the writes are unchanged, the reads
grow (by `k` only) and hold `k`, read with mod revision `r` (`0`: absent). -/
def RevPost (k : GoString) (st : STMSt) (r : w64) (st' : STMSt) : Prop :=
  st'.writes = st.writes ∧ ReadsGrow st.reads st'.reads [k] ∧
    ∃ e, st'.reads !! k = some e ∧ r = e.modRev

/-- The options of `Put(k, v, opts...)` the STM supports: `OpPut` does not panic and the
operation is a put of `k` with `v` (no `WithIgnoreValue`/`WithIgnoreLease`; a lease allowed). -/
def PutOptsOk (k v : GoString) (gs : List (OpFull → OpFull)) : Prop :=
  ¬ (opPutModel k v gs).putPanics ∧
    txnOpOf (opPutModel k v gs) = some (.put k v (opPutModel k v gs).leaseID)

/-- The options a `*stm`'s gets use (`getOpts`): none (`stmSerializable`'s first read, after a
failed commit), `WithSerializable()` (`RepeatableReads`, `ReadCommitted`), or
`WithRev(S), WithSerializable()` (the serializable levels after the first read). -/
def ReadOptsOk (gs : List (OpFull → OpFull)) : Prop :=
  gs = [] ∨ gs = [withSerializableM] ∨ ∃ S, gs = [withRevM S, withSerializableM]

/-- The options of the level `lvl`'s gets. -/
def GetOptsOk (lvl : w64) (gs : List (OpFull → OpFull)) : Prop :=
  if isoSer lvl then gs = [] ∨ ∃ S, gs = [withRevM S, withSerializableM]
  else gs = [withSerializableM]

/-! ## Options -/

/-- `stmOptions`, as the options change it: the isolation level and the keys to prefetch (the
context is any context, `stmOptionsOwn`). -/
structure STMOpts where
  iso : w64
  prefetch : List GoString

/-- What `NewSTM` starts from: `&stmOptions{ctx: c.Ctx()}`. -/
def STMOpts.init : STMOpts := { iso := W64 0, prefetch := [] }

/-- `WithIsolation(lvl)` -/
def withIsoM (lvl : w64) (o : STMOpts) : STMOpts := { o with iso := lvl }

/-- `WithPrefetch(keys...)` -/
def withPrefetchM (ks : List GoString) (o : STMOpts) : STMOpts :=
  { o with prefetch := o.prefetch ++ ks }

/-- The options' transformers applied in order (`NewSTM`'s loop). -/
def stmOptsFold (gs : List (STMOpts → STMOpts)) (o : STMOpts) : STMOpts :=
  gs.foldl (fun o g => g o) o

theorem stmOptsFold_take_succ (gs : List (STMOpts → STMOpts)) (o : STMOpts) (n : Nat)
    (g : STMOpts → STMOpts) (h : gs[n]? = some g) :
    stmOptsFold (gs.take (n + 1)) o = g (stmOptsFold (gs.take n) o) := by
  unfold stmOptsFold
  rw [List.take_add_one, h]
  simp

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- The `stm` of the STM `p` of level `lvl`: `p` itself for a `*stm`, the embedded field for a
`*stmSerializable`. -/
def stmBase (lvl : w64) (p : Loc) : Loc :=
  if isoSer lvl then structFieldRef stmSerializable go!"stm" p else p

/-- The STM `p` of level `lvl` as an `STM` interface value. -/
def stmIface (lvl : w64) (p : Loc) : GoInterfaceOk :=
  interface.mk (go.GoType.PointerType (if isoSer lvl then stmSerializable.ty else stm.ty)) #p

end addrs

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- The `*stmOptions` `p` holds `o` (owned): its level, its prefetch keys (an owned slice, with
its capacity: `WithPrefetch` appends), and some context. -/
def stmOptionsOwn (p : Loc) (o : STMOpts) : IProp GF :=
  iprop(∃ (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (sl : GoSlice),
    p ↦ ({ iso' := o.iso, ctx' := GoInterface.ok ctx, prefetch' := sl } : stmOptions) ∗
    sl ↦* o.prefetch ∗ ownSliceCap GoString sl (DFrac.own 1) ∗ context.isContext ctx cs)

/-- The `STMOption` closure `f` changes options modelled by `o` into `g o`. -/
def stmOptSpec (f : GoFunc) (g : STMOpts → STMOpts) : IProp GF :=
  iprop(□ ∀ (p : Loc) (o : STMOpts),
    {{ stmOptionsOwn p o }} (App (Val #f) (Val #p)) {{ RET #(); stmOptionsOwn p (g o) }})

instance stmOptSpec_persistent (f : GoFunc) (g : STMOpts → STMOpts) :
    Persistent (stmOptSpec (GF := GF) f g) := by
  unfold stmOptSpec; infer_instance

/-- The `[]STMOption` slice `sl` (read-only) holds closures with the transformers `gs`. -/
def stmOptsAt (sl : GoSlice) (gs : List (STMOpts → STMOpts)) : IProp GF :=
  iprop(∃ fs : List GoFunc, sl ↦*□ fs ∗ ⌜fs.length = gs.length⌝ ∗
    □ ∀ (i : Nat) (f : GoFunc) (g : STMOpts → STMOpts), ⌜fs[i]? = some f⌝ -∗
      ⌜gs[i]? = some g⌝ -∗ stmOptSpec f g)

instance stmOptsAt_persistent (sl : GoSlice) (gs : List (STMOpts → STMOpts)) :
    Persistent (stmOptsAt (GF := GF) sl gs) := by
  unfold stmOptsAt; infer_instance

/-! ## The client -/

/-- **The client, as an STM uses it** (persistent): its `KV` answers transactions
(`isEtcdTxnKV`, the commit) and read transactions (`isEtcdReadTxnKV`, the gets), for the prefix
`pfx`; its `ctx` field holds a context (`client.Ctx()`, `NewSTM`'s default). -/
def isEtcdSTMClient (client : Loc) (pfx : GoString) : IProp GF :=
  iprop(∃ (kv cctx : GoInterfaceOk) (ccs : context.ContextDesc (IProp GF)),
    clientKVAddr client ↦□ GoInterface.ok kv ∗ isEtcdTxnKV kv pfx ∗ isEtcdReadTxnKV kv pfx ∗
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"ctx" client ↦□ GoInterface.ok cctx ∗
    context.isContext cctx ccs)

instance isEtcdSTMClient_persistent (client : Loc) (pfx : GoString) :
    Persistent (isEtcdSTMClient (GF := GF) client pfx) := by
  unfold isEtcdSTMClient; infer_instance

/-! ## Reads and writes, in Go -/

/-- **A read's fact** (persistent): etcd's state at the read's revision (under `pfx`, sorted)
has the read key-value for `k` (under `pfx`). -/
def readFact (pfx k : GoString) (e : ReadM) : IProp GF :=
  iprop(∃ s : List EtcdKv, □ etcdState e.rev pfx s ∗
    ⌜EtcdStateWf pfx s ∧ kvAt s k = e.kv ∧ pfx <+: k⌝)

instance readFact_persistent (pfx k : GoString) (e : ReadM) :
    Persistent (readFact (GF := GF) pfx k e) := by
  unfold readFact; infer_instance

/-- The reads' facts. -/
def readFacts (pfx : GoString) (reads : GMap GoString ReadM) : IProp GF :=
  iprop(□ ∀ (k : GoString) (e : ReadM), ⌜reads !! k = some e⌝ -∗ readFact pfx k e)

instance readFacts_persistent (pfx : GoString) (reads : GMap GoString ReadM) :
    Persistent (readFacts (GF := GF) pfx reads) := by
  unfold readFacts; infer_instance

/-- The `*GetResponse` `p` (not nil, read-only) is the read `e` of `k`: its header has revision
`e.hdr`, its `Kvs` are the read key-value (if any), and `readFact`. -/
def readRespAt (pfx k : GoString) (p : Loc) (e : ReadM) : IProp GF :=
  iprop(⌜p ≠ null⌝ ∗ readFact pfx k e ∗
    (∃ h : Loc, structFieldRef go_etcd_io.etcd.client.v3.GetResponse go!"Header" p ↦□ h ∗
      ⌜h ≠ null⌝ ∗ structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦□ e.hdr) ∗
    (∃ (sl : GoSlice) (ps : List Loc),
      structFieldRef go_etcd_io.etcd.client.v3.GetResponse go!"Kvs" p ↦□ sl ∗ sl ↦*□ ps ∗
      kvPtrsAt ps e.kv.toList))

instance readRespAt_persistent (pfx k : GoString) (p : Loc) (e : ReadM) :
    Persistent (readRespAt (GF := GF) pfx k p e) := by
  unfold readRespAt; infer_instance

/-- The `*pb.ResponseOp` `p` (not nil, read-only) holds a range response that is the read `e` of
`k` (what `ResponseOp.GetResponseRange` returns: `rs.add`'s entries). -/
def respOpReadAt (pfx k : GoString) (p : Loc) (e : ReadM) : IProp GF :=
  iprop(⌜p ≠ null⌝ ∗ ∃ (w rr : Loc),
    structFieldRef etcdserverpb.ResponseOp go!"Response" p ↦□
      interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponseRange.ty) #w ∗
    structFieldRef etcdserverpb.ResponseOp_ResponseRange go!"ResponseRange" w ↦□ rr ∗
    readRespAt pfx k rr e)

instance respOpReadAt_persistent (pfx k : GoString) (p : Loc) (e : ReadM) :
    Persistent (respOpReadAt (GF := GF) pfx k p e) := by
  unfold respOpReadAt; infer_instance

/-- The map `rsMap` (key ↦ `*GetResponse`) holds the reads `reads`: the same keys, each
response its read (persistent). -/
def readsAt (pfx : GoString) (rsMap : GMap GoString Loc) (reads : GMap GoString ReadM) :
    IProp GF :=
  iprop(⌜∀ k, (rsMap !! k).isSome = (reads !! k).isSome⌝ ∗
    □ ∀ (k : GoString) (p : Loc) (e : ReadM), ⌜rsMap !! k = some p⌝ -∗ ⌜reads !! k = some e⌝ -∗
      readRespAt pfx k p e)

instance readsAt_persistent (pfx : GoString) (rsMap : GMap GoString Loc)
    (reads : GMap GoString ReadM) : Persistent (readsAt (GF := GF) pfx rsMap reads) := by
  unfold readsAt; infer_instance

/-- The `stmPut` value `sp` is the write `w` of `k` (under `pfx`): its value is `w`'s, its `Op`
the operation of `w` (persistent). -/
def writeAt (pfx k : GoString) (sp : stmPut) (w : WriteM) : IProp GF :=
  iprop(⌜sp.val' = w.val ∧ pfx <+: k⌝ ∗ ∃ o : OpFull, opFullAt sp.op' o ∗ ⌜txnOpOf o = some (w.op k)⌝)

instance writeAt_persistent (pfx k : GoString) (sp : stmPut) (w : WriteM) :
    Persistent (writeAt (GF := GF) pfx k sp w) := by
  unfold writeAt; infer_instance

/-- The map `wsMap` (key ↦ `stmPut`) holds the writes `writes` (persistent). -/
def writesAt (pfx : GoString) (wsMap : GMap GoString stmPut) (writes : GMap GoString WriteM) :
    IProp GF :=
  iprop(⌜∀ k, (wsMap !! k).isSome = (writes !! k).isSome⌝ ∗
    □ ∀ (k : GoString) (sp : stmPut) (w : WriteM), ⌜wsMap !! k = some sp⌝ -∗
      ⌜writes !! k = some w⌝ -∗ writeAt pfx k sp w)

instance writesAt_persistent (pfx : GoString) (wsMap : GMap GoString stmPut)
    (writes : GMap GoString WriteM) : Persistent (writesAt (GF := GF) pfx wsMap writes) := by
  unfold writesAt; infer_instance

/-! ## The fields of an STM -/

/-- The `stm` (struct) at `b`: its client and context (read-only), the client's contract for
`pfx` (persistent). -/
def stmEnv (pfx : GoString) (b : Loc) : IProp GF :=
  iprop(∃ (c : Loc) (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)),
    structFieldRef stm go!"client" b ↦□ c ∗ isEtcdSTMClient c pfx ∗
    structFieldRef stm go!"ctx" b ↦□ GoInterface.ok ctx ∗ context.isContext ctx cs)

instance stmEnv_persistent (pfx : GoString) (b : Loc) : Persistent (stmEnv (GF := GF) pfx b) := by
  unfold stmEnv; infer_instance

/-- The read set of the `stm` at `b` (its field and its map, owned) holds `reads`. -/
def stmRsetOwn (pfx : GoString) (b : Loc) (reads : GMap GoString ReadM) : IProp GF :=
  iprop(∃ (m : Loc) (rsMap : GMap GoString Loc), structFieldRef stm go!"rset" b ↦ m ∗
    m ↦$ rsMap ∗ readsAt pfx rsMap reads)

/-- The write set of the `stm` at `b` (its field and its map, owned) holds `writes`. -/
def stmWsetOwn (pfx : GoString) (b : Loc) (writes : GMap GoString WriteM) : IProp GF :=
  iprop(∃ (m : Loc) (wsMap : GMap GoString stmPut), structFieldRef stm go!"wset" b ↦ m ∗
    m ↦$ wsMap ∗ writesAt pfx wsMap writes)

/-- The get options of the `stm` at `b` (the field owned) are closures with transformers `gs`. -/
def stmOptsOwn (b : Loc) (gs : List (OpFull → OpFull)) : IProp GF :=
  iprop(∃ sl : GoSlice, structFieldRef stm go!"getOpts" b ↦ sl ∗ optsAt sl gs)

/-- **The conflicts closure** `f` of level `lvl` for the `stm` at `b`: called with the read and
write sets, it returns their comparisons (`ConflictsOk`) and leaves them. -/
def conflictsSpec (lvl : w64) (pfx : GoString) (b : Loc) (f : GoFunc) : IProp GF :=
  iprop(□ ∀ (reads : GMap GoString ReadM) (writes : GMap GoString WriteM),
    {{ stmRsetOwn pfx b reads ∗ stmWsetOwn pfx b writes }} (App (Val #f) (Val #()))
    {{ (sl : GoSlice), RET #sl; stmRsetOwn pfx b reads ∗ stmWsetOwn pfx b writes ∗
        ∃ ms : List CmpModel, cmpsAt sl ms ∗ ⌜ConflictsOk lvl reads writes ms⌝ }})

instance conflictsSpec_persistent (lvl : w64) (pfx : GoString) (b : Loc) (f : GoFunc) :
    Persistent (conflictsSpec (GF := GF) lvl pfx b f) := by
  unfold conflictsSpec; infer_instance

/-- The conflicts field of the `stm` at `b` holds, for good, a conflicts closure of level `lvl`. -/
def stmConflictsAt (lvl : w64) (pfx : GoString) (b : Loc) : IProp GF :=
  iprop(∃ f : GoFunc, structFieldRef stm go!"conflicts" b ↦□ f ∗ conflictsSpec lvl pfx b f)

instance stmConflictsAt_persistent (lvl : w64) (pfx : GoString) (b : Loc) :
    Persistent (stmConflictsAt (GF := GF) lvl pfx b) := by
  unfold stmConflictsAt; infer_instance

/-- The prefetched reads of the `*stmSerializable` `p` (the field and its map, owned) are `pre`,
reads of some keys, as the read set's (`readsAt`). -/
def stmPreOwn (pfx : GoString) (p : Loc) (pre : GMap GoString ReadM) : IProp GF :=
  iprop(∃ (m : Loc) (preMap : GMap GoString Loc),
    structFieldRef stmSerializable go!"prefetch" p ↦ m ∗ m ↦$ preMap ∗ readsAt pfx preMap pre)

/-- A key both read and prefetched is written (`Get` moves the prefetched reads of its keys to the
read set unless one of them is written, and `Rev` fetches a key whose `Get` returned its write):
so moving a prefetched read never replaces a read. -/
def PreOk (st : STMSt) (pre : GMap GoString ReadM) : Prop :=
  ∀ k, (st.reads !! k).isSome → (pre !! k).isSome → (st.writes !! k).isSome

/-- **The STM's state** (exclusive): the STM `p` of level `lvl`, for the client's prefix `pfx`,
holds the attempt `st` (its read and write sets), get options of its level, its conflicts
closure, and (serializable levels) prefetched reads (`PreOk`). -/
def stmState (lvl : w64) (pfx : GoString) (p : Loc) (st : STMSt) : IProp GF :=
  iprop(stmEnv pfx (stmBase lvl p) ∗ stmRsetOwn pfx (stmBase lvl p) st.reads ∗
    stmWsetOwn pfx (stmBase lvl p) st.writes ∗
    (∃ gs : List (OpFull → OpFull), stmOptsOwn (stmBase lvl p) gs ∗ ⌜GetOptsOk lvl gs⌝) ∗
    stmConflictsAt lvl pfx (stmBase lvl p) ∗
    (if isoSer lvl then iprop(∃ pre, stmPreOwn pfx p pre ∗ ⌜PreOk st pre⌝) else iprop(True)))

/-- **The STM's state before `reset`**: as `stmState`, but the read and write set fields hold
anything (nil maps after `mkSTM`; the prefetch map after a failed serializable commit). -/
def stmStale (lvl : w64) (pfx : GoString) (p : Loc) : IProp GF :=
  iprop(stmEnv pfx (stmBase lvl p) ∗
    (∃ m : Loc, structFieldRef stm go!"rset" (stmBase lvl p) ↦ m) ∗
    (∃ m : Loc, structFieldRef stm go!"wset" (stmBase lvl p) ↦ m) ∗
    (∃ gs : List (OpFull → OpFull), stmOptsOwn (stmBase lvl p) gs ∗ ⌜GetOptsOk lvl gs⌝) ∗
    stmConflictsAt lvl pfx (stmBase lvl p) ∗
    (if isoSer lvl then iprop(∃ pre, stmPreOwn pfx p pre) else iprop(True)))

/-! ## A committed attempt -/

/-- **What a successful commit gives** (persistent), for the attempt `st` of level `lvl`, called
knowing that etcd has reached `lo`: a revision `R`, the state `s` the transaction ran on and the
state `s'` it left (`txnStates`: if it wrote, etcd's states at `R - 1` and `R`; otherwise `s = s'`
is etcd's state at `R`), the operations `ops` of the write set, `STMCommitted`, the reads' facts,
and the response (`resp`'s header revision `R`, `Succeeded`, the puts' responses). -/
def stmOutcome (pfx : GoString) (lvl lo : w64) (st : STMSt) (resp : Loc) : IProp GF :=
  iprop(∃ (R : w64) (s s' : List EtcdKv) (ops : List TxnOp),
    txnStates pfx R s s' (txnWrote (runOps R s ops).2) ∗ etcdReached R ∗
    readFacts pfx st.reads ∗ ⌜STMCommitted pfx lvl lo st R s s' ops⌝ ∗
    txnRespAt resp R true ops (runOps R s ops).2)

instance stmOutcome_persistent (pfx : GoString) (lvl lo : w64) (st : STMSt) (resp : Loc) :
    Persistent (stmOutcome (GF := GF) pfx lvl lo st resp) := by
  unfold stmOutcome; infer_instance

/-- **What `NewSTM` (and `runSTM`) return**: an error; or `nil` with a committed attempt whose
state `st` satisfies the closure's `Q`. -/
def stmResult (pfx : GoString) (lvl lo : w64) (Q : STMSt → Prop) (resp : Loc)
    (err : GoInterface) : IProp GF :=
  iprop(⌜err ≠ GoInterface.nil⌝ ∨
    (⌜err = GoInterface.nil⌝ ∗ ∃ st : STMSt, ⌜Q st⌝ ∗ stmOutcome pfx lvl lo st resp))

instance stmResult_persistent (pfx : GoString) (lvl lo : w64) (Q : STMSt → Prop) (resp : Loc)
    (err : GoInterface) : Persistent (stmResult (GF := GF) pfx lvl lo Q resp err) := by
  unfold stmResult; infer_instance

/-! ## The interface's methods and the closure -/

/-- **The STM's methods** (persistent): the triples of the `STM` interface's methods on the STM
`p` of level `lvl` (`stmIface`), over its state. `Get(keys...)` (keys under `pfx`): `GetPost`;
`Put(k, v, opts...)`: the write set gets the put; `Rev(k)`: `RevPost`; `Del(k)`: the write set
gets the delete; `commit()`: `nil` (failed) or a response with `stmOutcome`, leaving the state
stale; `reset()`: from a stale state, a fresh attempt. A client error aborts `Get`, `Rev` and
`commit` (a panic `runSTM` recovers: they do not return, `stmPanic.spec`). -/
def stmMethods (lvl : w64) (pfx : GoString) (p : Loc) : IProp GF :=
  iprop(
    (□ ∀ (st : STMSt) (sl : GoSlice) (ks : List GoString),
      {{ stmState lvl pfx p st ∗ sl ↦*□ ks ∗ ⌜∀ k ∈ ks, pfx <+: k⌝ }}
        (App (Val #(methods (stmIface lvl p).ty go!"Get" (stmIface lvl p).v)) (Val #sl))
      {{ (v : GoString), RET #v; ∃ st', stmState lvl pfx p st' ∗ ⌜GetPost ks st v st'⌝ }}) ∗
    (□ ∀ (st : STMSt) (k v : GoString) (sl : GoSlice) (gs : List (OpFull → OpFull)),
      {{ stmState lvl pfx p st ∗ optsAt sl gs ∗ ⌜pfx <+: k ∧ PutOptsOk k v gs⌝ }}
        (App (App (App (Val #(methods (stmIface lvl p).ty go!"Put" (stmIface lvl p).v))
          (Val #k)) (Val #v)) (Val #sl))
      {{ RET #(); stmState lvl pfx p
          { st with writes := GMap.insert k (.put v (opPutModel k v gs).leaseID) st.writes } }}) ∗
    (□ ∀ (st : STMSt) (k : GoString),
      {{ stmState lvl pfx p st ∗ ⌜pfx <+: k⌝ }}
        (App (Val #(methods (stmIface lvl p).ty go!"Rev" (stmIface lvl p).v)) (Val #k))
      {{ (r : w64), RET #r; ∃ st', stmState lvl pfx p st' ∗ ⌜RevPost k st r st'⌝ }}) ∗
    (□ ∀ (st : STMSt) (k : GoString),
      {{ stmState lvl pfx p st ∗ ⌜pfx <+: k⌝ }}
        (App (Val #(methods (stmIface lvl p).ty go!"Del" (stmIface lvl p).v)) (Val #k))
      {{ RET #(); stmState lvl pfx p { st with writes := GMap.insert k .del st.writes } }}) ∗
    (□ ∀ (st : STMSt) (lo : w64),
      {{ stmState lvl pfx p st ∗ etcdReached lo }}
        (App (Val #(methods (stmIface lvl p).ty go!"commit" (stmIface lvl p).v)) (Val #()))
      {{ (resp : Loc), RET #resp; stmStale lvl pfx p ∗
          (⌜resp = null⌝ ∨ ⌜resp ≠ null⌝ ∗ stmOutcome pfx lvl lo st resp) }}) ∗
    (□ {{ stmStale lvl pfx p }}
        (App (Val #(methods (stmIface lvl p).ty go!"reset" (stmIface lvl p).v)) (Val #()))
      {{ RET #(); stmState lvl pfx p STMSt.empty }}))

instance stmMethods_persistent (lvl : w64) (pfx : GoString) (p : Loc) :
    Persistent (stmMethods (GF := GF) (hG := hG) lvl pfx p) := by
  unfold stmMethods; infer_instance

/-- **The user's closure** `apply` (`func(STM) error`; persistent: `runSTM` calls it once per
attempt): on any STM with the methods' triples, from any state, it returns an error or `nil`, in
some state, and `nil` means the attempt's reads and writes satisfy `Q`. It may only use the
STM through `Get`, `Put`, `Rev`, `Del` (it has no triple of `commit`/`reset`), and must not
recover a panic (the STM's aborts are panics `runSTM` recovers). -/
def applySpec (pfx : GoString) (apply : GoFunc) (Q : STMSt → Prop) : IProp GF :=
  iprop(□ ∀ (lvl : w64) (p : Loc) (st : STMSt), stmMethods lvl pfx p -∗
    {{ stmState lvl pfx p st }}
      (App (Val #apply) (Val #(GoInterface.ok (stmIface lvl p))))
    {{ (err : GoInterface), RET #err;
        ∃ st', stmState lvl pfx p st' ∗ ⌜err = GoInterface.nil → Q st'⌝ }})

instance applySpec_persistent (pfx : GoString) (apply : GoFunc) (Q : STMSt → Prop) :
    Persistent (applySpec (GF := GF) (hG := hG) pfx apply Q) := by
  unfold applySpec; infer_instance

end defs

end concurrency
end EtcdGrove
end Perennial
