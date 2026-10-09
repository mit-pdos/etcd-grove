/-
The etcd model: what etcd's cache knows of etcd itself, its trust boundary (Lean-first, no
Rocq counterpart; the Rocq development's `is_etcd_kvs` is the precedent). See `decisions.md`,
"the etcd model".

**etcd's state.** `etcdState rev pfx s` (an axiom, with `etcdState_agree`) says that etcd's
key-value state at revision `rev`, restricted to the keys with prefix `pfx`, is `s`: the
key-values as etcd stores them (`EtcdKv`: key, value, create and mod revisions, version,
lease), by key. It is a fact about the server, which Goose does not model, hence an opaque
predicate. Its one property is **agreement**: etcd has one state per revision. That is all
the cache's proofs need of etcd; everything else is said by the client's statements, which
produce `etcdState` facts.

**Maps.** The cache keeps maps of `(key, *KeyValue)` (`KvMap`, `InvStore.lean`), and a
`*KeyValue` is a fresh allocation in every response, so the model is about contents, not
pointers: `isEtcdKvs rev pfx m` says that the map `m`'s entries are, in order, etcd's state
`s` at `rev` (`□ etcdState rev pfx s`), with each `*KeyValue` holding (read-only) the
corresponding `EtcdKv` (`kvValAt`), keys strictly increasing, all with prefix `pfx`. It is
persistent, and two of them at the same revision have the same keys and contents
(`isEtcdKvs_agree`). It is the store's certificate in the cache (`etcdCert`).

**The client.** `isEtcdKV kv pfx` is the triple of `kv.Get(ctx, key, opts...)` on the
`clientv3.KV` interface value `kv`, for a cache of prefix `pfx`, at the strength of etcd's
documented API: any error is possible; on success the response's header has a revision `r`
at which etcd had a state, and a prefix get (`OpFull.isPrefixGet`: `WithPrefix` on `pfx`, no
revision, limit, sort, filters, keys-only or count-only) lists exactly that state, `r`'s.
It is a definition (as Perennial's `isLocker` is), not an axiom: the cache's specs take it as
a premise, and the client axiom is what a caller will have to assume of `client.KV`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvStore
public import Proof.go_etcd_io.etcd.client.v3.InvOp

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

/-! ## etcd's state -/

/-- A key-value as etcd stores it (`mvccpb.KeyValue`'s fields). -/
structure EtcdKv where
  key : GoString
  createRev : w64
  modRev : w64
  version : w64
  value : GoString
  lease : w64

/-- etcd's key-value state at revision `rev`, restricted to the keys with prefix `pfx`, is `s`
(sorted by key). A fact about the etcd server, which is not modelled: an axiom. -/
axiom etcdState {GF : BundledGFunctors} (rev : w64) (pfx : GoString) (s : List EtcdKv) :
  IProp GF

/-- etcd has one state per revision. -/
axiom etcdState_agree {GF : BundledGFunctors} (rev : w64) (pfx : GoString)
    (s s' : List EtcdKv) :
  etcdState (GF := GF) rev pfx s ∗ etcdState rev pfx s' ⊢ ⌜s = s'⌝

/-- The keys of `s` are strictly increasing and have the prefix `pfx`. -/
def EtcdStateWf (pfx : GoString) (s : List EtcdKv) : Prop :=
  (s.map EtcdKv.key).Pairwise go.GoStringLt ∧ ∀ v ∈ s, pfx <+: v.key

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `l` is a `*mvccpb.KeyValue` whose fields hold `v`, read-only (on the fields, as `kvAt`). -/
def kvValAt (l : Loc) (v : EtcdKv) : IProp GF :=
  iprop(∃ keySl valSl : GoSlice,
    structFieldRef mvccpb.KeyValue go!"Key" l ↦□ keySl ∗ keySl ↦*□ v.key ∗
    structFieldRef mvccpb.KeyValue go!"CreateRevision" l ↦□ v.createRev ∗
    structFieldRef mvccpb.KeyValue go!"ModRevision" l ↦□ v.modRev ∗
    structFieldRef mvccpb.KeyValue go!"Version" l ↦□ v.version ∗
    structFieldRef mvccpb.KeyValue go!"Value" l ↦□ valSl ∗ valSl ↦*□ v.value ∗
    structFieldRef mvccpb.KeyValue go!"Lease" l ↦□ v.lease)

instance kvValAt_persistent (l : Loc) (v : EtcdKv) : Persistent (kvValAt (GF := GF) l v) := by
  unfold kvValAt; infer_instance

/-- The `*KeyValue`s of `m` hold, in order, the key-values `s`. -/
def kvValsAt (m : KvMap) (s : List EtcdKv) : IProp GF :=
  iprop(□ ∀ (i : Nat) (e : KvEntry) (v : EtcdKv), ⌜m[i]? = some e⌝ -∗ ⌜s[i]? = some v⌝ -∗
    kvValAt e.2 v)

instance kvValsAt_persistent (m : KvMap) (s : List EtcdKv) :
    Persistent (kvValsAt (GF := GF) m s) := by
  unfold kvValsAt; infer_instance

/-- The map `m` is etcd's state at revision `rev`, restricted to the prefix `pfx`. -/
def isEtcdKvs (rev : w64) (pfx : GoString) (m : KvMap) : IProp GF :=
  iprop(∃ s : List EtcdKv, □ etcdState rev pfx s ∗ ⌜m.map Prod.fst = s.map EtcdKv.key⌝ ∗
    ⌜EtcdStateWf pfx s⌝ ∗ kvValsAt m s)

instance isEtcdKvs_persistent (rev : w64) (pfx : GoString) (m : KvMap) :
    Persistent (isEtcdKvs (GF := GF) rev pfx m) := by
  unfold isEtcdKvs; infer_instance

/-- Two maps that are etcd's state at the same revision have the same keys and contents. -/
theorem isEtcdKvs_agree (rev : w64) (pfx : GoString) (m m' : KvMap) :
    isEtcdKvs (GF := GF) rev pfx m ∗ isEtcdKvs rev pfx m' ⊢
      ⌜m.map Prod.fst = m'.map Prod.fst⌝ ∗ ∃ s, kvValsAt m s ∗ kvValsAt m' s := by
  unfold isEtcdKvs
  iintro ⟨⟨%s, #Hs, %Hk, %-, #Hv⟩, ⟨%s', #Hs', %Hk', %-, #Hv'⟩⟩
  ihave %Heq := etcdState_agree rev pfx s s' $$ [$Hs $Hs']
  subst Heq
  isplitr
  · ipureintro; rw [Hk, Hk']
  iexists s
  isplitl []
  · iexact Hv
  · iexact Hv'

/-- The cache's store certificate: a snapshot `(r, m)` is etcd's state at `r`, restricted to the
cache's prefix. -/
def etcdCert (pfx : GoString) : w64 → KvMap → IProp GF := fun r m => isEtcdKvs r pfx m

/-! ## The client's `KV.Get` -/

/-- The `*clientv3.GetResponse` `resp` has a header (non-nil) with revision `r`, read-only. -/
def getRespRev (resp : Loc) (r : w64) : IProp GF :=
  iprop(∃ hdr : Loc, structFieldRef go_etcd_io.etcd.client.v3.GetResponse go!"Header" resp ↦□ hdr ∗
    ⌜hdr ≠ null⌝ ∗ structFieldRef etcdserverpb.ResponseHeader go!"Revision" hdr ↦□ r)

instance getRespRev_persistent (resp : Loc) (r : w64) :
    Persistent (getRespRev (GF := GF) resp r) := by
  unfold getRespRev; infer_instance

/-- The `*clientv3.GetResponse` `resp` lists the `*KeyValue`s of `m`, read-only. -/
def getRespKvs (resp : Loc) (m : KvMap) : IProp GF :=
  iprop(∃ sl : GoSlice, structFieldRef go_etcd_io.etcd.client.v3.GetResponse go!"Kvs" resp ↦□ sl ∗
    sl ↦*□ (m.map Prod.snd))

instance getRespKvs_persistent (resp : Loc) (m : KvMap) :
    Persistent (getRespKvs (GF := GF) resp m) := by
  unfold getRespKvs; infer_instance

end defs

/-- A get of every key with the prefix `pfx` at the latest revision: what `WithPrefix()` makes of
`OpGet(pfx)` (from `"\x00"` on for the empty prefix), and no other option that changes the answer
(revision, limit, sort, revision filters, keys-only, count-only; serializable is allowed). -/
def OpFull.isPrefixGet (pfx : GoString) (o : OpFull) : Bool :=
  decide (o.t = W64 1 ∧ o.keysOnly = false ∧ o.base.countOnly = false ∧ o.base.sortSet = false ∧
    o.base.limit = W64 0 ∧ o.base.rev = W64 0 ∧ o.base.minModRev = W64 0 ∧
    o.base.maxModRev = W64 0 ∧ o.base.minCreateRev = W64 0 ∧ o.base.maxCreateRev = W64 0 ∧
    (if pfx = [] then o.key = [W8 0] ∧ o.base.rangeEnd = [W8 0]
     else o.key = pfx ∧ o.base.rangeEnd = prefixRangeEnd pfx))

section client
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- What `kv.Get` returns for the `Op` `o`, on a cache of prefix `pfx`: any error; or, on success,
a response whose header revision `r` is one at which etcd had a state, and which lists exactly
that state if `o` is a prefix get. -/
def kvGetResult (pfx : GoString) (o : OpFull) (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop(⌜err ≠ GoInterface.nil⌝ ∨
    (⌜err = GoInterface.nil⌝ ∗ ∃ (r : w64) (m : KvMap), getRespRev resp r ∗ isEtcdKvs r pfx m ∗
      (if o.isPrefixGet pfx then getRespKvs resp m else iprop(True))))

instance kvGetResult_persistent (pfx : GoString) (o : OpFull) (resp : Loc) (err : GoInterface) :
    Persistent (kvGetResult (GF := GF) pfx o resp err) := by
  unfold kvGetResult; split <;> infer_instance

/-- The `clientv3.KV` interface value `kv` talks to etcd, for a cache of prefix `pfx`: the triple
of its `Get(ctx, key, opts...)` (a range request: `OpGet(key, opts...)` must not panic and must
be a range), with any context, options with model transformers `gs`. -/
def isEtcdKV (kv : GoInterfaceOk) (pfx : GoString) : IProp GF :=
  iprop(□ ∀ (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (key : GoString)
      (sl : GoSlice) (gs : List (OpFull → OpFull)),
    {{ context.isContext ctx cs ∗ optsAt sl gs ∗
        ⌜¬ opGetPanics gs ∧ (opGetModel key gs).t = W64 1⌝ }}
      (App (App (App (Val #(methods kv.ty go!"Get" kv.v)) (Val #(GoInterface.ok ctx)))
        (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        kvGetResult pfx (opGetModel key gs) resp err }})

instance isEtcdKV_persistent (kv : GoInterfaceOk) (pfx : GoString) :
    Persistent (isEtcdKV (GF := GF) kv pfx) := by
  unfold isEtcdKV; infer_instance

end client

end EtcdGrove
end Perennial
