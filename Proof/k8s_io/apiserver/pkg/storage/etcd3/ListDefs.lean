/-
Lean-first (no Rocq counterpart).

# The store's lists: vocabulary (stage 7e-2 of `notes/k8s-7e-scope.md`; `notes/k8s-7e-2-draft.md`
§1 with its "Corrections (2026-11-09)")

- `kInScope kp recur k`: a list's scope (recursive, the keys under the prepared prefix `kp`; not
  recursive, `kp` itself);
- `kListL dec sel lim kp recur s`: the store's list over the store `s` at the read revision, through
  7e-3a's loop (`ListModel.loop`): the first `lim` key-values in scope the predicate selects, whether
  a key in scope follows the `lim`-th match, the last match's key, the count of the scope;
- `limN`: a list's limit as a count; `listRevL`: the revision a list reads (`ValidateListOptions`);
- `kvSameHist σ σ'`: two states of one history (`kvSameHist_at`: they agree at every revision both
  keep); `kvWfHist c σ`: every revision's key-values under the store's prefix decode;
  `kvKeysShort σ`: every revision holds fewer than `2 ^ 41` key-values, each key shorter than
  `opKeyMax` (correction G3).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Store
public import Proof.k8s_io.component_base.tracing.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ListModel
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.KList

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver reflectM

/-! ## The pure part -/

section pure
variable [GooseExts]
variable {Obj : Type}

/-- **A list's scope** (`store.go:1081-1100`): recursive, the keys under the prepared prefix `kp`
(`kubernetes.Client.List`'s range `[kp, GetPrefixRangeEnd kp)`, `client.go:59-73`); not recursive,
the key `kp` itself (`kubernetes.Client.Get`, `client.go:47-57`). -/
def kInScope (kp : GoString) (recur : Bool) (k : GoString) : Bool :=
  if recur then decide (kp <+: k) else decide (k = kp)

/-- **The store's list over the store `s` at the list's revision**: the key-values of the scope in
key order, each decoded by `dec` (`ObjSpec.dec`) with its mod revision, through 7e-3a's loop
(`ListModel.loop`): the first `lim` the predicate `sel` selects (all for `lim = 0`), whether a key in
scope follows the `lim`-th match (`more`), the last match's key, and the count of keys in scope. -/
def kListL (dec : Dec Obj) (sel : Obj → Bool) (lim : Nat) (kp : GoString) (recur : Bool)
    (s : KVStore) : k8s_etcd3.ListModel.LState w8 (Obj × Nat) :=
  k8s_etcd3.ListModel.loop (fun x => sel x.1) lim
    ((s.kvs.filter fun v => kInScope kp recur v.key).filterMap fun v =>
      (dec v.value).map fun d => (v.key, (d.1, sint.nat v.modRev)))

/-- A list's limit as a count (`opts.Predicate.Limit`; none for `≤ 0`). -/
def limN (l : w64) : Nat := if 0 < sint.Z l then sint.nat l else 0

/-- **Two states of one history**: the same base and compaction revision, one's changes a prefix
of the other's (so they agree at every revision both keep: `kvSameHist_at`). -/
def kvSameHist (σ σ' : KVState) : Prop :=
  σ.compacted = σ'.compacted ∧ σ.base = σ'.base ∧
    (σ.changes <+: σ'.changes ∨ σ'.changes <+: σ.changes)

theorem take_of_prefix {α : Type} {l l' : List α} (h : l <+: l') (n : Nat) (hn : n ≤ l.length) :
    l.take n = l'.take n := by
  obtain ⟨t, rfl⟩ := h
  rw [List.take_append_of_le_length hn]

theorem kvSameHist_at (σ σ' : KVState) (r : Nat) (h : kvSameHist σ σ') (hr : r ≤ σ.rev)
    (hr' : r ≤ σ'.rev) : σ.at r = σ'.at r := by
  obtain ⟨hc, hb, hp⟩ := h
  unfold KVState.at
  rw [hc, hb]
  unfold KVState.rev at hr hr'
  split
  · rfl
  · congr 2
    rcases hp with hp | hp
    · exact take_of_prefix hp _ (by omega)
    · exact (take_of_prefix hp _ (by omega)).symm

/-- **The revision a list reads** (`ValidateListOptions`, `interfaces.go:372-410`): its resource
version `n` for `Exact`, and for the legacy match when recursive with a limit and `n > 0`; else
(`0`) the latest. -/
def listRevL (m : GoString) (recur : Bool) (lim : w64) (n : w64) : w64 :=
  if m = go!"Exact" then n
  else if m = [] ∧ recur = true ∧ 0 < sint.Z lim ∧ 0 < uint.Z n then n else W64 0

/-- **Every revision's key-values are few and their keys short** (correction G3): fewer than
`2 ^ 41` key-values (a response's `Count` and the metrics' sums stay below `2 ^ 63`), each key
shorter than `opKeyMax` (a later page's start key, the last key and `"\x00"`, is a key
`Client.List` takes). -/
def kvKeysShort (σ : KVState) : Prop :=
  ∀ R ≤ σ.rev, (σ.at R).kvs.length < 2 ^ 41 ∧
    ∀ kv ∈ (σ.at R).kvs, kv.key.length < opKeyMax

/-- **A chunk's loop** (Draft §3.4's `ListModel.chunkL`; here to spare the driver a rebuild): 7e-3a's
`lstep` on the chunk's items, stopping once `more` is set (`appendChunk` returns at the item that
finds the limit reached). -/
def chunkL {α O : Type} (sel : O → Bool) (lim : Nat) :
    k8s_etcd3.ListModel.LState α O → List (List α × O) → k8s_etcd3.ListModel.LState α O
  | st, [] => st
  | st, ko :: r => if st.more then st else chunkL sel lim (k8s_etcd3.ListModel.lstep sel lim st ko) r

theorem chunkL_append {α O : Type} (sel : O → Bool) (lim : Nat) :
    ∀ (st : k8s_etcd3.ListModel.LState α O) (l1 l2 : List (List α × O)),
      chunkL sel lim st (l1 ++ l2) = chunkL sel lim (chunkL sel lim st l1) l2
  | st, [], l2 => rfl
  | st, ko :: l1, l2 => by
    simp only [List.cons_append, chunkL]
    split
    · rename_i h
      cases l2 with
      | nil => rfl
      | cons _ _ => simp [chunkL, h]
    · exact chunkL_append sel lim _ l1 l2

theorem chunkL_more {α O : Type} (sel : O → Bool) (lim : Nat)
    (st : k8s_etcd3.ListModel.LState α O) (h : st.more = true) :
    ∀ l, chunkL sel lim st l = st
  | [] => rfl
  | _ :: _ => by simp [chunkL, h]

/-- **A chunk's key-values decoded** (Draft §3.4): each key with its object and mod revision. -/
def decodedL (dec : Dec Obj) (kvs : List EtcdKv) : List (GoString × (Obj × Nat)) :=
  kvs.filterMap fun v => (dec v.value).map fun d => (v.key, (d.1, sint.nat v.modRev))

end pure

/-! ## The store's part -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.client.v3.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable {Obj : Type} [DecidableEq Obj]

/-- **Every revision of `σ` is the store's** (D30i, at each revision a past read may read): the key-
values under the prefix decode, and (B3, decided by etcd-grove-81) every mod revision is positive and at
most `r` (as `KWf`'s). -/
def kvWfHist (c : StoreCfg GF Obj) (σ : KVState) : Prop :=
  ∀ r, r ≤ σ.rev → ∀ v ∈ (σ.at r).kvs, (c.pfx <+: v.key → c.S.dec v.value ≠ none) ∧
    0 < uint.nat v.modRev ∧ uint.nat v.modRev ≤ r

/-- **The default gate has `EtcdRangeStream` off** (Draft §2, #13, persistent): the gate
`DefaultFeatureGate` holds (read-only, as `features`' fact `featuresInit` says) had
`Set("EtcdRangeStream=false")` succeed. Producer: the driver's `noStreaming` before `etcd3.New`. -/
def rangeStreamOff : IProp GF :=
  iprop(∃ g : GoInterfaceOk,
    globalAddr k8s_io.apiserver.pkg.util.feature.DefaultFeatureGate ↦□ GoInterface.ok g ∗
    k8sfeature.featureOff g go!"EtcdRangeStream")

instance rangeStreamOff_persistent : Persistent (rangeStreamOff (GF := GF)) := by
  unfold rangeStreamOff; infer_instance

/-- **`newItemFunc` makes a fresh zero object** (persistent; Draft §3.2), as `NewFunc()` does
(`ObjSpec.newObj`). -/
def newItemOk (S : ObjSpec GF Obj) (f : GoFunc) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, ▷ (∀ x, S.objAt x S.zero [] -∗ Φ #x) -∗
    WP (App (Val #f) (Val #())) {{ Φ }})

instance newItemOk_persistent (S : ObjSpec GF Obj) (f : GoFunc) :
    Persistent (newItemOk S f) := by
  unfold newItemOk; infer_instance

/-- `rem` holds the remaining count `remV`: `nil` for `none`, a cell holding `n` for `some n`
(`PrepareContinueToken`'s `*int64`). -/
def remIs (rem : Loc) : Option w64 → IProp GF
  | none => iprop(⌜rem = null⌝)
  | some n => iprop(rem ↦ n)

/-- **The list objects** (Draft §6): a list type, where its items slice is, what the items hold
(bodies and resource version strings, with the slice's capacity), and the list's metadata. -/
structure ListSpec (GF : BundledGFunctors) (Obj : Type) where
  listTy : go.GoType
  itemsRef : Loc → Loc
  /-- `itemsAt s os`: the slice `s` holds the items `os`, with its capacity -/
  itemsAt : GoSlice → List (Obj × GoString) → IProp GF
  itemsAt_nil : ⊢ itemsAt slice.nil []
  /-- the slice's length is the item count (revision after the attack, change 4) -/
  itemsAt_len : ∀ s os, itemsAt s os ⊢ ⌜uint.nat s.len = os.length⌝
  /-- the slice is well formed, its capacity at least its length (`ownSliceCap_wf`; a form settled
  at Prove: `growSlice`'s `MakeSlice(rt, v.Len(), max)` needs `len ≤ max` from `max > cap`) -/
  itemsAt_wf : ∀ s os, itemsAt s os ⊢ ⌜0 ≤ sint.Z s.len ∧ sint.Z s.len ≤ sint.Z s.cap⌝
  /-- the list's `ListMeta`: resource version, continue token, remaining count -/
  metaAt : Loc → w64 → GoString → Option w64 → IProp GF

/-- The list at `pl` with its items and metadata. -/
def ListSpec.listAtItems (L : ListSpec GF Obj) (pl : Loc) (os : List (Obj × GoString)) (rv : w64)
    (cont : GoString) (rem : Option w64) : IProp GF :=
  iprop(⌜pl ≠ null⌝ ∗ ∃ s, L.itemsRef pl ↦ s ∗ L.itemsAt s os ∗ L.metaAt pl rv cont rem)

/-- The list object `lx` (a `*listTy`) with its items and metadata. -/
def ListSpec.listAt (L : ListSpec GF Obj) (lx : GoInterface) (os : List (Obj × GoString))
    (rv : w64) (cont : GoString) (rem : Option w64) : IProp GF :=
  iprop(∃ pl, ⌜lx = interface.mkOk (go.GoType.PointerType L.listTy) #pl⌝ ∗
    L.listAtItems pl os rv cont rem)

/-- **The reflect calls on the items** (Draft §6, #9 at the store's abstract element type; the
`…` spots filled at Prove, one clause per call): `meta.GetItemsPtr` of a list; `MakeSlice(rt, 0,
m)`, an empty items slice; `MakeSlice(rt, n, m)` for `n` items, whose `Copy(w, v)` then moves the
items of `v`'s slice into it (`growSlice`); `Append(v, [e])` of an object, one item more
(`processListItem`). -/
def listContractOk' (S : ObjSpec GF Obj) (L : ListSpec GF Obj) : IProp GF :=
  iprop(
    (□ ∀ (pl : Loc) (Φ : val → IProp GF), ⌜pl ≠ null⌝ -∗
      ▷ Φ (PairV #(interface.mkOk (go.GoType.PointerType (go.GoType.SliceType S.objTy))
          #(L.itemsRef pl) : GoInterface) #GoInterface.nil) -∗
      WP (App (Val (@! k8s_io.apimachinery.pkg.api.«meta».GetItemsPtr))
        (Val #(interface.mkOk (go.GoType.PointerType L.listTy) #pl : GoInterface))) {{ Φ }}) ∗
    (□ ∀ (rt : _root_.Perennial.reflect.Type') (m : w64) (Φ : val → IProp GF),
      ⌜reflType rt (go.GoType.SliceType S.objTy) ∧ 0 ≤ sint.Z m ∧ sint.Z m ≤ 2 ^ 41⌝ -∗
      ▷ (∀ (w : _root_.Perennial.reflect.Value) (s' : GoSlice), ⌜reflSliceV w S.objTy s'⌝ -∗
          L.itemsAt s' [] -∗ Φ #w) -∗
      WP (App (App (App (Val (@! _root_.Perennial.reflect.MakeSlice)) (Val #rt)) (Val #(W64 0)))
        (Val #m)) {{ Φ }}) ∗
    (□ ∀ (rt : _root_.Perennial.reflect.Type') (n m : w64) (os : List (Obj × GoString))
        (Φ : val → IProp GF),
      ⌜reflType rt (go.GoType.SliceType S.objTy) ∧ sint.nat n = os.length ∧ 0 ≤ sint.Z n ∧
        sint.Z n ≤ sint.Z m ∧ sint.Z m ≤ 2 ^ 41⌝ -∗
      ▷ (∀ (w : _root_.Perennial.reflect.Value) (s' : GoSlice), ⌜reflSliceV w S.objTy s'⌝ -∗
          (∀ (v : _root_.Perennial.reflect.Value) (p : Loc) (dq : DFrac) (s : GoSlice)
              (Ψ : val → IProp GF),
            ⌜reflElem v (go.GoType.SliceType S.objTy) p⌝ -∗ p ↦{dq} s -∗ L.itemsAt s os -∗
            ▷ (∀ r : w64, p ↦{dq} s -∗ L.itemsAt s' os -∗ Ψ #r) -∗
            WP (App (App (Val (@! _root_.Perennial.reflect.Copy)) (Val #w)) (Val #v)) {{ Ψ }}) -∗
          Φ #w) -∗
      WP (App (App (App (Val (@! _root_.Perennial.reflect.MakeSlice)) (Val #rt)) (Val #n))
        (Val #m)) {{ Φ }}) ∗
    (□ ∀ (v : _root_.Perennial.reflect.Value) (p : Loc) (dq : DFrac) (s : GoSlice)
        (os : List (Obj × GoString)) (e : _root_.Perennial.reflect.Value) (esl : GoSlice)
        (dqe : DFrac) (q : Loc) (o : Obj) (rv : GoString) (Φ : val → IProp GF),
      ⌜reflElem v (go.GoType.SliceType S.objTy) p ∧ reflElem e S.objTy q⌝ -∗
      p ↦{dq} s -∗ L.itemsAt s os -∗ esl ↦*{dqe} [e] -∗
      S.objAt (interface.mkOk (go.GoType.PointerType S.objTy) #q) o rv -∗
      ▷ (∀ (w : _root_.Perennial.reflect.Value) (s' : GoSlice), ⌜reflSliceV w S.objTy s'⌝ -∗
          p ↦{dq} s -∗ L.itemsAt s' (os ++ [(o, rv)]) -∗ esl ↦*{dqe} [e] -∗
          S.objAt (interface.mkOk (go.GoType.PointerType S.objTy) #q) o rv -∗ Φ #w) -∗
      WP (App (App (Val (@! _root_.Perennial.reflect.Append)) (Val #v)) (Val #esl)) {{ Φ }}))

instance listContractOk'_persistent (S : ObjSpec GF Obj) (L : ListSpec GF Obj) :
    Persistent (listContractOk' S L) := by
  unfold listContractOk'; infer_instance

/-- **The list half of the contract** (Draft §6): the reflect calls, the decoder's
`DecodeListItem` and the versioner's `UpdateList`, and the list type is not unstructured. -/
def listContractOk (c : StoreCfg GF Obj) (L : ListSpec GF Obj) : IProp GF :=
  iprop(listContractOk' c.S L ∗
    □ (∀ (ctx : GoInterface) (dsl : GoSlice) (d : GoString) (rev : w64) (nf : GoFunc)
        (Φ : val → IProp GF),
      dsl ↦*□ d -∗ newItemOk c.S nf -∗
      ▷ (∀ (x err : GoInterface),
          (match c.S.decode d with
            | some o => ⌜err = GoInterface.nil⌝ ∗ c.S.objAt x o (c.S.fmtRV rev)
            | none => ⌜err ≠ GoInterface.nil⌝ ∗ go_etcd_io.etcd.cache.v3.errStrOk err) -∗
          Φ (PairV #x #err)) -∗
      WP (App (App (App (App (Val #(methods c.di.ty go!"DecodeListItem" c.di.v)) (Val #ctx))
        (Val #dsl)) (Val #rev)) (Val #nf)) {{ Φ }}) ∗
    □ (∀ (pl : Loc) (os : List (Obj × GoString)) (rv rv' : w64) (cont cont' : GoString)
        (rem : Loc) (remV rem0 : Option w64) (Φ : val → IProp GF),
      L.listAtItems pl os rv cont rem0 -∗ remIs rem remV -∗
      ▷ (∀ err, ⌜err = GoInterface.nil⌝ ∗ L.listAtItems pl os rv' cont' remV -∗ Φ #err) -∗
      WP (App (App (App (App (Val #(methods c.vi.ty go!"UpdateList" c.vi.v))
        (Val #(interface.mkOk (go.GoType.PointerType L.listTy) #pl : GoInterface))) (Val #rv'))
        (Val #cont')) (Val #rem)) {{ Φ }}) ∗
    ⌜L.listTy ≠ k8s_io.apimachinery.pkg.apis.«meta».v1.unstructured.UnstructuredList.ty⌝)

instance listContractOk_persistent (c : StoreCfg GF Obj) (L : ListSpec GF Obj) :
    Persistent (listContractOk c L) := by
  unfold listContractOk; infer_instance

/-- **The items of a loop state** (Draft §3.4): in order, each object with its mod revision's
string. -/
def itemsOf (c : StoreCfg GF Obj) (st : k8s_etcd3.ListModel.LState w8 (Obj × Nat)) :
    List (Obj × GoString) :=
  st.items.reverse.map fun x => (x.1, c.S.fmtRV (W64 (x.2 : Int)))

/-- **`appendChunk`'s last key** (Draft §3.4's `lastKeyIs`, a form settled at Prove): `nil` if no
key-value was evaluated, else the key of the `n`-th (the last evaluated). -/
def lastKeyIs (lk : GoSlice) (kvs : List EtcdKv) (n : Nat) : IProp GF :=
  if n = 0 then iprop(⌜lk = slice.nil⌝)
  else iprop(∃ kv : EtcdKv, ⌜kvs[n - 1]? = some kv⌝ ∗ lk ↦*□ kv.key)

instance lastKeyIs_persistent (lk : GoSlice) (kvs : List EtcdKv) (n : Nat) :
    Persistent (lastKeyIs (GF := GF) lk kvs n) := by
  unfold lastKeyIs; split <;> infer_instance

/-- **A list's answer** in the list object `lx` (Draft §2): the items (each object at its mod
revision's string), the list's resource version, the continue token (`encL` of the last match's
key and `"\x00"`, the prefix and the revision, iff more) and the remaining count (iff more and the
predicate is empty). -/
def listIs (c : StoreCfg GF Obj) (L : ListSpec GF Obj) (kp : GoString) (emp : Bool) (lim : w64)
    (R : w64) (a : k8s_etcd3.ListModel.LState w8 (Obj × Nat)) (lx : GoInterface) : IProp GF :=
  L.listAt lx (a.items.reverse.map fun x => (x.1, c.S.fmtRV (W64 (x.2 : Int)))) R
    (if a.more then k8s_etcd3.encL (a.last.getD [] ++ [W8 0]) kp R else [])
    (if a.more ∧ emp then some (W64 (a.total : Int) - lim) else none)

/-- **A list's error** whose outcome tells nothing (Draft §2, the driver's `EOther`): the
client's, or the 410 `interpretListError` makes of an `ErrCompacted` (`NewResourceExpired`: reason
`Expired`, code 410, no details; a form settled at Prove: the Draft's `expiredStatus`). -/
def listErr (c : StoreCfg GF Obj) (err : GoInterface) : IProp GF :=
  iprop(unkErr c err ∨ ∃ st : k8s_io.apimachinery.pkg.apis.«meta».v1.Status,
    apierrors.apiErrAt err (.status st []) ∗
    ⌜st.Reason' = go!"Expired" ∧ st.Code' = W32 410⌝)

instance listErr_persistent (c : StoreCfg GF Obj) (err : GoInterface) :
    Persistent (listErr c err) := by
  unfold listErr; infer_instance

/-- **An error of the kubernetes client** (`unkErr`'s first branch; D1 of the second third): not
`nil`, a leaf grpc's `status` accepts, an `rpctypes.EtcdError` value if of that type. -/
def kClientErr (err : GoInterface) : IProp GF :=
  iprop(⌜err ≠ GoInterface.nil ∧ clientErr err⌝ ∗ go_etcd_io.etcd.cache.v3.statusErrOk err ∗
    go_etcd_io.etcd.cache.v3.errCellOk err)

instance kClientErr_persistent (err : GoInterface) : Persistent (kClientErr (GF := GF) err) := by
  unfold kClientErr; infer_instance

open Iris.ProofMode in
theorem kClientErr_unkErr (c : StoreCfg GF Obj) (err : GoInterface) :
    kClientErr (GF := GF) err ⊢ unkErr c err := by
  unfold kClientErr
  iintro ⟨%h, #Hs, #Hc⟩
  iapply (unkErr_client c err h.1 h.2) $$ Hc Hs

/-- **A range error's future-revision soundness** (B4, decided by etcd-grove-81: the future half
only): an error whose description is `ErrFutureRev`'s (`errDesc`, D29) means the state the read's
update fired at is below the revision `o` asked. What `Client.List`/`Client.GetAt` (hypotheses
until 7e-1/7c-3) give. -/
def rangeErrSound (o : w64) (Q : w64 → KVState → IProp GF) (err : GoInterface) : IProp GF :=
  iprop(□ (⌜go_etcd_io.etcd.cache.v3.errDesc err = go_etcd_io.etcd.cache.v3.futureRevDesc⌝ -∗
      ∃ σ : KVState, □ Q (W64 (σ.rev : Int)) σ ∗ ⌜σ.rev < sint.nat o⌝))

instance rangeErrSound_persistent o Q err : Persistent (rangeErrSound (GF := GF) o Q err) := by
  unfold rangeErrSound; infer_instance

/-- **A failed read's error** (Draft §3.5): the client's error (`kClientErr`, so `unkErr`; D1), and,
by its description (`errDesc`, D29), a future revision only if the state `Q` fired at is below `rev`
(`rangeErrSound`'s future half). -/
def readErrIs (c : StoreCfg GF Obj) (rev : w64) (Q : w64 → KVState → IProp GF)
    (err : GoInterface) : IProp GF :=
  iprop(kClientErr err ∗
    □ (⌜go_etcd_io.etcd.cache.v3.errDesc err = go_etcd_io.etcd.cache.v3.futureRevDesc⌝ -∗
      ∃ σ : KVState, □ Q (W64 (σ.rev : Int)) σ ∗ ⌜σ.rev < sint.nat rev⌝))

instance readErrIs_persistent (c : StoreCfg GF Obj) rev Q err :
    Persistent (readErrIs c rev Q err) := by
  unfold readErrIs; infer_instance

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
