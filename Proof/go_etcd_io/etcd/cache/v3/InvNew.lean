/-
etcd's cache `New`/`newCache` (`cache/cache.go`): the vocabulary of
`Spec/go_etcd_io/etcd/cache/v3/{New,newCache}.lean`. Lean-first (no Rocq counterpart).

**The client.** `isEtcdClient client pfx` is what `New`'s caller assumes of its
`*clientv3.Client` (the trust boundary about the client, a definition like `isEtcdKV`): its
embedded `KV` and `Watcher` fields hold, for good, a `KV` that answers `Get`s with etcd's state
(`isEtcdKVE`: `isEtcdKV`, its errors' `Error()` returning some string) and a `Watcher` that streams etcd's watch responses (`isEtcdWatcher`) and accepts
`RequestProgress` (`isEtcdProgressNotifier`), for the prefix `pfx`; the same `KV` runs
transactions (`isEtcdTxnKV`) and the `Lease` field grants, keeps alive and revokes leases
(`isEtcdLeaseClient`): `InvEtcdTxn.lean`, unused by the cache. etcd's **linearizability**
is part of `isEtcdKV`'s triple, stated against what the caller knows etcd has reached
(`etcdReached`, `InvEtcd.lean`), a property of the client alone: nothing here is about caches.

**What `New` hands out** (`cacheHandles`): the readers of the store (`cacheReader`, for `Get` and
`WaitForRevision`), the watch slots (`cacheWatchSlot`: a demux token and a wait-group slot, for
`Watch`), the handles on the demux's resync notifier (`demuxResyncHandle`, for
`WaitForNextResync`) with its initial lower bound, and the whole "open" token (`cacheOpen`, for
`Watch` and `Close`).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvCache
public import Proof.go_etcd_io.etcd.cache.v3.InvConfig
public import Proof.go_etcd_io.etcd.cache.v3.InvEtcdTxn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- `&client.KV` (the embedded `KV` of a `*clientv3.Client`). -/
abbrev clientKVAddr (cl : Loc) : Loc := structFieldRef go_etcd_io.etcd.client.v3.Client go!"KV" cl
/-- `&client.Watcher` (the embedded `Watcher` of a `*clientv3.Client`). -/
abbrev clientWatcherAddr (cl : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.client.v3.Client go!"Watcher" cl

end addrs

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `TypeRepr` of `clientv3.Client` (named and underlying types), straight from its
`TypeAssumptions`, as `InvStore.lean` does for the protobuf messages: without these, the
`StructFieldRef` step of `client.KV`/`client.Watcher` finds `TypeRepr` through `Client`'s
`IntoValTyped` instance, built from the `sorry` instances ("axiomatized type") of its
names-only fields (`cfg`, `creds`, `authTokenBundle`, `lg`, `Maintenance`), putting them in the
trust base for nothing. -/
instance (priority := high) client_typeRepr :
    TypeRepr go_etcd_io.etcd.client.v3.Client.ty go_etcd_io.etcd.client.v3.Client :=
  go.type_repr_underlying (u := go_etcd_io.etcd.client.v3.Client.underlying)

instance (priority := high) client_typeRepr_u :
    TypeRepr go_etcd_io.etcd.client.v3.Client.underlying go_etcd_io.etcd.client.v3.Client :=
  go.type_repr_underlying (u := go_etcd_io.etcd.client.v3.Client.underlying)

/-- **The client** `client` (a `*clientv3.Client`) talks to etcd for the prefix `pfx` (persistent;
see the module docstring): its `KV` and `Watcher` fields and their triples; the `KV`'s
transactions (`isEtcdTxnKV`) and the `Lease` field (`isEtcdLeaseClient`, `InvEtcdTxn.lean`),
which the cache does not use. -/
def isEtcdClient (client : Loc) (pfx : GoString) : IProp GF :=
  iprop(∃ (kv w : GoInterfaceOk),
    clientKVAddr client ↦□ GoInterface.ok kv ∗ clientWatcherAddr client ↦□ GoInterface.ok w ∗
    isEtcdKVE kv pfx ∗ isEtcdWatcher w pfx ∗ isEtcdProgressNotifier w ∗
    isEtcdTxnKV kv pfx ∗ isEtcdLeaseClient client)

instance isEtcdClient_persistent (client : Loc) (pfx : GoString) :
    Persistent (isEtcdClient (GF := GF) client pfx) := by
  unfold isEtcdClient; infer_instance

/-- The number of the `RWMutex` tokens of the store, the demux and the notifier
(`sync.rwmutex.actualMaxReaders`, `2^30 - 1`). -/
abbrev maxReaders : Nat := Int.toNat sync.rwmutex.actualMaxReaders

/-- What `New` hands out (see the module docstring): `maxReaders - 1` store readers,
`maxReaders - 2` watch slots, `maxReaders - 1` resync handles with the notifier's lower bound
`0`, and the whole "open" token. -/
def cacheHandles (cf : CacheFields) (γd : DemuxNames) (cap : Nat) (γn : NotifierNames) :
    IProp GF :=
  iprop(([∗list] _x ∈ List.replicate (maxReaders - 1) (), cacheReader cf) ∗
    ([∗list] _x ∈ List.replicate (maxReaders - 2) (), cacheWatchSlot cf γd cap) ∗
    ([∗list] _x ∈ List.replicate (maxReaders - 1) (), demuxResyncHandle cf.demux γn) ∗
    notifierLb γn 0 ∗ cacheOpen cf 1)

/-- What `newCache`/`New` return for the prefix `pfx` and the configuration `cfg`: if `cfg` is
rejected (`HistoryWindowSize ≤ 0` or `BTreeDegree < 2`), `nil` and a non-nil error; otherwise a
`*Cache` `c` and `nil`, with `c` a cache (`isCacheFields`, every field) for the prefix and the
configuration, a history of capacity `HistoryWindowSize`, and its handles (`cacheHandles`). -/
def newCacheResult (pfx : GoString) (cfg : Config) (c : Loc) (err : GoInterface) : IProp GF :=
  if CfgValid cfg then
    iprop(⌜err = GoInterface.nil⌝ ∗
      ∃ (cf : CacheFields) (γr : ReadyNames) (γd : DemuxNames) (γn : NotifierNames),
        isCacheFields c cf γr γd (sint.nat cfg.HistoryWindowSize') ∗
        ⌜cf.pfx = pfx ∧ cf.cfg = cfg ∧ cf.scap = sint.nat cfg.HistoryWindowSize'⌝ ∗
        cacheHandles cf γd (sint.nat cfg.HistoryWindowSize') γn)
  else iprop(⌜c = null ∧ err ≠ GoInterface.nil⌝)

/-- The cache's wait group, as `NewDemux` uses it for the resync loop: a slot and an owed
capacity with the whole "open" token (no `Close` waits), an owed running token (the resync loop
keeps its own thread token), the "open" token back. -/
theorem cache_wgSlotProtocol (c : Loc) (cf : CacheFields)
    (Hbound : threadBound GF + cacheWgOwedMax ≤ 2 ^ 31) :
    isPkgInit (PROP := IProp GF) pkg_id.sync ∗ sync.isWaitGroup (cacheWgAddr c) cf.γwg cacheWgWGN ∗
      inv cacheWgN (cacheWgInv cf) ⊢
    wgSlotProtocol (cacheWgAddr c) iprop(cacheWgSlot cf ∗ cacheWgOwedCap cf ∗ cacheOpen cf 1)
      (cacheWgRunningOwed cf) (cacheOpen cf 1) := by
  iintro ⟨#Hsync, #Hwg, #Hinv⟩
  unfold wgSlotProtocol
  isplitl
  · imodintro
    iintro %Φ
    imodintro
    iintro ⟨Hslot, Hcap, Hopen⟩ HΦ
    iapply wp_cacheWg_AddOwed c cf 1 Hbound $$ [$Hsync $Hwg $Hinv $Hslot $Hcap $Hopen] HΦ
  · imodintro
    iintro %Φ
    imodintro
    iintro Hrun HΦ
    iapply wp_cacheWg_DoneOwed c cf $$ [$Hsync $Hwg $Hinv $Hrun]
    inext
    iintro -
    iapply HΦ
    itrivial

/-- `c.waitGroup.Add(2)` (`newCache`'s, for the watch loop and the progress requestor, two
goroutines that keep their own thread tokens), spending two goroutine slots and two owed
capacities for two owed running tokens, with a fraction of the "open" token. -/
theorem wp_cacheWg_Add2 (c : Loc) (cf : CacheFields) (q : Qp)
    (Hbound : threadBound GF + cacheWgOwedMax ≤ 2 ^ 31) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ sync.isWaitGroup (cacheWgAddr c) cf.γwg cacheWgWGN ∗
        inv cacheWgN (cacheWgInv cf) ∗ ownToks cf.γwb 2 ∗ ownToks cf.γwc 2 ∗ cacheOpen cf q }}
      (App (Val (cacheWgAddr c @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Add")) (Val #(W64 2)))
    {{ RET #(); ownToks cf.γwo 2 ∗ cacheOpen cf q }} := by
  iintro %Φ ⟨#Hsync, #Hwg, #Hinv, Hslot, Hocap, Hopen⟩ HΦ
  iapply sync.WaitGroup.wp_Add (cacheWgAddr c) (W64 2) cf.γwg cacheWgWGN $$ [] [Hslot Hocap Hopen HΦ]
  · iframe #
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro cacheWg_mask
  iintro Hmask
  inext
  iunfold cacheWgInv at Hi
  icases Hi with ⟨%ctr, %wn, %k, %d, Hwgo, Hwt, Hrun, Hk, Hoauth, Hcap, Hcauth, ⟨%j, Hbud⟩, Hbauth,
    %Hctr, %Hkd, Hwn⟩
  icases Hwn with (%Hw0 | ⟨-, Hop1⟩)
  rotate_left
  · iexfalso
    iapply cacheOpen_excl cf q $$ [$Hopen $Hop1]
  subst Hw0
  ihave Hbud' := ownToks_add_2 2 j cf.γwb $$ [Hbud Hslot]
  · iframe
  ihave Hcap' := ownToks_add_2 2 d cf.γwc $$ [Hcap Hocap]
  · iframe
  icases persistent_entails_left (threadToks_lt (GF := GF) k) $$ Hk with ⟨Hk, %Hlt⟩
  icombine Hcauth Hcap' gives %Hd
  have hb := cacheWg_ctr_bound_owed (n := 2) Hbound Hlt Hd
  have h1 : sint.Z (W32 (sint.Z (W64 2))) = 2 := by decide
  have hc : ((sint.nat ctr : Nat) : Int) = sint.Z ctr := Int.toNat_of_nonneg Hctr
  have hle : sint.Z ctr + 2 ≤ 2 ^ 31 - 1 := by omega
  have hn : sint.nat (ctr + W32 (sint.Z (W64 2))) = sint.nat ctr + 2 := by
    rw [show W32 (sint.Z (W64 2)) = W32 2 from rfl]; word
  iexists ctr
  iframe Hwgo
  isplitr
  · ipureintro; rw [h1]; omega
  iright
  iframe Hwt
  iintro Hwt Hwgo
  imod Hmask with -
  imod ownTokAuth_add 2 cf.γwo d $$ Hoauth with ⟨Hoauth, Hotok⟩
  imod Hclose $$ [Hwgo Hwt Hrun Hk Hoauth Hcap' Hcauth Hbud' Hbauth] with -
  · inext
    unfold cacheWgInv
    iexists ctr + W32 (sint.Z (W64 2)), 0, k, d + 2
    rw [hn]
    iframe
    isplitr
    · ipureintro
      have : sint.Z (ctr + W32 (sint.Z (W64 2))) = sint.Z ctr + 2 := by
        rw [show W32 (sint.Z (W64 2)) = W32 2 from rfl]; word
      omega
    isplitr
    · ipureintro; omega
    ileft; ipureintro; rfl
  imodintro
  iapply HΦ
  iframe

/-! ### Lists of replicated resources -/

theorem ownToks_replicate (γ : GName) :
    ∀ n : Nat, ownToks (GF := GF) γ n ⊢ [∗list] _x ∈ List.replicate n (), ownToks γ 1
  | 0 => by
    iintro -
    simp only [List.replicate_zero]
    iapply BigSepL.bigSepL_nil.2
    iempintro
  | n + 1 => by
    rw [List.replicate_succ]
    iintro H
    icases ownToks_add_1 1 n γ $$ H with ⟨Hn, H1⟩
    iapply BigSepL.bigSepL_cons.2
    iframe H1
    iapply ownToks_replicate γ n $$ Hn

theorem bigSepL_replicate_sep (P Q : IProp GF) (n : Nat) :
    ([∗list] _x ∈ List.replicate n (), P) ∗ ([∗list] _x ∈ List.replicate n (), Q) ⊢
      [∗list] _x ∈ List.replicate n (), iprop(P ∗ Q) :=
  BigSepL.bigSepL_sep_eqv.2

theorem bigSepL_replicate_pop' (P : IProp GF) (n m : Nat) (h : n = m + 1) :
    ([∗list] _x ∈ List.replicate n (), P) ⊢ P ∗ [∗list] _x ∈ List.replicate m (), P := by
  subst h
  rw [List.replicate_succ]
  exact BigSepL.bigSepL_cons.1

end defs

end EtcdGrove
end Perennial
