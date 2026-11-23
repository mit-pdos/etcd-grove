/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/cmap/Specs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The specs of the concurrent-map model (`harness/rpcmodel/cmap`, v1.0.0's code) that SwiftPaxos's
`swift` package calls: `New`, `Set`, `Upsert`, `Get`, `Has`, `Remove`, `IterCb`, `Count`,
`IsEmpty` (internal, the replica group's). Predicates and laws: `Defs.lean`, `Ghost.lean`;
pure vocabulary (`fnv32F`, `shardOf`, `shardPart`, `iterTrace`): `Pure.lean`.

The strong specs (`…V`) are over the client's view `cmapView γ M` of the whole map (TaDA):
`Set`, `Upsert`, `Remove` commit the client's atomic update on it while the shard's write lock
is held (`M ↦ <[key := v]> M`, `M ↦ GMap.delete key M`); `Get` and `Has` answer from it (an
atomic observation under the shard's read lock); `IterCb` observes it at each shard's read lock
and calls `fn` on exactly that shard's part of it (`shardPart`), each entry once. The map's
entries also keep `□ R k v` (HOCAP, for readers that need only those facts). Writers need the
persistent `isCMapV m γ R`; readers a reader bundle `readerV m γ R` (one `RWMutex` reader token
per shard, given back): `New` makes `cmapReaders` (`2^30 - 1`) of them. `Count` and `IsEmpty`
are not linearizable (the shards are read one at a time) and give some answer.

The old specs (no view) are kept, over `isCMap m R` and `reader m R`, which now keep the view in
an invariant nobody else uses (`cmapOld`); they are corollaries of the strong ones.
-/
module

public import Dsverify.Proof.github_com.orcaman.concurrent_map.Ghost
public import Perennial.ProgramLogic.AtomicFupd
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Base

@[expose] public section

noncomputable section

namespace Perennial.github_com.orcaman.concurrent_map

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [concurrent_map.Assumptions] [sync.Assumptions]
variable [github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF]

/-- `fnv32(key)`: the hash `fnv32F key`. -/
abbrev fnv32.spec : Prop :=
  ∀ (key : GoString),
  {{ (True : IProp GF) }}
    (App (Val (@! concurrent_map.fnv32)) (Val #key))
  {{ RET #(fnv32F key); True }}

/-- `m.GetShard(key)`: shard `shardOf n key` of `m`'s `n` shards. -/
abbrev ConcurrentMap.GetShardV.spec : Prop :=
  ∀ (m : GoSlice) (n : w64) (shs : List Loc) (key : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.orcaman.concurrent_map ∗
      typedPointsto (globalAddr concurrent_map.SHARD_COUNT) n DFrac.discard ∗ m ↦*□ shs ∗
      ⌜0 < sint.Z n ∧ shs.length = sint.nat n⌝ }}
    (App (Val #(methods ConcurrentMap.ty go!"GetShard" #m)) (Val #key))
  {{ (sh : Loc), RET #sh; ⌜shs[shardOf (sint.nat n) key]? = some sh⌝ }}

/-- `m.GetShard(key)`: one of `m`'s shards. -/
abbrev ConcurrentMap.GetShard.spec : Prop :=
  ∀ (m : GoSlice) (R : GoString → GoInterface → IProp GF) (key : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.orcaman.concurrent_map ∗ isCMap m R }}
    (App (Val #(methods ConcurrentMap.ty go!"GetShard" #m)) (Val #key))
  {{ (sh : Loc), RET #sh; isShard sh R ∗
      ∃ (shs : List Loc) (i : Nat), m ↦*□ shs ∗ ⌜shs[i]? = some sh⌝ }}

/-- `New()`: an empty map, and `cmapReaders` reader token bundles. -/
abbrev New.spec : Prop :=
  ∀ (n : w64) (R : GoString → GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.orcaman.concurrent_map ∗
      typedPointsto (globalAddr concurrent_map.SHARD_COUNT) n DFrac.discard ∗ ⌜0 < sint.Z n⌝ }}
    (App (Val (@! concurrent_map.New)) (Val #()))
  {{ (m : GoSlice), RET #m; isCMap m R ∗
      [∗list] _x ∈ List.replicate cmapReaders (), reader m R }}

/-- `m.Set(key, value)`. -/
abbrev ConcurrentMap.Set.spec : Prop :=
  ∀ (m : GoSlice) (R : GoString → GoInterface → IProp GF) (key : GoString) (v : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.orcaman.concurrent_map ∗ isCMap m R ∗
      □ R key v }}
    (App (App (Val #(methods ConcurrentMap.ty go!"Set" #m)) (Val #key)) (Val #v))
  {{ RET #(); True }}

/-- `m.Upsert(key, value, cb)`: `cb(exists, old, value)` runs under the shard's lock, with
`R key old` when an entry exists; its result is stored and returned. -/
abbrev ConcurrentMap.Upsert.spec : Prop :=
  ∀ (m : GoSlice) (R : GoString → GoInterface → IProp GF) (key : GoString) (v : GoInterface)
    (cb : GoFunc) (Q : GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.orcaman.concurrent_map ∗ isCMap m R ∗
      (∀ (ex : Bool) (old : GoInterface) (Φ : val → IProp GF),
        (if ex then R key old else ⌜old = interface.nil⌝) -∗
        ▷ (∀ res : GoInterface, □ R key res -∗ Q res -∗ Φ #res) -∗
        WP (App (App (App (Val #cb) (Val #ex)) (Val #old)) (Val #v)) {{ Φ }}) }}
    (App (App (App (Val #(methods ConcurrentMap.ty go!"Upsert" #m)) (Val #key)) (Val #v))
      (Val #cb))
  {{ (res : GoInterface), RET #res; Q res }}

/-- `m.Get(key)`. -/
abbrev ConcurrentMap.Get.spec : Prop :=
  ∀ (m : GoSlice) (R : GoString → GoInterface → IProp GF) (key : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.orcaman.concurrent_map ∗ isCMap m R ∗
      reader m R }}
    (App (Val #(methods ConcurrentMap.ty go!"Get" #m)) (Val #key))
  {{ (v : GoInterface) (ok : Bool), RET (PairV #v #ok); reader m R ∗
      (if ok then R key v else ⌜v = interface.nil⌝) }}

/-- `m.Has(key)`. -/
abbrev ConcurrentMap.Has.spec : Prop :=
  ∀ (m : GoSlice) (R : GoString → GoInterface → IProp GF) (key : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.orcaman.concurrent_map ∗ isCMap m R ∗
      reader m R }}
    (App (Val #(methods ConcurrentMap.ty go!"Has" #m)) (Val #key))
  {{ (ok : Bool), RET #ok; reader m R ∗ (if ok then ∃ v, R key v else True) }}

/-- `m.Remove(key)`. -/
abbrev ConcurrentMap.Remove.spec : Prop :=
  ∀ (m : GoSlice) (R : GoString → GoInterface → IProp GF) (key : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.orcaman.concurrent_map ∗ isCMap m R }}
    (App (Val #(methods ConcurrentMap.ty go!"Remove" #m)) (Val #key))
  {{ RET #(); True }}

/-- `m.Count()`: some count. -/
abbrev ConcurrentMap.Count.spec : Prop :=
  ∀ (m : GoSlice) (R : GoString → GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.orcaman.concurrent_map ∗ isCMap m R ∗
      reader m R }}
    (App (Val #(methods ConcurrentMap.ty go!"Count" #m)) (Val #()))
  {{ (c : w64), RET #c; reader m R }}

/-- `m.IsEmpty()`: some answer (not linearizable: the shards are read one at a time). -/
abbrev ConcurrentMap.IsEmpty.spec : Prop :=
  ∀ (m : GoSlice) (R : GoString → GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.orcaman.concurrent_map ∗ isCMap m R ∗
      reader m R }}
    (App (Val #(methods ConcurrentMap.ty go!"IsEmpty" #m)) (Val #()))
  {{ (b : Bool), RET #b; reader m R }}

/-- `m.IterCb(fn)`: `fn` on some entries (each shard's, under its read lock), keeping `I`. -/
abbrev ConcurrentMap.IterCb.spec : Prop :=
  ∀ (m : GoSlice) (R : GoString → GoInterface → IProp GF) (fn : GoFunc) (I : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.orcaman.concurrent_map ∗ isCMap m R ∗
      reader m R ∗ iterOk fn R I ∗ I }}
    (App (Val #(methods ConcurrentMap.ty go!"IterCb" #m)) (Val #fn))
  {{ RET #(); reader m R ∗ I }}

/-! ### The strong specs -/

/-- `New()`: an empty map with its view (fresh `γ`), and `cmapReaders` reader bundles. -/
abbrev NewV.spec : Prop :=
  ∀ (n : w64) (R : GoString → GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.orcaman.concurrent_map ∗
      typedPointsto (globalAddr concurrent_map.SHARD_COUNT) n DFrac.discard ∗ ⌜0 < sint.Z n⌝ }}
    (App (Val (@! concurrent_map.New)) (Val #()))
  {{ (m : GoSlice), RET #m; ∃ γ : GName, isCMapV m γ R ∗ cmapView γ ∅ ∗
      [∗list] _x ∈ List.replicate cmapReaders (), readerV m γ R }}

/-- `m.Set(key, value)`: the view `M` becomes `<[key := v]> M` (under the shard's write lock). -/
abbrev ConcurrentMap.SetV.spec : Prop :=
  ∀ (m : GoSlice) (γ : GName) (R : GoString → GoInterface → IProp GF) (key : GoString)
    (v : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.orcaman.concurrent_map ∗ isCMapV m γ R ∗
      □ R key v }}
  <<{ ∀∀ (M : GMap GoString GoInterface), cmapView γ M }>>
    (App (App (Val #(methods ConcurrentMap.ty go!"Set" #m)) (Val #key)) (Val #v)) @@ (↑cmapN : CoPset)
  <<{ cmapView γ (<[key := v]> M) }>>
  {{ RET #(); True }}

/-- `m.Remove(key)`: the view `M` becomes `GMap.delete key M`. -/
abbrev ConcurrentMap.RemoveV.spec : Prop :=
  ∀ (m : GoSlice) (γ : GName) (R : GoString → GoInterface → IProp GF) (key : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.orcaman.concurrent_map ∗ isCMapV m γ R }}
  <<{ ∀∀ (M : GMap GoString GoInterface), cmapView γ M }>>
    (App (Val #(methods ConcurrentMap.ty go!"Remove" #m)) (Val #key)) @@ (↑cmapN : CoPset)
  <<{ cmapView γ (GMap.delete key M) }>>
  {{ RET #(); True }}

/-- `m.Upsert(key, value, cb)`: `cb(ex, old, value)` runs under the shard's write lock, with
`R key old` when an entry exists, and gives the client `Q ex old res` for its result `res`; then
(the lock still held) the client's atomic update commits: the view `M`, in which `key` is bound
as `cb` saw it, becomes `<[key := res]> M`; `res` is stored and returned. -/
abbrev ConcurrentMap.UpsertV.spec : Prop :=
  ∀ (m : GoSlice) (γ : GName) (R : GoString → GoInterface → IProp GF) (key : GoString)
    (v : GoInterface) (cb : GoFunc) (Q : Bool → GoInterface → GoInterface → IProp GF),
  ⊢ ∀ Φ : val → IProp GF,
    isPkgInit (PROP := IProp GF) pkg_id.github_com.orcaman.concurrent_map ∗ isCMapV m γ R ∗
      (∀ (ex : Bool) (old : GoInterface) (Ψ : val → IProp GF),
        (if ex then R key old else ⌜old = interface.nil⌝) -∗
        ▷ (∀ res : GoInterface, □ R key res -∗ Q ex old res -∗ Ψ #res) -∗
        WP (App (App (App (Val #cb) (Val #ex)) (Val #old)) (Val #v)) {{ Ψ }}) -∗
    (∀ (ex : Bool) (old res : GoInterface), Q ex old res -∗
      ▷ |={⊤ \ ↑cmapN, ∅}=> ∃ M : GMap GoString GoInterface, cmapView γ M ∗
        (⌜M !! key = if ex then some old else none⌝ -∗ cmapView γ (<[key := res]> M) -∗
          |={∅, ⊤ \ ↑cmapN}=> Φ #res)) -∗
    WP (App (App (App (Val #(methods ConcurrentMap.ty go!"Upsert" #m)) (Val #key)) (Val #v))
      (Val #cb)) {{ Φ }}

/-- `m.Get(key)`: the entry of `key` in the view (an atomic observation). -/
abbrev ConcurrentMap.GetV.spec : Prop :=
  ∀ (m : GoSlice) (γ : GName) (R : GoString → GoInterface → IProp GF) (key : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.orcaman.concurrent_map ∗ readerV m γ R }}
  <<{ ∀∀ (M : GMap GoString GoInterface), cmapView γ M }>>
    (App (Val #(methods ConcurrentMap.ty go!"Get" #m)) (Val #key)) @@ (↑cmapN : CoPset)
  <<{ cmapView γ M }>>
  {{ (v : GoInterface) (ok : Bool), RET (PairV #v #ok); readerV m γ R ∗
      ⌜v = (M !! key).getD interface.nil ∧ ok = (M !! key).isSome⌝ ∗
      (if ok then R key v else True) }}

/-- `m.Has(key)`: whether `key` is in the view (an atomic observation). -/
abbrev ConcurrentMap.HasV.spec : Prop :=
  ∀ (m : GoSlice) (γ : GName) (R : GoString → GoInterface → IProp GF) (key : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.orcaman.concurrent_map ∗ readerV m γ R }}
  <<{ ∀∀ (M : GMap GoString GoInterface), cmapView γ M }>>
    (App (Val #(methods ConcurrentMap.ty go!"Has" #m)) (Val #key)) @@ (↑cmapN : CoPset)
  <<{ cmapView γ M }>>
  {{ (ok : Bool), RET #ok; readerV m γ R ∗ ⌜ok = (M !! key).isSome⌝ ∗
      (∀ v, ⌜M !! key = some v⌝ -∗ R key v) }}

/-- `m.Count()`: some count (not linearizable). -/
abbrev ConcurrentMap.CountV.spec : Prop :=
  ∀ (m : GoSlice) (γ : GName) (R : GoString → GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.orcaman.concurrent_map ∗ readerV m γ R }}
    (App (Val #(methods ConcurrentMap.ty go!"Count" #m)) (Val #()))
  {{ (c : w64), RET #c; readerV m γ R }}

/-- `m.IsEmpty()`: some answer (not linearizable). -/
abbrev ConcurrentMap.IsEmptyV.spec : Prop :=
  ∀ (m : GoSlice) (γ : GName) (R : GoString → GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.orcaman.concurrent_map ∗ readerV m γ R }}
    (App (Val #(methods ConcurrentMap.ty go!"IsEmpty" #m)) (Val #()))
  {{ (b : Bool), RET #b; readerV m γ R }}

/-- `m.IterCb(fn)`, shard by shard: at each shard's read lock the client observes its view `M`
(`I obs vis` becomes `I (obs ++ [M]) vis`, `obs` the views observed so far), then `fn` is called
on each entry `(k, v)` of `M`'s part in the shard, once each (`I obs vis` becomes
`I obs (vis ++ [(k, v)])`). At the end `iterTrace n obs vis`: one observation per shard, and the
entries visited are, shard by shard, a permutation of the observed view's part in it. -/
abbrev ConcurrentMap.IterCbV.spec : Prop :=
  ∀ (m : GoSlice) (γ : GName) (R : GoString → GoInterface → IProp GF) (fn : GoFunc)
    (I : List (GMap GoString GoInterface) → List (GoString × GoInterface) → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.orcaman.concurrent_map ∗ readerV m γ R ∗
      I [] [] ∗
      □ (∀ (obs : List (GMap GoString GoInterface)) (vis : List (GoString × GoInterface)),
          I obs vis -∗
          |={⊤ \ ↑cmapN, ∅}=> ∃ M : GMap GoString GoInterface, cmapView γ M ∗
            (cmapView γ M ={∅, ⊤ \ ↑cmapN}=∗ I (obs ++ [M]) vis)) ∗
      □ (∀ (obs : List (GMap GoString GoInterface)) (vis : List (GoString × GoInterface))
          (k : GoString) (v : GoInterface) (Φ : val → IProp GF),
          ⌜∃ M, obs.getLast? = some M ∧ M !! k = some v⌝ -∗ R k v -∗ I obs vis -∗
          ▷ (I obs (vis ++ [(k, v)]) -∗ Φ #()) -∗
          WP (App (App (Val #fn) (Val #k)) (Val #v)) {{ Φ }}) }}
    (App (Val #(methods ConcurrentMap.ty go!"IterCb" #m)) (Val #fn))
  {{ RET #(); readerV m γ R ∗
      ∃ (n : Nat) (obs : List (GMap GoString GoInterface)) (vis : List (GoString × GoInterface)),
        cmapShards n ∗ I obs vis ∗ ⌜iterTrace n obs vis⌝ }}

end spec

end Perennial.github_com.orcaman.concurrent_map
