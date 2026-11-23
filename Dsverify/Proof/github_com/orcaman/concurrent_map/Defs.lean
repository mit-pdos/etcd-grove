/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/cmap/Defs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The concurrent map's predicates (internal, the replica group's).

The strong view (TaDA): `cmapView γ M` is the whole map's contents `M`, exclusive, owned by the
client (half of a ghost variable `γ` whose other half the library's invariant holds; the ghost
variable also holds the shard count and shards, `(n, shs)`, which the client never sees). Its
library-side predicates:

* `shardP mp R γi q`: a shard's `RWMutex` resource at fraction `q`: the shard's Go map at `q`,
  the same fraction of half of the shard's ghost variable `γi` (holding the same map), `□ R` of
  each entry;
* `cmapInv γ n shs`: the library invariant (namespace `cmapN`): `∃ M`, the other half of `γ`
  at `M` and, for each shard `i`, the other half of `γi` at `shardPart n i M`. A writer holding
  shard `i`'s write lock has all of `γi` and updates `γ` with it (shards hold disjoint keys, by
  `shardOf`); a reader holding the read lock sees, through the invariant, that its shard is
  `M`'s part;
* `cmapCore m γ R n shs` (persistent): `m` is a slice of `n` shards `shs` (each with its ghost
  name), `SHARD_COUNT ↦□ n`, the invariant, each shard's `items` field and guard;
* `isCMapV m γ R := ∃ n shs, cmapCore m γ R n shs` (persistent; the writers' handle);
* `readerV m γ R`: the core and one reader token per shard (the readers' bundle);
* `cmapShards n`: `SHARD_COUNT ↦□ w` with `n = sint.nat w > 0` (persistent, agreeing).

The old (HOCAP) names, kept for the old specs: `isCMap m R := ∃ γ, isCMapV m γ R ∗ cmapOld γ`,
`reader m R := ∃ γ, readerV m γ R ∗ cmapOld γ`, where `cmapOld γ` keeps the view in an
invariant (`cmapOldN`) nobody else uses.
-/
module

public import Perennial.Proof.sync
public import Perennial.Golang.Theory
public import Dsverify.GeneratedProof.github_com.orcaman.concurrent_map
public import Dsverify.Proof.github_com.orcaman.concurrent_map.Pure

@[expose] public section

noncomputable section

namespace Perennial.github_com.orcaman.concurrent_map

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section defs
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [concurrent_map.Assumptions] [sync.Assumptions]

/-- The library's invariant namespace (the client's atomic updates run with it open). -/
def cmapN : Namespace := nroot.@"cmap"
/-- The namespace of the old specs' view invariant (`cmapOld`). -/
def cmapOldN : Namespace := nroot.@"cmapOld"

/-- The client's view of the whole map: its contents `M` (exclusive). -/
def cmapView (γ : GName) (M : GMap GoString GoInterface) : IProp GF :=
  iprop(∃ c : Nat × List (Loc × GName), ghostVar γ (1 : Qp).half (M, c))

instance cmapView_timeless (γ : GName) (M : GMap GoString GoInterface) :
    Timeless (cmapView (GF := GF) γ M) := by unfold cmapView; infer_instance

/-- The library invariant: the other half of the view, and of each shard's ghost variable at
the view's part in it. The view's ghost variable also records the map's shard count and shards
`(n, shs)` (the core's identity: two invariants of the same `γ` agree on them through the client's
view; `cmapLocked_pin_false`, Proof/cmap/RemoveL.lean). -/
def cmapInv (γ : GName) (n : Nat) (shs : List (Loc × GName)) : IProp GF :=
  iprop(∃ M : GMap GoString GoInterface, ghostVar γ (1 : Qp).half (M, (n, shs)) ∗
    [∗list] i ↦ p ∈ shs, ghostVar p.2 (1 : Qp).half (shardPart n i M))

/-- A shard's lock resource at fraction `q`. -/
def shardP (mp : Loc) (R : GoString → GoInterface → IProp GF) (γi : GName) (q : Qp) :
    IProp GF :=
  iprop(∃ M : GMap GoString GoInterface, ownMap mp (DFrac.own q) M ∗ ghostVar γi q.half M ∗
    □ (∀ k v, ⌜M !! k = some v⌝ → R k v))

/-- Shard `sh` with ghost name `γi` (persistent): its read-only `items` map and its lock's
guard. -/
def isShardV (sh : Loc) (R : GoString → GoInterface → IProp GF) (γi : GName) : IProp GF :=
  iprop(∃ mp : Loc, sh.[ConcurrentMapShared, go!"items"] ↦□ mp ∗
    sync.isRWMutexGuard (sh.[ConcurrentMapShared, go!"RWMutex"]) (shardP mp R γi))

/-- A reader token of shard `sh`. -/
def shardTok (sh : Loc) (R : GoString → GoInterface → IProp GF) (γi : GName) : IProp GF :=
  iprop(∃ mp : Loc, sh.[ConcurrentMapShared, go!"items"] ↦□ mp ∗
    sync.ownRWMutex (sh.[ConcurrentMapShared, go!"RWMutex"]) (shardP mp R γi))

/-- The map `m` of `n` shards `shs` (with their ghost names), persistent. -/
def cmapCore (m : GoSlice) (γ : GName) (R : GoString → GoInterface → IProp GF) (n : w64)
    (shs : List (Loc × GName)) : IProp GF :=
  iprop(typedPointsto (globalAddr concurrent_map.SHARD_COUNT) n DFrac.discard ∗
    m ↦*□ (shs.map Prod.fst) ∗ ⌜0 < sint.Z n ∧ shs.length = sint.nat n⌝ ∗
    inv cmapN (cmapInv γ (sint.nat n) shs) ∗
    [∗list] p ∈ shs, isShardV p.1 R p.2)

/-- The concurrent map `m` with view `γ` (persistent). -/
def isCMapV (m : GoSlice) (γ : GName) (R : GoString → GoInterface → IProp GF) : IProp GF :=
  iprop(∃ (n : w64) (shs : List (Loc × GName)), cmapCore m γ R n shs)

/-- A reader token bundle of `m`: one reader token per shard. -/
def readerV (m : GoSlice) (γ : GName) (R : GoString → GoInterface → IProp GF) : IProp GF :=
  iprop(∃ (n : w64) (shs : List (Loc × GName)), cmapCore m γ R n shs ∗
    [∗list] p ∈ shs, shardTok p.1 R p.2)

/-- The number of shards of every map (`SHARD_COUNT`, read-only), persistent. -/
def cmapShards (n : Nat) : IProp GF :=
  iprop(∃ w : w64, typedPointsto (globalAddr concurrent_map.SHARD_COUNT) w DFrac.discard ∗
    ⌜sint.nat w = n ∧ 0 < n⌝)

/-- The view kept in an invariant nobody else uses (the old specs'). -/
def cmapOld (γ : GName) : IProp GF :=
  inv cmapOldN (∃ M : GMap GoString GoInterface, cmapView γ M)

/-- Shard `sh` (persistent; old name). -/
def isShard (sh : Loc) (R : GoString → GoInterface → IProp GF) : IProp GF :=
  iprop(∃ γi : GName, isShardV sh R γi)

/-- The concurrent map `m` (persistent; the old specs' handle). -/
def isCMap (m : GoSlice) (R : GoString → GoInterface → IProp GF) : IProp GF :=
  iprop(∃ γ : GName, isCMapV m γ R ∗ cmapOld γ)

/-- A reader token bundle of `m` (the old specs'). -/
def reader (m : GoSlice) (R : GoString → GoInterface → IProp GF) : IProp GF :=
  iprop(∃ γ : GName, readerV m γ R ∗ cmapOld γ)

instance isShardV_persistent (sh : Loc) (R : GoString → GoInterface → IProp GF) (γi : GName) :
    Persistent (isShardV sh R γi) := by unfold isShardV; infer_instance
instance cmapCore_persistent (m : GoSlice) (γ : GName) (R : GoString → GoInterface → IProp GF)
    (n : w64) (shs : List (Loc × GName)) : Persistent (cmapCore m γ R n shs) := by
  unfold cmapCore; infer_instance
instance isCMapV_persistent (m : GoSlice) (γ : GName) (R : GoString → GoInterface → IProp GF) :
    Persistent (isCMapV m γ R) := by unfold isCMapV; infer_instance
instance cmapShards_persistent (n : Nat) : Persistent (cmapShards (GF := GF) n) := by
  unfold cmapShards; infer_instance
instance cmapOld_persistent (γ : GName) : Persistent (cmapOld (GF := GF) γ) := by
  unfold cmapOld; infer_instance
instance isShard_persistent (sh : Loc) (R : GoString → GoInterface → IProp GF) :
    Persistent (isShard sh R) := by unfold isShard; infer_instance
instance isCMap_persistent (m : GoSlice) (R : GoString → GoInterface → IProp GF) :
    Persistent (isCMap m R) := by unfold isCMap; infer_instance

instance shardP_fractional (mp : Loc) (R : GoString → GoInterface → IProp GF) (γi : GName) :
    Fractional (shardP mp R γi) where
  fractional p q := by
    constructor
    · iintro H
      iunfold shardP at H
      icases H with ⟨%M, HM, Hg, #HR⟩
      icases ((ownMap_fractional (K := GoString) (V := GoInterface) mp M).fractional p q).1 $$ HM
        with ⟨H1, H2⟩
      icases ((ghostVar_half_fractional (GF := GF) γi M).fractional p q).1 $$ Hg with ⟨G1, G2⟩
      isplitl [H1 G1]
      · iunfold shardP; iexists M; iframe H1 G1 HR
      · iunfold shardP; iexists M; iframe H2 G2 HR
    · iintro ⟨H1, H2⟩
      iunfold shardP at H1 H2
      icases H1 with ⟨%M1, HM1, G1, #HR1⟩
      icases H2 with ⟨%M2, HM2, G2, #HR2⟩
      ihave %Heq := ownMap_agree (K := GoString) (V := GoInterface) mp _ _ M1 M2 $$ [HM1 HM2]
      · iframe
      subst Heq
      iunfold shardP
      iexists M1
      iframe HR1
      isplitl [HM1 HM2]
      · iapply ((ownMap_fractional (K := GoString) (V := GoInterface) mp M1).fractional p q).2
        iframe
      · iapply ((ghostVar_half_fractional (GF := GF) γi M1).fractional p q).2
        iframe

/-- The number of reader token bundles `New` makes. -/
def cmapReaders : Nat := Int.toNat sync.rwmutex.actualMaxReaders

/-- `fn` (an `IterCb`) keeps the client's `I` on every entry. -/
def iterOk (fn : GoFunc) (R : GoString → GoInterface → IProp GF) (I : IProp GF) : IProp GF :=
  iprop(□ ∀ (k : GoString) (v : GoInterface) (Φ : val → IProp GF), R k v -∗ I -∗
    ▷ (I -∗ Φ #()) -∗ WP (App (App (Val #fn) (Val #k)) (Val #v)) {{ Φ }})

instance iterOk_persistent (fn : GoFunc) (R : GoString → GoInterface → IProp GF) (I : IProp GF) :
    Persistent (iterOk fn R I) := by unfold iterOk; infer_instance

end defs

end Perennial.github_com.orcaman.concurrent_map
