/-
# The backend's file and crashes, over bbolt's (batch 4a, round 1)

The laws that tie 4a's file vocabulary to 4c's (`Spec/go_etcd_io/bbolt/Api.lean`): only the opener
(2e's `OpenBackend`, `OpenSnapshotBackend`, the restart) and the crash argument import this module.

* `imgOf D`: bbolt's data as etcd sees it (the root's buckets and their plain values; sequence
  counters dropped; nested buckets, which etcd never makes, read as absent values).
* `beFile_of`: **a file bbolt holds is a backend file of its image** (4c's `fileHolds`, from
  `fileHolds_new` for a fresh path or a deleted file, `fileHolds_image` for a received snapshot's
  file, or the crash law): so `New` can be called. `beFile_none`: an absent path (`osMeta … none`).
  Renaming a snapshot file over the backend's path (`os.Rename` in `OpenSnapshotBackend`) carries
  `fileHolds` by OsFs's rename rule, hence `beFile`.
* `beCrash`: **a crash leaves the file at one of the committed images** (4c's `boltCrash`, over the
  history the client keeps in an invariant): from the file's crash invariant `beDurInv γ p`, crash
  safety on (`beSynced γ`: `UnsafeNoFsync` off), the client's `beHist γ L` (any fraction of bbolt's
  state is folded into it: the realization keeps one in the history's authority) and OsFs's restart
  resources, the next generation gets `beFile p (some I)` for some `I ∈ L`. Serves 2d's item 3 (a
  restart finds a committed image, whose meaning the server's invariant attached at its commit),
  2e's `memberDisk`, 3c's item 4 (a session's writes land in one commit).

The next generation's `beFile` is the same opaque predicate (it takes no heap); its realization
over 4c's `fileHolds` at the new generation is part of the gap below.

Recorded gap: the realizations of `beFile`, `beHist`, `isBackend` and the sessions hold 4c's
resources, which carry `[HasExt osFsExt]`; at integration those predicates and the specs over them
gain the binder inside their statements (PRINCIPLES, "An instance binder a statement must carry goes
inside the statement"), as here.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.Api
public import Spec.go_etcd_io.bbolt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Backend

open Iris Iris.BI

section model
variable [GooseExts]

open Classical in
/-- **bbolt's data as etcd sees it**: the root's buckets and their plain values. -/
def imgOf (D : Bbolt.Data) : Image :=
  { made := fun b => decide (Bbolt.Ent.bktAt D [b]),
    ents := fun b k => match D.atPath [b, k] with
      | some (.val v) => some v
      | _ => none,
    clean := fun _ => true }

end model

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **A file bbolt holds is a backend file of its image.** -/
def beFile_of.spec : Prop :=
  ∀ [HasExt osFsExt] (p : GoString) (D : Bbolt.Data),
    Bbolt.fileHolds (GF := GF) p D ⊢ beFile p (some (imgOf D))

/-- **No file at `p`**: a backend file that `New` creates empty. -/
def beFile_none.spec : Prop :=
  ∀ [HasExt osFsExt] (p : GoString), osMeta (GF := GF) p (DFrac.own 1) none ⊢ beFile p none

/-- **The crash law** (see the header): the next generation `L'` finds the file at one of the
committed images. -/
def beCrash.spec : Prop :=
  ∀ [HasExt osFsExt] (L' : GooseLocalGS GF) (γ : BeNames) (p : GoString) (L : List Image)
    (Ps : List GoString),
    p ∉ Ps →
    beDurInv (GF := GF) γ p ∗ beSynced γ ∗ beHist γ L ∗ crashed ∗
      crashRest (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) Ps ⊢
    |={⊤}=> ∃ I : Image, ⌜I ∈ L⌝ ∗
      beFile (GF := GF) p (some I) ∗
      crashRest (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) (p :: Ps)

end laws

end Backend
end EtcdGrove
end Perennial
