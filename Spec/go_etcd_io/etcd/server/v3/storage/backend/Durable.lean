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

The next generation's `beFile` must be at the next generation's heap; see the gap below.

Recorded gap (integration, 2026-11-09; checked with `#check`): the gap is wider than the
extension binder. `Api.lean`'s opaque predicates are declared under section variables their
`iprop(True)` bodies do not use, so Lean drops them: `#check @beFile` is `{GF} → GoString → Option
Image → IProp GF`, with **no `HeapGS` and no `HasExt osFsExt`** (likewise `isBackend`, `beHist`,
`beCur`, `beSess`, ...). None of them can be realized over the heap (a points-to needs `hG`) or over
4c's predicates, and `beCrash`'s conclusion cannot name the next generation's heap. Not fixable in
this file (the predicates are `Api.lean`'s). The fix, in `Api.lean`:
1. every opaque resource predicate takes `[GooseSemantics] [GooseInterp] [hG : HeapGS HasLC.hasLC
   GF]` in its own signature (as 4c's `Bbolt.Api`; `GooseExts` is kept already);
2. `HasExt osFsExt` need **not** be a binder of the backend's predicates or triples: it is a `Prop`
   class (`Perennial/GooseLang/Lifting.lean`), so a realization over 4c's predicates holds it as
   `∃ _ : HasExt osFsExt, …` (proof-irrelevant: every instance is the same). Every triple's
   predicates come from `New`, whose premise `beFile` carries it; only the three laws here, which
   build `beFile` from bbolt's or OsFs's resources, take the binder (they do);
3. then `beCrash`'s conclusion becomes `@beFile _ _ _ GF ⟨hG.goose_globalGS, L'⟩ p (some I)` (the
   next generation's heap, as `Bbolt.boltCrash`'s `fileHolds`), and `beFile_of`/`beFile_none` are
   unchanged.
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
