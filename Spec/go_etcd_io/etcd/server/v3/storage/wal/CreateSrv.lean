/-
**`wal.Create(lg, dir, md)` in a member's fresh WAL area, in the server's vocabulary** (claim #34, stage
4, 2026-11-25): what `bootstrapNewWAL` (`bootstrap.go:724` at the etcd pin `edc800c6f`) needs of `Create`.
Lean-first.

From the WAL area `walAreaFresh dir` (`storage/WalAreaFresh.lean`, what `bootstrap`'s slot `wal.bootRes`
holds: the area's invariants, its program's part, the whole call permission of its root, the
generation's lock token and no WAL in `dir`) and the metadata `walMetaEnc id cid`, `Create` **succeeds**,
and the WAL is open in `dir` with the member's metadata and no records (`walOpenedH … walFresh []`, sized:
`Create` writes the metadata, the empty snapshot record and no entry), with the right to close it with
its files kept (`walPurgeRight`): what `wal.bootOk` holds. (P5, 2026-11-25, approved by coordinator-E on
#50, 07:04Z) The records' history is stated, and empty (`walRecsH … walFresh []`, where it said
`walRecs … walFresh`): layer 1's `Create` leaves the fresh durable state `walDurFresh`, whose history is
`[]`; the crash-aware durability invariant's allocation needs it (`rnDurK_alloc`).

**Not proved: a hypothesis** (`?` in the server's `Link.lean`) of `bootstrapNewWAL`'s linked result,
#15's to prove (the WAL plan's L5, `notes/wal-link-scope.md`: `bootstrap`'s WAL part). It holds of Go
on a disk that does not fail on the area's files and paths (`walAreaFresh`'s no-I/O-error instance
`a.sat`): `Create` fails only on an I/O error, or when a WAL is already in `dir`. Its proof needs, from
layer 1 and the slot (found 2026-11-25, `notes/STATUS.md`, "`bootstrapNewWAL` and `wal.Create`"):
1. **a no-error `Create`**: `Create.spec`'s two error arms carry no witness that the file system failed
   (`¬ FsNoErrOn …`), as `cut.spec`'s and `sync.specNoErr`'s do, so no spec of `Create` excludes its
   error today;
2. **the fresh room**: `Create.spec` gives the handle as `walOpenWF`, and the shared handle under
   coverage (`walOpenWS_alloc` through `walHdl`, `walCov a.Sio`) needs `walOpenWFR … walFreshRoom`, the
   stream's end below `2 ^ 43` (`cut.spec` states it of its new segment's headers; `Create` writes the
   same headers);
3. **`walAreaFresh` covering `Create`'s paths**: `Create.spec` takes `FsNoErrOn` of `dir`, `dir.tmp` and
   the area `r` (with `PathFits`), but the area covers by path only `dir` and the paths below it
   (`a.Sio.path a.dir`, `a.covP`), not `dir.tmp` (nor what `Create` makes below it) or `r`: the slot's
   body grows (the slot convention: this statement does not change);
4. the glue: `walAbsent` as `Create`'s view (`Pv o := o = none`), the history's authority allocated at
   `walDurFresh md`'s (`monoListAuthOwn`, `walRecs`' sealed body, an intro law beside it), and the
   handle shared (`walOpenWS_alloc`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.WalApi
public import Spec.go_uber_org.zap.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- See the file header. -/
abbrev wal.Create.specSrv : Prop :=
  ∀ (lg : Loc) (dir : GoString) (mp : GoSlice) (id cid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ zapLoggerOk lg ∗
      mp ↦*□ walMetaEnc id cid ∗ walAreaFresh dir }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.Create)) (Val #lg)) (Val #dir))
      (Val #mp))
  {{ (w : Loc) (err : GoInterface), RET (PairV #w #err);
      ⌜err = GoInterface.nil⌝ ∗
      ∃ h : WalH GF, ⌜h.w = w⌝ ∗ walOpenedH h dir id cid walFresh [] true ∗ walPurgeRight h }}

end spec

end EtcdGrove
end Perennial
