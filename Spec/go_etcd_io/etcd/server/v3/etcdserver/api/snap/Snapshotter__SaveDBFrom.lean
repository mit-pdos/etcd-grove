/-
## `(*Snapshotter).SaveDBFrom(r, id)` (`db.go:37-96`): trusted (names only)

**Users.** rafthttp's snapshot receiver (2f: the merged `MsgSnap`'s body saved before the message is
processed). Go test of this trusted model: `etcdserverboot/snap.go` (`ReqSnapRoundTrip`).

**Why it is true.** A temporary file, `io.Copy` from `r` (`dbReader`: the image's bytes, or an
error: a cut stream), fsync, then renamed to `<id:016x>.snap.db` unless that file exists (then the
new bytes are discarded: `Snap.saveAt`), the directory fsynced (in both branches: `db.go:58-64`
fsyncs it again when the file is there already). Two updates: the first at the rename (the
directory now shows the file, not yet durably: `snapSaving`), the second after the directory's
fsync (`snapDbs sd (saveAt F id img)`, durable); in the branch where the file exists both fire at
its fsync (`saveAt` keeps the old file). An error of `CreateTemp`, of the copy, of the temporary
file's fsync or of the rename is returned with nothing changed (the temporary file removed): the
first update is given back. An error of the directory's fsync is returned by the Go code after the
rename; it is `diskOk`'s (its docstring lists it).

**Changes** (from `specs-ref`'s `Snapshotter__SaveDBFrom.lean`): over the db files' model.
Changes: verify-round (A8 provability F7, F9): two updates around the directory's fsync
(`snapSaving`, the crash law `snapSaving_crash`); the directory fsync's error named as `diskOk`'s
(the round-1 error arm, "nothing changed", was false after the rename).

Last pass (backend-schema's request): the directory fsync (on success, in both branches) also
makes durable a pending rename onto any entry `p` of `sd` (`inDir sd p`: the backend file
`<snap dir>/db` after `OpenSnapshotBackend`): the second update (the directory fsync, the real
atomic point) takes the revert state `revertSt p os` in its precondition (any `os`; re-review N3:
the list of files a crash may bring back) and gives `revertSt p []` (`beNoRevert p`);
on an error neither update fired has touched it. Final relay round (rafthttp's request): the
revert state is in the update, not held for the whole call (round "last pass" held it from the
call's start, which two concurrent snapshot handlers could not both do).

**Margin.** The byte count is not stated.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Api
public import Spec.go_uber_org.zap.Api
public import Spec.go_etcd_io.etcd.server.v3.storage.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Snap

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.snap.Assumptions]

/-- **Saves the database snapshot read from `r` at index `id`**, durably (or fails, changing
nothing): an update at the rename, a second once the directory is fsynced. -/
def Snapshotter.SaveDBFrom.spec : Prop :=
  ∀ (ss : Loc) (sd : GoString) (r : GoInterface) (img : BeImage) (id : w64) (Q : IProp GF)
    (p : GoString),
  let au : IProp GF := iprop(AU <{ ∃∃ (F : Nat → Option BeImage), snapDbs sd F }> @ ⊤, ∅
        <{ snapSaving sd F (uint.nat id) img, COMM
           AU <{ ∃∃ (os : List (Option BeImage)), snapSaving sd F (uint.nat id) img ∗
                   revertSt p os }> @ ⊤, ∅
             <{ snapDbs sd (saveAt F (uint.nat id) img) ∗ revertSt p [], COMM Q }> }>)
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.snap ∗ isSnapshotter ss sd ∗ dbReader r img ∗ ⌜ServerStorage.diskOk ∧ inDir sd p⌝ ∗ au }}
    (App (App (Val (ss @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter.ty @!! go!"SaveDBFrom")) (Val #r)) (Val #id))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      (⌜err = GoInterface.nil⌝ ∗ Q) ∨ (⌜err ≠ GoInterface.nil⌝ ∗ au) }}

end spec

end Snap
end EtcdGrove
end Perennial
