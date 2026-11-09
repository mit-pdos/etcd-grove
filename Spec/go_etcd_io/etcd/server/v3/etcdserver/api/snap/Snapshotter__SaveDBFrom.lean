/-
## `(*Snapshotter).SaveDBFrom(r, id)` (`db.go:37-96`): trusted (names only)

**Users.** rafthttp's snapshot receiver (2f: the merged `MsgSnap`'s body saved before the message is
processed). Go test of this trusted model: `etcdserverboot/snap.go` (`ReqSnapRoundTrip`).

**Why it is true.** A temporary file, `io.Copy` from `r` (`dbReader`: the image's bytes, or an
error: a cut stream), fsync, then renamed to `<id:016x>.snap.db` unless that file exists (then the
new bytes are discarded: `Snap.saveAt`), the directory fsynced. On a copy error the temporary file
is removed and the error returned: nothing changed (the update is given back). An error of the
rename or the fsyncs is `diskOk`'s.

**Changes** (from `specs-ref`'s `Snapshotter__SaveDBFrom.lean`): over the db files' model.

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

/-- **Saves the database snapshot read from `r` at index `id`** (or fails, changing nothing). -/
def Snapshotter.SaveDBFrom.spec : Prop :=
  ∀ (ss : Loc) (sd : GoString) (r : GoInterface) (img : BeImage) (id : w64) (Q : IProp GF),
  let au : IProp GF := iprop(AU <{ ∃∃ (F : Nat → Option BeImage), snapDbs sd F }> @ ⊤, ∅
        <{ snapDbs sd (saveAt F (uint.nat id) img), COMM Q }>)
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.snap ∗ isSnapshotter ss sd ∗ dbReader r img ∗ ⌜ServerStorage.diskOk⌝ ∗ au }}
    (App (App (Val (ss @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter.ty @!! go!"SaveDBFrom")) (Val #r)) (Val #id))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      (⌜err = GoInterface.nil⌝ ∗ Q) ∨ (⌜err ≠ GoInterface.nil⌝ ∗ au) }}

end spec

end Snap
end EtcdGrove
end Perennial
