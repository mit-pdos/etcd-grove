/-
**The snapshot sender, opaque** (rafthttp stage 6b; D34, the user's choice: the snapshot stream a
trust-boundary axiom cut at its own functions). `snapshot_sender.go` is untranslated (the
configuration's `!newSnapshotSender`, `!snapshotSender.*`): `newSnapshotSender` gives a sender
(`snapSenderOk`, persistent) and the right to stop it once (`snapSenderStop`); its `send`, reached
only through `Transport.SendSnapshot` (untranslated too), is that axiom's. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Stream

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- `snapSenderOk`'s fact, raw (opaque). -/
opaque snapSenderRaw (Rh : RaftHttp GF) (pid : w64) (s : Loc) : IProp GF

/-- **A snapshot sender `s` to the peer `pid`** (persistent): what `newSnapshotSender` returns. -/
def snapSenderOk (Rh : RaftHttp GF) (pid : w64) (s : Loc) : IProp GF := iprop(□ snapSenderRaw Rh pid s)

instance snapSenderOk_persistent (Rh : RaftHttp GF) (pid : w64) (s : Loc) :
    Persistent (snapSenderOk Rh pid s) := by
  unfold snapSenderOk; infer_instance

/-- **The right to stop the snapshot sender `s`** (exclusive, once: `stop` closes its `stopc`). -/
opaque snapSenderStop (s : Loc) : IProp GF

end defs

end EtcdGrove
end Perennial
