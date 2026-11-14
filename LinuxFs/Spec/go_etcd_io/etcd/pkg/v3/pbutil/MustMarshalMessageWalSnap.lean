/-
**`pbutil.MustMarshalMessage(e)` of a WAL snapshot** (`SaveSnapshot`, S/wal.go:1145): the law the
WAL's proofs take as a hypothesis (W6 of `notes/wal-fsext-plan.md`: "the proofs will take the laws
(`MustMarshalMessage`, ...) as hypotheses"), its encoding the marshaller parameter's `Mr.encSnap`, in a fresh non-nil slice (protobuf-go's
`Marshal` returns a non-nil slice, empty or not: `MarshalPb.lean`).
`pbutil` is names-only (the main tree's spec, `Spec/go_etcd_io/etcd/pkg/v3/pbutil/MustMarshalMessage.lean`,
is over a registered protobuf type's content).

`walSnapAt Mr sp sm cs` (`walpb/PbSnapshot.lean`) is a frozen `walpb.Snapshot` at a content `c` whose
encoding `snapEnc c` (protobuf-go's, `snapEncC_ok`) is `Mr.encSnap sm`, so the law holds of the real
`MustMarshalMessage`: it is the main tree's generic spec at the registered `pbSnapC` (`pbSnapC_reg`;
`pbEncC pbSnapC c = snapEnc c`), plus protobuf-go's non-nil result (`Marshal` returns a non-nil slice,
empty or not), which the generic spec does not state. Not derived here: the part has no copy of the
generic spec yet. Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.WalDisk
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.WalEncRecs
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.DepsPkgInit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open WalEnc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev go_etcd_io.etcd.pkg.v3.pbutil.MustMarshalMessage.specWalSnap (Mr : WalMarshal) : Prop :=
  ∀ (sp : Loc) (sm : SnapshotMetadataM) (cs : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.pbutil ∗ walSnapAt Mr sp sm cs }}
    (App (Val (@! go_etcd_io.etcd.pkg.v3.pbutil.MustMarshalMessage))
      (Val #(interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.ty) #sp)))
  {{ (d : GoSlice), RET #d;
      ⌜d ≠ slice.nil⌝ ∗ d ↦* Mr.encSnap sm ∗ ownSliceCap w8 d (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
