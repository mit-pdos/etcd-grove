/-
**`pbutil.MustMarshalMessage(e)` of a WAL snapshot** (`SaveSnapshot`, S/wal.go:1145): the law the
WAL's proofs take as a hypothesis (W6 of `notes/wal-fsext-plan.md`: "the proofs will take the laws
(`MustMarshalMessage`, ...) as hypotheses"), its encoding the marshaller parameter's `Mr.encSnap`.
`pbutil` is names-only (the main tree's spec, `Spec/go_etcd_io/etcd/pkg/v3/pbutil/MustMarshalMessage.lean`,
is over a registered protobuf type's model; the part has no `walpb.Snapshot` model yet).

**Open (for W6/W11): as stated, the law constrains `Mr` beyond what `walSnapAt` determines.**
`walSnapAt sp sm cs` fixes the `Index` and `Term` and whether `ConfState` is nil, not the conf
state's content (nor unknown fields), which the encoding includes; so the law holds of the real
marshaller only once `walSnapAt` ties the whole object to `sm` (`ConfState'` and no unknown fields),
or `Mr.encSnap` is replaced by the encoding of the object. `Create`'s snapshot (`Index: 0, Term: 0`,
no conf state) is determined. Lean-first.
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
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.pbutil ∗ walSnapAt sp sm cs }}
    (App (Val (@! go_etcd_io.etcd.pkg.v3.pbutil.MustMarshalMessage))
      (Val #(interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.ty) #sp)))
  {{ (d : GoSlice), RET #d; d ↦* Mr.encSnap sm ∗ ownSliceCap w8 d (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
