/-
`newSnapshotReaderCloser(lg, snapshot)` (`snapshot_merge.go`): the database snapshot streamed
into a pipe by a goroutine, the pipe's reader returned. Lean-first (no Rocq counterpart); D22
S-h, 2026-10-20 (`notes/decisions.md`, "D22 S-h carried out"). The vocabulary is the backend's
`InvSnapshot.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvSnapshot

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `newSnapshotReaderCloser(lg, sp)`, of a non-nil logger and half of a snapshot open over bbolt's
committed data `D` (`snapOpenQ`, consumed: the goroutine streams it, then closes it): a reader
whose complete streams are bbolt images of `D` (`readerStreams`, the transport's `SendSnapshot`
takes it), given for the other half (the caller reads the snapshot's `Size` first: the pipe's
hand-over, `Proof/io/Defs.lean`). The goroutine writes the snapshot into the pipe (`WriteTo`),
closes the pipe's writer with `WriteTo`'s error (so the reader's stream ends in `io.EOF` only after
a complete image), which hands it the other half, and closes the whole snapshot; it does not
panic: an open snapshot's `Close` returns nil (`backend.snapshot.Close.spec`), and only a failed
close reaches `lg.Panic`. -/
abbrev newSnapshotReaderCloser.spec : Prop :=
  ∀ (lg sp : Loc) (D : backend.Data) (γ : GName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ ⌜lg ≠ null⌝ ∗
      backend.snapOpenQ sp D γ (1 : Qp).half }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.newSnapshotReaderCloser)) (Val #lg))
      (Val #(interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.snapshot.ty) #sp)))
  {{ (rc : GoInterface), RET #rc;
      backend.snapOpenQ sp D γ (1 : Qp).half -∗
        backend.readerStreams rc (fun bs => backend.boltImage bs D) }}

end spec

end EtcdGrove
end Perennial
