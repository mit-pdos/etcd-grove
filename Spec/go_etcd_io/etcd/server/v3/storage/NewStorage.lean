/-
`storage.NewStorage(lg, w, s)` (`server/storage/storage.go:54-56`; wal-link L2, 2026-11-17,
`notes/wal-link-scope.md` §2): the server's WAL storage. Proved in `Proof/.../storage/NewStorage.lean`.
Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.StorageRep

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI storage

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]

/-- **`NewStorage(lg, w, ss)`** returns, as a `Storage`, a fresh `*storage` `p` over the WAL `w` and the
snapshotter `ss` (`storageOver`, persistent) with two reader tokens of its lock (`storageRd`): one for etcd's
raft loop, one for its apply thread (`StorageRep.lean`). -/
abbrev storage.NewStorage.spec : Prop :=
  ∀ (lg w ss : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.NewStorage)) (Val #lg)) (Val #w)) (Val #ss))
  {{ (p : Loc), RET #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty) #p);
      storageOver p w ss ∗ storageRd p w ∗ storageRd p w }}

end spec

end EtcdGrove
end Perennial
