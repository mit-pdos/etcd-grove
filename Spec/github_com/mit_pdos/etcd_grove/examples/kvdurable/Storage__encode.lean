/- Lean-first (no Rocq counterpart).

`s.encode()` (storage.go): the storage's contents `M` as its file holds them (`encStor M`): the
replica's hard state copy, the snapshot, the log's start and the entries after it. The caller holds
the replica's `dmu` (so `M` is the contents between two groups of changes) with what it records of
the storage (`kdStorView`, the hard state copy), and the storage attached at its key.

(**API gaps**, `stageI-5-clients.md`: G2, the share of the uncommitted log `kdStorView` holds is not
the client's under raft's storage contract; G3, `MemoryStorage.Snapshot`'s attached mode does not
say which snapshot is stored, only a lower bound of its index, so the snapshot read here is `M`'s
only with a spec that names it.)
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

/-- See the file header. -/
abbrev Storage.encode.spec : Prop :=
  ∀ (s ms : Loc) (γs : MemStorNames) (J : MemJust GF) (hsp : Loc) (M : StorFile),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvdurable ∗ kdStorRec s ms γs ∗ memStorInvP ms γs J ∗
      s.[KStorage, go!"hs"] ↦ hsp ∗ hsOpt hsp M.hs ∗ kdStorView γs M ∗ ⌜KdFileOk M⌝ }}
    (App (Val (s @!! go.GoType.PointerType kStorageTy @!! go!"encode")) (Val #()))
  {{ (sl : GoSlice), RET #sl; sl ↦* encStor M ∗ ownSliceCap w8 sl (DFrac.own 1) ∗
      s.[KStorage, go!"hs"] ↦ hsp ∗ kdStorView γs M }}

end spec

end kvdurable
end EtcdGrove
end Perennial
