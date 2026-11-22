-- The copy for the part `KvNet/` of `RaftNoAx/Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvdurablenoax/Storage__encode.lean` (etc/copy-part.py; rerun it, do not edit).
/- Lean-first (no Rocq counterpart).

`s.encode()` (storage.go): the contents `M` the storage's image holds, as its file holds them
(`encStor M`): the hard state, the snapshot, the log's start and the entries after it. The caller
holds the replica's `dmu` (so `M` is the contents between two groups of changes), which holds the
image (`kdDmuInv`); the `MemoryStorage` is not read (the image is the replica's own record of its
contents, which its storage changes keep: `Image.lean`).
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Image

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev Storage.encode.spec : Prop :=
  ∀ (s ip : Loc) (M : StorFile),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗
      s.[KStorage, go!"img"] ↦□ ip ∗ ownImage ip M }}
    (App (Val (s @!! go.GoType.PointerType kStorageTy @!! go!"encode")) (Val #()))
  {{ (sl : GoSlice), RET #sl; sl ↦* encStor M ∗ ownSliceCap w8 sl (DFrac.own 1) ∗ ownImage ip M }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
