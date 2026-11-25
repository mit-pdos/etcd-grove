-- The copy for the part `KvRaft/` of `RaftNoAx/Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvdurablenoax/image__compact.lean` (etc/copy-part.py; rerun it, do not edit).
/- Lean-first (no Rocq counterpart).

`m.compact(i)` (storage.go): `MemoryStorage.Compact` on the image: refused with `ErrCompacted`
(`eco`), the image unchanged, when `i` is at most the log's start (`imgCompactStale`); otherwise
`nil`, and the image holds `imgCompact I i` (the log starting at `i`, at its term there, with the
entries after it). It does not panic: `i` is at most the log's last index.
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Image

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev image.compact.spec : Prop :=
  ∀ (p : Loc) (I : StorFile) (i : w64) (eco : GoInterface),
  uint.nat i ≤ uint.nat I.prev + I.ents.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗
      ownImage p I ∗ globalAddr ErrCompacted ↦□ eco }}
    (App (Val (p @!! go.GoType.PointerType kImageTy @!! go!"compact")) (Val #i))
  {{ (err : GoInterface), RET #err;
      (if imgCompactStale I i then iprop(⌜err = eco⌝ ∗ ownImage p I)
       else iprop(⌜err = interface.nil⌝ ∗ ownImage p (imgCompact I i))) }}

end spec

end kvraft
end EtcdGrove
end Perennial
