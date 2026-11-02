/- Lean-first (no Rocq counterpart).

`s.ApplySnapshot(snap)` (storage.go): `MemoryStorage.ApplySnapshot(snap)`, then the image's
(`image.applySnapshot`), whose answer it returns. Stated over any triple of the `MemoryStorage`'s call
that gives the snapshot back owned at `dq` (`MemoryStorage.ApplySnapshot.spec`'s, in either mode, with
`P` its precondition and `Q` the rest of its postcondition): the caller holds the replica's `dmu`
(the image), or owns the storage before its node runs.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Image
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.KdStorage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]

/-- See the file header. -/
abbrev Storage.ApplySnapshot.spec : Prop :=
  ∀ (s ms : Loc) (γs : MemStorNames) (ip : Loc) (I : StorFile) (sp : Loc) (dq : DFrac)
    (sv : SnapshotM) (eood : GoInterface) (P Q : IProp GF),
  {{ P }}
    (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"ApplySnapshot")) (Val #sp))
  {{ RET #interface.nil; ownSnapM sp dq sv ∗ Q }} →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvdurable ∗
      kdStorRec s ms γs ∗ s.[KStorage, go!"img"] ↦□ ip ∗ ownImage ip I ∗
      globalAddr ErrSnapOutOfDate ↦□ eood ∗ P }}
    (App (Val (s @!! go.GoType.PointerType kStorageTy @!! go!"ApplySnapshot")) (Val #sp))
  {{ (err : GoInterface), RET #err; ownSnapM sp dq sv ∗ Q ∗
      (if imgSnapStale I sv then iprop(⌜err = eood⌝ ∗ ownImage ip I)
       else iprop(⌜err = interface.nil⌝ ∗ ownImage ip (imgApplySnapshot I sv))) }}

end spec

end kvdurable
end EtcdGrove
end Perennial
