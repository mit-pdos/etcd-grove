/-
`snap.Snapshotter.DBFilePath(id)` (`etcdserver/api/snap/db.go`; names only): the path of the
database snapshot of index `id` if the file exists, else an error (the snapshot directory
unreadable, or no such file: `ErrNoDBSnapshot`, with a warning). The trust boundary (D22 S-f,
2026-10-19; an axiom in `Proof/.../snap/Snapshotter__DBFilePath.lean`). Lean-first (no Rocq
counterpart); the vocabulary is `Proof/.../snap/Defs.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Defs
public import Spec.fmt.Errorf
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.api.snap
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvSnapshot

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI snap

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `ss.DBFilePath(id)`, `ss` a snapshotter of the directory `sd`, the file of index `id` held
(holding `D`): `snapDBPath sd id` (`dbFilePath(id)`, a join with `s.dir`) and nil, or
an error `fmt` can format, the directory's read having failed (`¬ dirReadOk ss`: D22 receiver
epochs, S8d, 2026-10-24; with the file there, `ErrNoDBSnapshot` is not returned). (wal-link,
2026-11-19, approved by the user via etcd-grove-03: over the directory `sd` of the snapshotter's
`dir` field, `isSnapshotter ss sd`; until then over the opaque `snapDBPath ss`,
`notes/snapdir-crossworld.md`.) -/
abbrev snap.Snapshotter.DBFilePath.spec : Prop :=
  ∀ (ss : Loc) (sd : GoString) (id : w64) (D : backend.Data),
  {{ isSnapshotter (GF := GF) ss sd ∗ backend.fileAt (snapDBPath sd id) D }}
    (App (Val (ss @!! go.GoType.PointerType
        _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter.ty @!!
        go!"DBFilePath")) (Val #id))
  {{ (p : GoString) (err : GoInterface), RET (PairV #p #err);
      backend.fileAt (snapDBPath sd id) D ∗
      (⌜err = GoInterface.nil ∧ p = snapDBPath sd id⌝ ∨
        (⌜err ≠ GoInterface.nil ∧ ¬ dirReadOk ss⌝ ∗ fmt.argOk err)) }}

end spec

end EtcdGrove
end Perennial
