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

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI snap

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `ss.DBFilePath(id)`: `snapDBPath ss id` and nil, or an error `fmt` can format. -/
abbrev snap.Snapshotter.DBFilePath.spec : Prop :=
  ∀ (ss : Loc) (id : w64),
  {{ isSnapshotter (GF := GF) ss }}
    (App (Val (ss @!! go.GoType.PointerType
        _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter.ty @!!
        go!"DBFilePath")) (Val #id))
  {{ (p : GoString) (err : GoInterface), RET (PairV #p #err);
      ⌜err = GoInterface.nil ∧ p = snapDBPath ss id⌝ ∨ (⌜err ≠ GoInterface.nil⌝ ∗ fmt.argOk err) }}

end spec

end EtcdGrove
end Perennial
