/- Lean-first (no Rocq counterpart).

`s.cancel()` (`examples/mvccfull/mvccfull.go`): under `s.mu`, a registered watcher not marked
(`pick`) is marked cancelled (its struct and both halves of the registry, the stream's invariant
opened); then `Cancel` of it, by the registrar's update (its id added to the registrar's cancel
record `C`: from then on the watcher may be not live, `regOk'`), which succeeds (the watcher is the
stream's, the stream open), and `Cancel` again, which succeeds or fails with
`ErrWatcherNotExist`. Every check passes; the registrar's resources back, its cancel record
possibly grown.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Streams

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- See the file header. -/
abbrev stream.cancel.spec : Prop :=
  ∀ (T : Strm) (q : Qp) (C : List w64),
  {{ streamCtx (GF := GF) T ∗ regOwn T q C }}
    (App (T.s @!! go.GoType.PointerType stream.ty @!! go!"cancel") (Val #()))
  {{ RET #(); ∃ C' : List w64, regOwn T q C' }}

end spec

end mvccfull
end EtcdGrove
end Perennial
