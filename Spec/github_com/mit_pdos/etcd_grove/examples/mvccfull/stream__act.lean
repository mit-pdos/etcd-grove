/- Lean-first (no Rocq counterpart).

`s.act()` (`examples/mvccfull/mvccfull.go`): one step of the registrar of the stream `T`
(`Streams.lean`), with its resources (`regOwn`: a reader token of the incarnation, a fraction of its
live token, its half of the closed flag at `false`, its cancel record `C`): a registration
(`watch`), a cancel (`cancel`), a progress request for a watcher not cancelled (`pick` under `s.mu`)
or for the stream, the stream's revision checked against the member's bounds (`revLo` before, the
store's revision, `revHi` after: `inBounds`), or a watch of an empty range, which must fail. Every
check passes; the registrar's resources back, its cancel record possibly grown.
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
abbrev stream.act.spec : Prop :=
  ∀ (T : Strm) (q : Qp) (C : List w64),
  {{ streamCtx (GF := GF) T ∗ regOwn T q C }}
    (App (T.s @!! go.GoType.PointerType stream.ty @!! go!"act") (Val #()))
  {{ RET #(); ∃ C' : List w64, regOwn T q C' }}

end spec

end mvccfull
end EtcdGrove
end Perennial
