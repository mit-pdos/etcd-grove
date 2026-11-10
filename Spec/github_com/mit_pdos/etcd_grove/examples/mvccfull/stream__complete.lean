/- Lean-first (no Rocq counterpart).

`s.complete(upto)` (`examples/mvccfull/mvccfull.go`): whether every watcher not cancelled or
compacted has every change up to revision `upto`, read under `s.mu` through `expect`, for a lower
bound `Hlb` of the history that has `upto`. It makes no check: `endEpoch` only loops until it says
so, so the spec states nothing of the answer (a liveness fact partial correctness cannot use).
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
abbrev stream.complete.spec : Prop :=
  ∀ (T : Strm) (Hlb : List HRev) (upto : w64),
  0 ≤ sint.Z upto → sint.Z upto < Hlb.length → sint.Z upto < 2 ^ 63 - 1 →
  {{ streamCtx (GF := GF) T ∗ histRd T.ep.h T.ep.γh ∗ monoListLbOwn T.ep.γh.l Hlb }}
    (App (T.s @!! go.GoType.PointerType stream.ty @!! go!"complete") (Val #upto))
  {{ (b : Bool), RET #b; histRd T.ep.h T.ep.γh }}

end spec

end mvccfull
end EtcdGrove
end Perennial
