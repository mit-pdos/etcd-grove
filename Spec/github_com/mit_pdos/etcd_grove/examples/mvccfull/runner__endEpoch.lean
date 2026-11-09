/- Lean-first (no Rocq counterpart).

`x.endEpoch(m)` (`examples/mvccfull/mvccfull.go`): the epoch's end, by the writer (from `restart`
and `Run`), with the member's streams `ss` (`m.streams`, each `epochStream`). It sets each stream's
stop flag and waits for its registrar (`regDone`: the registrar's resources back, among them its
half of the closed flag), waits until every watcher not cancelled or compacted has every change up
to the member's revision `m.rev` (`complete`, for a revision of the writer's lower bound `Hlb` of the
history), closes each stream (both halves of the closed flag), waits for its receiver (`recvDone`:
the receiver's resources back), and checks that a watch and a cancel on the closed stream fail (with
the writer's own reader token and a fraction `qw` of the incarnation's live token). Every check
passes; `m.streams` is `nil` again, and each stream's `epochTok` is back.
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
abbrev runner.endEpoch.spec : Prop :=
  ∀ (E : Ep) (q qw : Qp) (sl : GoSlice) (ss : List Loc) (rv : w64) (Hlb : List HRev),
  0 ≤ sint.Z rv → sint.Z rv < Hlb.length → sint.Z rv < 2 ^ 63 - 1 →
  {{ epCtx (GF := GF) E ∗ mF go!"streams" E.mp ↦ sl ∗ sl ↦* ss ∗ ([∗list] s ∈ ss, epochStream E q s) ∗
      mF go!"rev" E.mp ↦ rv ∗ histRd E.h E.γh ∗ monoListLbOwn E.γh.l Hlb ∗
      mvccReaders E.ι.kv 1 ∗ epLive E qw }}
    (App (E.x @!! go.GoType.PointerType runner.ty @!! go!"endEpoch") (Val #E.mp))
  {{ RET #(); mF go!"streams" E.mp ↦ (slice.nil : GoSlice) ∗ mF go!"rev" E.mp ↦ rv ∗
      histRd E.h E.γh ∗ mvccReaders E.ι.kv 1 ∗ epLive E qw ∗
      [∗list] _x ∈ List.replicate ss.length (), epochTok E q }}

end spec

end mvccfull
end EtcdGrove
end Perennial
