/- Lean-first (no Rocq counterpart).

`x.startEpoch(m)` (`examples/mvccfull/mvccfull.go`): opens `cfg.Streams` watch streams on the
member's current incarnation `ι` (`E`, `Streams.lean`), each with its receiver and its registrar
goroutines. It takes one `epochTok` per stream (a history reader slot for the receiver, two of
the incarnation's reader tokens, a fraction of its live token) and gives, per stream, the writer's
part of it (`epochStream`: its handles, and its wait groups, which give each goroutine's resources
back at `endEpoch`). `m.streams` goes from `nil` to the new streams; `m.regs` (in its counter
invariant) is reset. The member's `kv` field is read (the incarnation's handle, `isInc`).
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
abbrev runner.startEpoch.spec : Prop :=
  ∀ (E : Ep) (q : Qp),
  {{ epCtx (GF := GF) E ∗ mF go!"kv" E.mp ↦ E.kv ∗ mF go!"streams" E.mp ↦ (slice.nil : GoSlice) ∗
      [∗list] _x ∈ List.replicate (sint.Z E.cfg.Streams').toNat (), epochTok E q }}
    (App (E.x @!! go.GoType.PointerType runner.ty @!! go!"startEpoch") (Val #E.mp))
  {{ RET #(); mF go!"kv" E.mp ↦ E.kv ∗
      ∃ (sl : GoSlice) (ss : List Loc), mF go!"streams" E.mp ↦ sl ∗ sl ↦* ss ∗
        ownSliceCap Loc sl (DFrac.own 1) ∗ ⌜ss.length = (sint.Z E.cfg.Streams').toNat⌝ ∗
        [∗list] s ∈ ss, epochStream E q s }}

end spec

end mvccfull
end EtcdGrove
end Perennial
