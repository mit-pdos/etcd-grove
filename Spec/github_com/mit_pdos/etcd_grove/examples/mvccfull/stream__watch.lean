/- Lean-first (no Rocq counterpart).

`s.watch()` (`examples/mvccfull/mvccfull.go`): the registrar registers a watcher, unless the member
has `cfg.Watchers` registrations already (`m.regs`, a counter): a random key and end (the end made
`nil` when it would make the range empty), a random filter (`filterFs`: NoPut, NoDelete or none),
from revision `0`, from any revision up to two past `revHi`, or from `cmpLo` (at least `1`). Under
`s.mu`, between `revLo` and `revHi` loads, `Watch` with the registrar's update at the incarnation's
and the stream's invariants: the stream is open (the registrar's half of the closed flag), so the
watcher is registered under a fresh id, which enters both halves of the registry with its
registration (`Reg`: `lo = watchLo σ start`, the sent count `k` with its `wsSentLb`), and the
watcher's struct enters the lock's map and order (a watcher from `0` floats in
`[revLo + 1, revHi + 1]`, `wPosOk'`: positive by `revLo_acc`'s `1 ≤ revLo`; its start and revision
below `2 ^ 63 - 1` by `revHi_acc`'s `revHi < 2 ^ 62`). Every check passes (no error; a fresh id: the registry is the
stream's watchers, `regOk'`); the registrar's resources back.
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
abbrev stream.watch.spec : Prop :=
  ∀ (T : Strm) (q : Qp) (C : List w64),
  {{ streamCtx (GF := GF) T ∗ regOwn T q C }}
    (App (T.s @!! go.GoType.PointerType stream.ty @!! go!"watch") (Val #()))
  {{ RET #(); regOwn T q C }}

end spec

end mvccfull
end EtcdGrove
end Perennial
