/-
`sendFragments(wr, maxRequestBytes, sendFunc)` (`watch.go`): a response sent whole or cut into
fragments.

**Users.** `sendLoop`'s `sendWatch` (`watch.go:488`) for an id created with `Fragment`, with
`sws.gRPCStream.Send` as `sendFunc`. (No old spec: added, `sendLoop`'s sketch needs it.)

**Proof sketch.** `proto.Size(wr)` (2a's `proto` boundary: an `int`, no panic, for a message owned
at any fraction): below the budget or fewer than two events, one call of `sendFunc` with `wr`
(`fragmentsOf`'s first case). Else a loop with `idx` (the events sent so far), invariant `S ms` with
`ms` the fragments sent, `fragPrefix wr ms`, `ms`' events `wr.Events[:idx]`: a fresh
`WatchResponse` `cur` (`wireWatchRespOwn_unfold`; `wr`'s header pointer and event pointers shared,
read-only: `wr` is persisted, `DFrac.discard`) gets the events from `idx` on while its size stays
below the budget, at least one (the `len(cur.Events) > 1` guard); `Fragment` unless it took the
last; persisted and passed to `sendFunc` (the premise, at `fragPrefix wr (ms ++ [cur])`); an error
returns it; the last fragment ends the loop with `fragmentsOf wr ms`.

**Changes**: new. verify-round (client-watch's request W1): 1b's `wireStep` now requires every fragment after
the first, and the completing response, to carry the first fragment's id, header, compaction
revision and cancel reason (`WireSt.frag`); true here: each fragment is a copy of `wr` with only
`Events` (and `Fragment`) changed (`watch.go`'s `sendFragments` builds `cur := *wr` per fragment),
so the id, header, compact revision and cancel reason are `wr`'s in every fragment.

**Margin.** Which cut (the sizes are not modelled): any `fragmentsOf`.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ApiWatch

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3rpc

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`sendFragments(wr, maxRequestBytes, sendFunc)`**, for a `sendFunc` that sends each message
it is given in a state `S` indexed by the messages sent so far: sends `wr` whole or as fragments
(`fragmentsOf`), in order, stopping at the first error, which it returns. -/
def sendFragments.spec : Prop :=
  ∀ (wr : Loc) (m : WireWatchRespM) (mrb : w64) (send : GoFunc)
    (S : List WireWatchRespM → IProp GF),
  (∀ (ms : List WireWatchRespM) (p : Loc) (m' : WireWatchRespM),
    {{ S ms ∗ wireWatchRespOwn p DFrac.discard m' ∗ ⌜fragPrefix m (ms ++ [m'])⌝ }}
      (App (Val #send) (Val #p))
    {{ (err : GoInterface), RET #err;
        (⌜err = GoInterface.nil⌝ ∗ S (ms ++ [m'])) ∨ ⌜err ≠ GoInterface.nil⌝ }}) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      wireWatchRespOwn wr DFrac.discard m ∗ S [] }}
    (App (App (App (Val (@! v3rpc.sendFragments)) (Val #wr)) (Val #mrb)) (Val #send))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ ∃ ms, ⌜fragmentsOf m ms⌝ ∗ S ms) ∨ ⌜err ≠ GoInterface.nil⌝ }}

end spec

end V3rpc
end EtcdGrove
end Perennial
