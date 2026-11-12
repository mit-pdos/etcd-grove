/- Lean-first (no Rocq counterpart).

`s.receive(resp)` (`examples/mvccfull/mvccfull.go`): under `s.mu` (`smuBody` at `rs`), the
receiver's check of the response `r` it just received (`wsRecv` at `rs ++ [r]`, `wrespIs`), with its
half of `σs.rcv` at `rs`. By `recv_facts` (`Streams.lean`: `wsRecvOk` at the incarnation's state,
the registry, `onceUpTo` everywhere), each check of `receive` is a clause of the watch guarantee: a
revision written (clause 1, `r.rev < |σ.notifiedLog|`, against `revHi` loaded after: `readQ`'s
lower bound of the monotone notified length, `nrevHi_acc`, since a response may be at the revision
still pending, `revHi`'s own lower bound being only the committed revision's); eventless revisions non-decreasing
(clause 5, `eventlessOk`); a stream progress response covers every stamped, unmarked watcher
(clause 3 with `w.k ≤ j` from the stamp, `w.live` from the mark); a watcher's (clause 1: a
registered one, `regOk'`); a compaction response's revision compacted (clause 1, against `cmpHi`
loaded after); a watcher's progress at least its first revision less one (clause 4, with the
floating window) and after its expected changes up to it (clause 3); each event its watcher's next
expected change (clause 2 with `watchEvents_filtered_eq_expChs`), at or below the response's
revision, with its fields; now and then the event's previous key-value read (`checkStoreRange`,
the receiver's reader token). Every check passes; the lock's body and the receiver's half at
`rs ++ [r]` (the registry unchanged, the history's bound and the eventless revision possibly
grown).

The progress response's coverage of compacted watchers (`mvccfull.go`, `stamped && !cancelled`,
compacted or not) rests on `wsRecvOk`'s clause 3 of a live compacted watcher, vacuous only because
`memberState` keeps `onceUpToAll` (through `recv_facts`' `onceUpTo`): weakening `onceUpToAll` would
make that check unprovable. `covered`'s and `expect`'s `changesAt` panic (not a `check`) is ruled
out by `histOkM`: the position is below `|σ.notifiedLog| ≤ |Hl|`.
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
abbrev stream.receive.spec : Prop :=
  ∀ (T : Strm) (q : Qp) (rs : List WResp) (r : WResp)
    (resp : go_etcd_io.etcd.server.v3.storage.mvcc.WatchResponse) (W : GMap w64 Reg)
    (Hl : List HRev) (P : w64),
  {{ streamCtx (GF := GF) T ∗ smuBody T rs W Hl P ∗ ghostVar T.σs.rcv (1 : Qp).half rs ∗
      wsRecv T.σs.ws (rs ++ [r]) ∗ wrespIs resp r ∗ mvccReaders T.ep.ι.kv 1 ∗ epLive T.ep q ∗
      histRd T.ep.h T.ep.γh }}
    (App (T.s @!! go.GoType.PointerType stream.ty @!! go!"receive") (Val #resp))
  {{ RET #(); ∃ (Hl' : List HRev) (P' : w64), smuBody T (rs ++ [r]) W Hl' P' ∗
      ghostVar T.σs.rcv (1 : Qp).half (rs ++ [r]) ∗ wsRecv T.σs.ws (rs ++ [r]) ∗
      mvccReaders T.ep.ι.kv 1 ∗ epLive T.ep q ∗ histRd T.ep.h T.ep.γh }}

end spec

end mvccfull
end EtcdGrove
end Perennial
