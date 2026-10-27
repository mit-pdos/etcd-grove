/- Lean-first (no Rocq counterpart).

`Collect(wch, upTo)` (`examples/common/watch.go`; watchkv's `collect` until 2026-10-22, D33, which
linkv3p's repeated): reads a client watch channel of a prefix watch from revision `1`
(`isRespChan`, its responses saying the caller's `Ok`: the clients' model's `watchRespOk`, or the
client's Watch spec's reads of the KV state, `stateOk`; its consumer at position `0`) until an
event at `upTo` or above; with `true` the events read are the puts at revisions `2, 3, ...`, each of a key and value
of the plan `P` and the put `R` has at its revision, at least up to `upTo` (`collectOk`).

What a response's events are is the caller's (`Hresp`, from its persistent resources `A`), and that
its close error, if any, is one grpc's `status` accepts (`Hce`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.common.RespChan

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace common

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver github_com.mit_pdos.etcd_grove.examples.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.common.Assumptions]

/-- See the file header. -/
abbrev Collect.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (Ok : RespOk GF)
    (R : Nat → GoString → GoString → IProp GF) (A : IProp GF) (P : List (GoString × GoString))
    (wch : Loc) (γ : EtcdWatchNames) (upTo : w64),
  (∀ (c c' : w64) (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel),
    Persistent (Ok c c' v r)) →
  (∀ (c c' : w64) (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel),
    Ok c c' v r ⊢ go_etcd_io.etcd.cache.v3.statusErrOk v.closeErr') →
  (∀ (n : Nat) (c c' : w64) (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel),
    ¬ watchErr v → Cur n c →
    ⊢ □ A -∗ Ok c c' v r ={⊤}=∗
      ⌜Cur (n + r.events.length) c'⌝ ∗
      □ ∀ (j : Nat) (e : EvModel), ⌜r.events[j]? = some e⌝ -∗ evFactR R P (2 + n + j) e) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.common ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isRespChan wch γ Ok ∗ etcdWatchConsumer γ 0 (W64 0) ∗ □ A }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.common.Collect)) (Val #wch))
      (Val #upTo))
  {{ (sl : GoSlice) (ok : Bool), RET (PairV #sl #ok);
      ⌜ok = true⌝ -∗ ∃ evs : List wev, sl ↦* evs ∗ collectOk R P upTo evs }}

end spec

end common
end EtcdGrove
end Perennial
