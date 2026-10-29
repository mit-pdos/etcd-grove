/- Lean-first (no Rocq counterpart).

`Collect(wch, upTo)` (`examples/common/watch.go`; watchkv's `collect` until 2026-10-22, D33, which
linkv3p's repeated): reads a client watch channel of a watch from revision `1` (`isRespChan`, its
responses saying the caller's `Ok`: the clients' model's `watchRespOk`, or the client's Watch
spec's reads of the KV state, `stateOk`; its consumer at position `0`) until an event at `upTo` or
above; with `true`, the events read, in order, each meeting the caller's `F` at its position, the
last at `upTo` or above (none read only at `upTo = 0`).

What a response's events are is the caller's (`Hresp`, from its persistent resources `A`: each
event's `Event`, `evWev`, at its position among those read, and a relation `I` it keeps between
the events read and the consumer's cursor, from `I 0 0`: watchkv's `Cur`, "the `n`-th event at
revision `1 + n`", for a plan of puts; `True` for a watch whose revisions skip), and that its close error, if any, is
one grpc's `status` accepts (`Hce`). General in the events since 2026-10-29 (authkv's root watch
has deletes and keys of no plan, `notes/authkv-main-plan.md`, round 1, F-H3); watchkv's and
linkv3p's plan of puts at revisions `2, 3, ...` is `common.wp_Collect_plan`.
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
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (Ok : RespOk GF) (I : Nat → w64 → Prop)
    (F : Nat → wev → IProp GF) (A : IProp GF) (wch : Loc) (γ : EtcdWatchNames) (upTo : w64),
  I 0 (W64 0) →
  (∀ (c c' : w64) (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel),
    Persistent (Ok c c' v r)) →
  (∀ (c c' : w64) (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel),
    Ok c c' v r ⊢ go_etcd_io.etcd.cache.v3.statusErrOk v.closeErr') →
  (∀ (n : Nat) (c c' : w64) (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel),
    ¬ watchErr v → I n c →
    ⊢ □ A -∗ Ok c c' v r ={⊤}=∗
      ⌜I (n + r.events.length) c'⌝ ∗
      □ ∀ (j : Nat) (e : EvModel), ⌜r.events[j]? = some e⌝ -∗
        ∃ kvv : EtcdKv, kvValAt e.kv kvv ∗ F (n + j) (evWev e kvv.value)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.common ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isRespChan wch γ Ok ∗ etcdWatchConsumer γ 0 (W64 0) ∗ □ A }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.common.Collect)) (Val #wch))
      (Val #upTo))
  {{ (sl : GoSlice) (ok : Bool), RET (PairV #sl #ok);
      ⌜ok = true⌝ -∗ ∃ evs : List wev, sl ↦* evs ∗
        ⌜upTo = W64 0 ∨ ∃ e, evs.getLast? = some e ∧ sint.Z upTo ≤ sint.Z e.Rev'⌝ ∗
        □ ∀ (i : Nat) (e : wev), ⌜evs[i]? = some e⌝ -∗ F i e }}

end spec

end common
end EtcdGrove
end Perennial
