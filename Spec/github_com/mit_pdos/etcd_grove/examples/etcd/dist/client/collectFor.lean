/-
`collectFor(wch, cancel, upTo)` (`examples/etcd/dist/client/auth.go`): `etcdstart.Collect(wch, upTo)` under a
timer that calls `cancel` after `readTimeout` (an end, not a check), then the timer stopped and `cancel` called.
Lean-first (no Rocq counterpart); F7 stage S6 (`notes/etcd-dist-f7.md`, "Handoff RA-2").

**The triple**: `Collect.spec`'s, at the same channel predicate, invariant and per-event fact, given that
`cancel` may be called (any number of times, from any thread) and returns without panicking.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Collect

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Net client go_etcd_io.etcd.server.v3.etcdserver
open github_com.mit_pdos.etcd_grove.examples.etcd.dist
open etcdstart

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]

/-- See the file header. -/
abbrev collectFor.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (Ok : RespOk GF) (I : Nat → w64 → Prop)
    (F : Nat → wev → IProp GF) (A : IProp GF) (wch : Loc) (γ : EtcdWatchNames) (cancel : GoFunc)
    (upTo c0 : w64),
  I 0 c0 →
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
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      isRespChan wch γ Ok ∗ etcdWatchConsumer γ 0 c0 ∗ □ A ∗
      □ (∀ Ψ : val → IProp GF, ▷ Ψ #() -∗ WP (App (Val #cancel) (Val #())) {{ Ψ }}) }}
    (App (App (App (Val (@! client.collectFor)) (Val #wch)) (Val #cancel)) (Val #upTo))
  {{ (sl : GoSlice) (ok : Bool), RET (PairV #sl #ok);
      ⌜ok = true⌝ -∗ ∃ evs : List wev, sl ↦* evs ∗
        ⌜upTo = W64 0 ∨ ∃ e, evs.getLast? = some e ∧ sint.Z upTo ≤ sint.Z e.Rev'⌝ ∗
        □ ∀ (i : Nat) (e : wev), ⌜evs[i]? = some e⌝ -∗ F i e }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
