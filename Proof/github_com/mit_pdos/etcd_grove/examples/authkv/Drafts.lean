/-
**Draft statements of `Main`'s remaining callees** (`notes/authkv-main-plan.md`, "Main's
callees, draft"; 2026-10-29). Lean-first (no Rocq counterpart).

These are for review round 2, written here so that they typecheck; no proof uses them. When frozen,
each goes where it belongs (`common.Collect.spec` restated in its `Spec` file, the laws to
`Hist.lean`) and this file goes away.

- **`Collect`, general in the events** (round 1, F-H3). Today's `common.Collect.spec` requires every
  event to be a put at revision `2+n+j` of a key and value of a plan (watchkv's, linkv3p's). Root's
  history has deletes, and keys from no plan. The draft takes the caller's per-event fact instead
  (`F`, at the event's position among those read). The post gives it for each collected event,
  and with `true` the last one at or above `upTo`, which is `Collect`'s test. Today's spec is
  derivable: `F i e := ⌜e.Put' ∧ sint.Z e.Rev' = 2 + i ∧ (e.Key', e.Val') ∈ P⌝ ∗ R (2 + i) e.Key'
  e.Val'`, so the plan's `collectOk` follows. Its callers (watchkv, linkv3p) would go through that
  corollary.
- **From the invariant to `CheckHistory`'s premise** (`histOk_of_keyHistOk`, proved): the
  collected events above `setupRev` on admitted keys are what `histOk` asks.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.common.RespChan
public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.Hist

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv
namespace draft

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver github_com.mit_pdos.etcd_grove.examples.common
  common

section pure
variable [GooseExts]

/-- **The history's check from the invariant's keys**: `histOk` asks of the events above
`setupRev` that are not `endKey`'s exactly that their key's principal was permitted, which
`keyHistOk` says. -/
theorem histOk_of_keyHistOk (evs : List wev) (setupRev : w64)
    (h : ∀ e ∈ evs, sint.Z setupRev < sint.Z e.Rev' → keyHistOk e.Key') :
    histOk evs setupRev endKey := by
  intro e he hr hne
  rcases h e he hr with h | h
  · exact h
  · exact absurd h hne

end pure

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.common.Assumptions]

/-- The `Event` `Collect` appends for the event `e` whose key-value's value is `v`. -/
def evWev (e : EvModel) (v : GoString) : wev :=
  { Rev' := e.rev, Key' := e.key, Val' := v, Put' := decide (e.typ = W32 0) }

/-- **`Collect(wch, upTo)`, general in the events** (draft of `common.Collect.spec`, see the file
header): the caller says, from its persistent resources `A`, what each event of a response is
(`Hresp`: at its position `n + j` among the events read, `F` of the `Event` it becomes). With
`true` the events read are in order, each meeting `F` at its position, and the last at `upTo` or
above (or none read, `upTo = 0`). -/
abbrev Collect_spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (Ok : RespOk GF) (F : Nat → wev → IProp GF)
    (A : IProp GF) (wch : Loc) (γ : EtcdWatchNames) (upTo : w64),
  (∀ (c c' : w64) (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel),
    Persistent (Ok c c' v r)) →
  (∀ i e, Persistent (F i e)) →
  (∀ (c c' : w64) (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel),
    Ok c c' v r ⊢ go_etcd_io.etcd.cache.v3.statusErrOk v.closeErr') →
  (∀ (n : Nat) (c c' : w64) (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel),
    ¬ watchErr v → Cur n c →
    ⊢ □ A -∗ Ok c c' v r ={⊤}=∗
      ⌜Cur (n + r.events.length) c'⌝ ∗
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

end draft
end authkv
end EtcdGrove
end Perennial
