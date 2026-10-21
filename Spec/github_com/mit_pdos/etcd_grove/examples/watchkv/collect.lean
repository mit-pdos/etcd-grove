/- Lean-first (no Rocq counterpart).

`collect(wch, upTo)` (watchkv.go): reads the client watch channel of a prefix watch from revision
`1` (`isEtcdWatchChan` at the server's model, its consumer at position `0`) of a watchkv server
(`γr.kv.wl = workload P`, the plan's keys under the prefix) until an event at `upTo` or above;
with `true` the events read are the puts at revisions `2, 3, ...`, each of a key and value of the
plan (`P`) and the store's put at its revision (`revAt`), at least up to `upTo`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.watchkv.WatchFacts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace watchkv

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver github_com.mit_pdos.etcd_grove.examples.watchkv

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.watchkv.Assumptions]

/-- What `collect` returns with `true`: the events, as the file header says. -/
def collectOk (E : apply.AEnv GF) (P : List (GoString × GoString)) (upTo : w64)
    (evs : List wev) : IProp GF :=
  iprop(⌜(upTo = W64 0 ∨ sint.Z upTo ≤ 1 + evs.length) ∧ evs.length + 1 < 2 ^ 63 ∧
      ∀ (i : Nat) (e : wev), evs[i]? = some e →
        e.put' = true ∧ sint.Z e.rev' = 2 + i ∧ (e.key', e.val') ∈ P⌝ ∗
    □ ∀ (i : Nat) (e : wev), ⌜evs[i]? = some e⌝ -∗ revAt E (2 + i) e.key' e.val')

/-- See the file header. -/
abbrev collect.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (E : apply.AEnv GF) (γr : ReadNames) (P : List (GoString × GoString)) (wch : Loc)
    (γ : EtcdWatchNames) (upTo : w64),
  γr.kv.wl = workload P → γr.kv.log0 = [[], []] → (∀ kv ∈ P, wkPfx <+: kv.1) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.watchkv ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isEtcdWatchChan (EM := v3rpc.etcdModelOfServer E) wch γ wkPfx ∗
      etcdWatchConsumer γ 0 (W64 0) ∗ srvKVInvs E γr ∗ mvcc.idxCert E.γ.idx [[], []] }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.watchkv.collect)) (Val #wch))
      (Val #upTo))
  {{ (sl : GoSlice) (ok : Bool), RET (PairV #sl #ok);
      ⌜ok = true⌝ -∗ ∃ evs : List wev, sl ↦* evs ∗ collectOk E P upTo evs }}

end spec

end watchkv
end EtcdGrove
end Perennial
