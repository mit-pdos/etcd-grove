/-
`etcd3.NewCompactor(client, compactInterval, clock, onClose)` (`compact.go`): a compactor
whose loop runs in a goroutine (K2 of `notes/k8s-compactor-plan.md`). Lean-first (no Rocq
counterpart).

At a nonzero interval, a `RealClock` and an `onClose` that is `nil` or returns when called
(`closeOk`; until Q1 (c), 2026-11-05, `nil` only): the compaction loop (`runCompactLoop`) in a
goroutine, with the client's resources and the caller's contract (`casOk`); and, when the feature
gate `ListFromCacheSnapshot` is on (whatever `Enabled` answers: `featureInit`), the watch loop
(`runWatchLoop`) in a second one, with the client's watcher (`clientWatchOk`) and the caller's read
contract (`keyReadOk`). (Until Q1 (b), 2026-11-04, the spec took the gate off, `gateOff`, U3.) The
wait group's `Add(1)`s are `sync.join`'s, which needs no thread token. Returns the compactor
(`isCompactor`) and a lower bound `0` on its revision.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.CompactorDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [sync_sem : sync.Assumptions]

/-- See the file header. -/
abbrev NewCompactor.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (cl : Loc) (ms : List (client.SrvAt GF)) (V : client.WEnv GF) (γk : KVNames)
    (Seen : IProp GF) (recorded : w64 → IProp GF) [Persistent Seen] [∀ c, Persistent (recorded c)]
    (iv : w64) (ck : k8s_io.utils.clock.RealClock) (f : GoFunc),
  (∀ x ∈ ms, kvSame x.γr.kv γk) → γk.cmp = true → γk.cret = 0 → iv ≠ W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isNewClient cl (ms.map client.SrvAt.addr) V ∗
      client.clientWriteOnce cl (ms.map client.SrvAt.addr) ∗ ([∗list] x ∈ ms, client.kvRegsAt x) ∗
      clientKvOk cl γk ∗ clientWatchOk cl γk ∗
      casOk ms γk Seen recorded ∗ keyReadOk γk recorded ∗ closeOk f }}
    (App (App (App (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.NewCompactor)) (Val #cl))
      (Val #iv)) (Val #(interface.mkOk k8s_io.utils.clock.RealClock.ty #ck : GoInterface)))
      (Val #f))
  {{ (c : Loc) (γc : CompactorNames), RET #c; isCompactor c cl γk recorded γc ∗ compactRevLb γc (W64 0) }}

end spec

end k8s
end EtcdGrove
end Perennial
