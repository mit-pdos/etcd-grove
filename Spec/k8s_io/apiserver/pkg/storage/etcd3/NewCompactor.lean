/-
`etcd3.NewCompactor(client, compactInterval, clock, onClose)` (`compact.go`): a compactor
whose loop runs in a goroutine (K2 of `notes/k8s-compactor-plan.md`). Lean-first (no Rocq
counterpart).

At a nonzero interval, a `RealClock`, no `onClose`, and `ListFromCacheSnapshot` off
(`gateOff`, U3: no watch loop; a scope restriction, retired by Q1 (b)): one goroutine, the loop
(`runCompactLoop`; the wait group's one `Add(1)` is `sync.join`'s, which needs no thread token), with the
client's resources and the caller's contract (`casOk`). Returns the compactor (`isCompactor`)
and a lower bound `0` on its revision.
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
variable [sync_sem : sync.Assumptions]

/-- See the file header. -/
abbrev NewCompactor.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (cl : Loc) (ms : List (client.SrvAt GF)) (V : client.WEnv GF) (γk : KVNames)
    (Seen : IProp GF) (recorded : w64 → IProp GF) [Persistent Seen] [∀ c, Persistent (recorded c)]
    (iv : w64) (ck : k8s_io.utils.clock.RealClock),
  (∀ x ∈ ms, kvSame x.γr.kv γk) → γk.cmp = true → γk.cret = 0 → iv ≠ W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ gateOff ∗
      isNewClient cl (ms.map client.SrvAt.addr) V ∗
      client.clientWriteOnce cl (ms.map client.SrvAt.addr) ∗ ([∗list] x ∈ ms, client.kvRegsAt x) ∗
      clientKvOk cl γk ∗
      casOk ms γk Seen recorded }}
    (App (App (App (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.NewCompactor)) (Val #cl))
      (Val #iv)) (Val #(interface.mkOk k8s_io.utils.clock.RealClock.ty #ck : GoInterface)))
      (Val #func.nil))
  {{ (c : Loc) (γc : CompactorNames), RET #c; isCompactor c cl γk recorded γc ∗ compactRevLb γc (W64 0) }}

end spec

end k8s
end EtcdGrove
end Perennial
