/-
`(*compactor).runCompactLoop(stopCh)` (`compact.go`): the compactor's loop (K2 of
`notes/k8s-compactor-plan.md`). Lean-first (no Rocq counterpart).

Until `stopCh` (the compactor's `stop`, a broadcast channel only closed) closes: wait
`interval` on the clock, run a round (`Compact`) from the previous round's `(cv, cr)` (from
`(0, 0)`), and on a reported revision raise the compactor's (`UpdateCompactRevision`).

**The guarantee (Q3 of the plan, in rounds):** every `client.Compact` the loop issues is at a
recorded, reached, positive revision `r` (`Compact`'s post, `casOk`), and `r` is the header
revision of its previous round, one `clock.After(interval)` earlier: at least one interval of
history before a compaction. The logic has no time: the interval is the code's structure (one
`After` between rounds), checked by the Go test. The client's resources stay with the loop.
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
abbrev compactor.runCompactLoop.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (c cl : Loc) (ms : List (client.SrvAt GF)) (V : client.WEnv GF) (γk : KVNames)
    (Seen : IProp GF) (recorded : w64 → IProp GF) [Persistent Seen] [∀ c, Persistent (recorded c)]
    (γc : CompactorNames) (sc : GoChan) (γs : ChanNames),
  (∀ x ∈ ms, kvSame x.γr.kv γk) → γk.cmp = true → γk.cret = 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isCompactor c cl γk recorded γc ∗ compactorStopOk c sc γs ∗
      isNewClient cl (ms.map client.SrvAt.addr) V ∗
      client.clientWriteOnce cl (ms.map client.SrvAt.addr) ∗ ([∗list] x ∈ ms, client.kvRegsAt x) ∗
      casOk ms γk Seen recorded }}
    (App (Val (c @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.compactor.ty @!!
      go!"runCompactLoop")) (Val #sc))
  {{ RET #(); True }}

end spec

end k8s
end EtcdGrove
end Perennial
