/-
`resyncDelay` (`watchable_store.go`; etcd-io/etcd#22297, in the fork since D19l). Lean-first (no
Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchSync

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `resyncDelay(d, last, now)`: `d` when the last sync pass made progress with watchers left
unsynced (`now ≠ 0`, `last > now`) and `d` is positive, else the package variable
`watchResyncPeriod` (100 ms). Positive either way: what `syncWatchersLoop`'s `Ticker.Reset`
needs, for any `d` (`time.Since` may answer `0` on a coarse clock,
`issues/etcd-watch-sync-ticker-reset-zero.md`). -/
abbrev mvcc.resyncDelay.spec : Prop :=
  ∀ (d : w64) (last now : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.resyncDelay)) (Val #d))
      (Val #last)) (Val #now))
  {{ (r : w64), RET #r;
      ⌜r = (if now ≠ W64 0 ∧ sint.Z now < sint.Z last ∧ 0 < sint.Z d then d
            else W64 100000000) ∧ 0 < sint.Z r⌝ }}

end spec

end EtcdGrove
end Perennial
