/-
`store.Close` (`kvstore.go`): the trust boundary (untranslated). Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvCompact

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

/-- `s.Close()` of the store, with the right to close it once (`storeCloser`: its `stopc` field's
close, the scheduler's stop token and the compaction jobs' queue; `Close` closes `s.stopc` and
stops the store's scheduler, `fifoSched.Stop()`, with the token and the queue, as
`Scheduler.Stop`'s spec takes them: no `Schedule` follows, which would panic; a second call would
close `stopc` again, a panic): returns `nil`. D19m (C), 2026-10-18: until then without the stop
token, which `NewStore` gave up for good (`isStore` held `schedLive`), so a holder of `isStore`
could compact after `Close`, where Go's `Schedule` panics. (M2, the storage side, the approval's
item 23) The right to close by the mode at the store's compaction revision `c` (`storeCloserM`:
off, `storeCloser`; on, the restorable compaction right `compactRightR`, whose queue is at `c`, not
`-1`: `storeCloser`'s queue is at `-1`, which a store that compacted cannot give,
`compactQueue_mono` only going up). Unreachable today (the server's `run` never returns, so
`Cleanup` never closes the KV): what a modelled shutdown takes. -/
abbrev mvcc.store.Close.spec : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (c : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.storeCloserM s γ c }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Close")) (Val #()))
  {{ RET #(GoInterface.nil); True }}

end spec

end EtcdGrove
end Perennial
