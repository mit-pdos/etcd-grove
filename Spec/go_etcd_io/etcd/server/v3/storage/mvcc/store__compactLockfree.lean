/-
`store.compactLockfree` (`kvstore.go`) (2026-10-13, unit 5a).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.LockArm

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

/-- `s.compactLockfree(rev)` (`restore()`'s resumed compaction, with `s.mu` held exclusively:
`muInvLag s γ rev cp`, its finished record `cp` lagging the scheduled one `rev`): `updateCompactRev`,
which succeeds (past the finished record, a revision of the committed log), then `compact` (at
`context.TODO()`'s trace), the job scheduled on the compaction right's queue (2026-10-13, unit 5c).
Of a store whose backend supports the compaction (`storeCmp`), at a revision past `0` (the records'
`recsPos`). The compaction revision is already `rev` (`restore()` set it to the scheduled record):
`updateCompactRev`'s ghost step is the identity (`cmpCb_refl`), and its excluder is `s.mu`'s deposit
ghost (`ghostVar γ.wr 1 ()`, lent: the restoring state's; the frozen state's, by the placeholder
`slotF_excl_M1`, `KV.Restore.contract`'s); `KV.Compact.contract`, 2026-11-06: until then the
caller's certificate of a log with revision `rev`, and two error arms the resume never takes. -/
abbrev mvcc.store.compactLockfree.spec : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (rev : w64) (cp : Int) (P : IProp GF) (hk : Option val)
    (Pre Q Post : IProp GF),
  mvcc.storeCmp γ → cp < sint.Z rev → 1 ≤ sint.Z rev →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.muInvLag s γ (sint.Z rev) cp ∗ mvcc.compactRightR s γ (sint.Z rev) ∗
      mvcc.crevPermAt γ (sint.Z rev) ∗
      mvcc.lockCtxM γ P hk Pre Q Post ∗ mvcc.storeRT γ ∗ mvcc.kbWTSupplyM γ.kb ∗ ghostVar γ.wr 1 () ∗
      mvcc.slotFr γ }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"compactLockfree")) (Val #rev))
  {{ (ch : GoChan) (err : GoInterface), RET (PairV #ch #err); mvcc.storeRT γ ∗ mvcc.lockBackM γ P hk ∗
      ghostVar γ.wr 1 () ∗ mvcc.slotFr γ ∗ ⌜err = GoInterface.nil⌝ ∗ mvcc.muInvAt s γ 1 (sint.Z rev) ∗
      mvcc.compactRightR s γ (sint.Z rev) ∗ mvcc.crevLb γ.idx (sint.Z rev) ∗ Post ∗
      mvcc.compactChan ch (mvcc.compactDone s γ (sint.Z rev)) ∗ mvcc.lagTok γ (sint.Z rev) cp }}

end spec

end EtcdGrove
end Perennial
