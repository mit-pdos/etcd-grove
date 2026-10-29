/-
`store.checkPrevCompactionCompleted` (`kvstore.go`) (2026-10-13, unit 5a).
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

/-- `s.checkPrevCompactionCompleted()`: some boolean (the meta keys read through a `ReadTx`
with no view, `metaReadTx`; racy with the job, which writes `finishedCompactRev`: the result only
decides whether the next compaction's hash is stored, which the model ignores). Of a store whose
backend supports the compaction (`storeCmp`: the real backend's model promises nothing of the
`Meta` bucket, its hook's). The store's fields for its compaction (`storeStop`; D22 receiver epochs,
S3: until then `isStore`'s `↦□`). Its `ReadTx`'s `RLock` takes the reader's token `storeRT γ` and
its `RUnlock` gives it back (question 5's switch, decision (i), 2026-10-29: the caller lends it,
`store.Compact`'s from the apply thread's `writerOwn`). -/
abbrev mvcc.store.checkPrevCompactionCompleted.spec : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames),
  mvcc.storeCmp γ →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.isStore s γ ∗
      mvcc.storeStop s γ ∗ mvcc.storeRT γ }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"checkPrevCompactionCompleted")) (Val #()))
  {{ (b : Bool), RET #b; mvcc.storeRT γ }}

end spec

end EtcdGrove
end Perennial
