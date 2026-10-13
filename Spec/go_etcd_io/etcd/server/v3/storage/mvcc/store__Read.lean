/-
`store__Read` (kvstore_txn.go). Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `s.Read(mode, trace)` opens a read transaction of the committed log at its last revision:
the transaction holds `s.mu` shared and a snapshot of the bucket, both taken under `s.revMu`.
The log read is pinned between the caller's certificate and its revision tokens: it extends
the certificate's log `log₀` (`s.revMu` holds half the committed log's authority), and the
caller's `m` tokens, with the writer's, are among the budget's (`s.revMu` holds half its
authority): `log.length + m + 3 ≤ 2 ^ 63`. (With every token not spent and the certificate of
the last log committed, the log read is that log: the txn package's sole writer.) With `m = 0`
(`ownToks_0`) and `log₀ = []` (`idxCert_nil`), both ghost updates, it is the spec without
them.

**The compaction revision** (2026-10-13, unit 6a): the transaction observes the compaction
revision `crev` (`s.compactMainRev`, read under both locks, `firstRev`; fixed until `End`, since
`Compact` updates it holding `s.mu` exclusively), at or above the caller's lower bound `c` (with
`store.Compact`'s `crevLb` after a compaction at `rev`: `rev ≤ crev`), a revision of `log` (or
`-1`); the reader's tag `Z` (persistent) is carried to `End`. The frozen statement (a store
never compacted, `storeReader`: `crev = -1`) is `specFrozen`, a corollary (`spec_frozen`, `FrozenSpecs.lean`). -/
abbrev mvcc.store.Read.spec : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (mode : w32) (trace : Loc) (m : Nat) (log₀ : mvcc.Log) (c : Int)
    (Z : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.storeReaderC s γ ∗ □ Z ∗ ownToks γ.revs m ∗ mvcc.idxCert γ.idx log₀ ∗
      mvcc.crevLb γ.idx c ∗ ⌜trace ≠ null⌝ }}
    (App (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Read")) (Val #mode)) (Val #trace))
  {{ (mw : Loc), RET #(interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw);
      ∃ (log : mvcc.Log) (rev : w64) (crev : Int), mvcc.isTxnRead mw s γ log rev crev Z ∗
        ownToks γ.revs m ∗ mvcc.crevLb γ.idx crev ∗
        ⌜log₀ <+: log ∧ log.length + m + 3 ≤ 2 ^ 63 ∧ c ≤ crev⌝ }}

end spec

end EtcdGrove
end Perennial
