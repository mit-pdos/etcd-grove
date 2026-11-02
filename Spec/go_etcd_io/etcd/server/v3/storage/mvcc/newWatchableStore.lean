/-
`newWatchableStore` (`watchable_store.go`). Lean-first (no Rocq counterpart); see `InvWatchSync.lean`, `Spec/.../NewStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchSync
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RdCode

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

/-- **`newWatchableStore` at the mode `aq`** (mvcc's candidate API, `notes/mvcc-api-proof-plan.md`):
the store in the abstract mode when `aq`: its range deleter's code
(`rdCode`, the deleter's contract is over the store's pools, made later) and `NewStore.spec`'s
abstract parts. -/
abbrev mvcc.newWatchableStore.spec : Prop :=
  ∀ (lg : Loc) (b le : GoInterface) (cfg : StoreConfig) (kb : Option mvcc.KBReal) (γb γl : GName)
    (P : IProp GF) (f : val) (rd0 : GoFunc) (γi : mvcc.IdxNames) (γok γtag : GName) (aq : Bool),
  mvcc.batchLimitOk cfg.CompactionBatchLimit' → receiptBound GF ≤ 2 ^ 48 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      (∀ (s : Loc) (γ : mvcc.StoreNames), ⌜γ.bucket = γb ∧ γ.kb = kb ∧ γ.idx = γi⌝ →
        mvcc.storeBackend b s γ P) ∗
      mvcc.kbView kb γb 1 (∅ : mvcc.Bucket) ∗ mvcc.kbNoCmp kb γb ∗ mvcc.kbRegRight kb ∗ mvcc.kbWT kb ∗ mvcc.kbWT kb ∗
      mvcc.kbSRM kb ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), mvcc.kbRT kb) ∗
      lease.lessorRdOf γl ∗ mvcc.isLessor le γl ∗ lease.rdOwn γl rd0 ∗
      mvcc.idxFresh γi ∗ ghostMapAuth γok 1 (∅ : GMap w64 mvcc.Log) }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.newWatchableStore)) (Val #lg))
      (Val #b)) (Val #le)) (Val #cfg))
  {{ (s : Loc), RET #s; ∃ (st : Loc) (γ : mvcc.WsNames), ⌜γ.st.bucket = γb ∧ γ.st.leases = γl ∧ γ.st.kb = kb ∧
        γ.st.idx = γi ∧ γ.st.cok = γok ∧ γ.tag = γtag ∧ γ.st.cm = decide (mvcc.kbCmpM kb) ∧
        γ.st.absQ = aq⌝ ∗
      mvcc.isWatchableStore s st γ ∗ (∃ rd : GoFunc, lease.rdOwn γl rd ∗
        (if aq then mvcc.rdCode rd s else mvcc.rdIs rd s st γ)) ∗ mvcc.hookInit γ.st P f ∗ mvcc.watchWriter γ [[], []] ∗
      mvcc.watchToks γ (2 ^ 63 - 3) ∗ ghostMapAuth γ.st.cok 1 (∅ : GMap w64 mvcc.Log) ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - mvcc.nJobRd kb) (),
        mvcc.watchReader s st γ) ∗
      (∃ stc : Loc, s.[watchableStore, go!"stopc"] ↦□ stc ∗ mvcc.stopCloser stc) ∗
      mvcc.storeCloser st γ.st ∗ mvcc.crevRightM γ.st ∗
      (if aq then iprop(mvcc.writerFragA γ.st ∗ ghostVar γ.st.abs (1 : Qp).half ([[], []] : mvcc.Log) ∗
          ghostVar γ.st.pnd (1 : Qp).half (none : Option (List mvcc.Change)))
       else mvcc.writerFrag γ.st) ∗ mvcc.retiredAt γ.st (mvcc.nJobRd kb) ∗
      typedPointsto (mvcc.wsWgAddr s) (zero_val sync.WaitGroup) (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
