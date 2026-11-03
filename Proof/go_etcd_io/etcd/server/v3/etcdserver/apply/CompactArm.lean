/-
**The apply package's compaction arm: the glue** (M2, the apply side, the switch; drafted in
`M2ApplyDraft.lean`, `notes/m2-apply-plan.md`). Lean-first (no Rocq counterpart). The vocabulary
(`chainCompacts`, `cmpRevAfter`, `cmpAdmitRev`, `cmpOwn`, `cmpAnswerIs`, the chain's `cmpTriple`) is
`Chain.lean`'s; here `cmp_store_pre`: the backend's `Compaction` meets `store.Compact.spec`'s
precondition from the apply thread's KV and compaction resources.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Chain
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvCompact
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Compact
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.LockArm

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

namespace apply

/-! ## `store.Compact`'s precondition from the backend's -/

section glue
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **The backend's `Compaction` meets `store.Compact.spec`'s precondition** (the glue of
`applierV3backend.Compaction.specD` over `mvcc_store_Compact`, the resource part): from the apply
thread's KV (`kvOwn`), its compaction resources (`cmpOwn`, on) and the options' hook fact
(`backendOptsOk`'s `hookOk`), the store's restorable right at `crev` (at least `-1`), the KV's
certificate of its log, the writer's hook (`hookIs`: the hook's facts and the writer's fragment,
from `txn.kvWriter`), the store's reader token (lent by `writerOwn`), the supply; and back, at the
compaction revision `store.Compact` leaves (any `c'` at least `-1`). -/
theorem cmp_store_pre (E : AEnv GF) (log : mvcc.Log) (crev : Int) (h : mvcc.kbCmpM E.γ.kb) :
    kvOwn E log ∗ cmpOwn E crev ∗ mvcc.hookOk E.γ E.P E.f ⊢
      mvcc.compactRightR E.s E.γ crev ∗ ⌜-1 ≤ crev⌝ ∗ mvcc.idxCert E.γ.idx log ∗
      mvcc.hookIs E.γ E.P E.f ∗ mvcc.storeRT E.γ ∗ mvcc.kbWTSupplyM E.γ.kb ∗
      (∀ c' : Int, mvcc.compactRightR E.s E.γ c' -∗ ⌜-1 ≤ c'⌝ -∗ mvcc.hookIs E.γ E.P E.f -∗
        mvcc.storeRT E.γ -∗ kvOwn E log ∗ cmpOwn E c') := by
  iintro ⟨Hkv, Hc, #Hhk⟩
  ihave ⟨Hkv, #Hcert⟩ := kvOwn_cert E log $$ Hkv
  iunfold kvOwn at Hkv
  icases Hkv with ⟨Hsr, Hw, Hll, Hrd, Hwo⟩
  iunfold txn.kvWriter at Hw
  icases Hw with ⟨Hsw, Hwl, Hfr⟩
  ihave ⟨Hrt, Hwob⟩ := mvcc.writerOwn_rt E.γ $$ Hwo
  iunfold cmpOwn at Hc
  icases Hc with ⟨Hr, #Hsup⟩
  iunfold cmpRight at Hr
  simp only [h, ↓reduceIte]
  icases Hr with ⟨Hr, %hge⟩
  iframe Hr Hcert Hrt Hsup
  isplitr
  · ipureintro; exact hge
  isplitl [Hfr]
  · iunfold mvcc.hookIs; iframe Hhk Hfr
  iintro %c' Hr' %hc' Hhi Hrt'
  iunfold mvcc.hookIs at Hhi
  icases Hhi with ⟨-, Hfr'⟩
  ihave Hwo := Hwob $$ Hrt'
  isplitl [Hsr Hsw Hwl Hfr' Hll Hrd Hwo]
  · iunfold kvOwn
    iframe Hsr Hll Hrd Hwo
    iunfold txn.kvWriter
    iframe Hsw Hwl Hfr'
  iunfold cmpOwn
  iframe Hsup
  iunfold cmpRight
  simp only [h, ↓reduceIte]
  iframe Hr'
  ipureintro; exact hc'

end glue

end apply

end EtcdGrove
end Perennial
