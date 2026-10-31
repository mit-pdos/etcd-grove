/-
**The apply package's compaction arm: the vocabulary** (M2, the apply side, the switch; drafted in
`M2ApplyDraft.lean`, `notes/m2-apply-plan.md`). Lean-first (no Rocq counterpart).

- `chainCompacts` (the chains whose `Compaction` reaches the backend), `cmpRevAfter` (the store's
  `updateCompactRev`), `cmpAdmitRev` (what a compaction at a revision needs).
- The apply thread's compaction resources `cmpOwn E c` (`cmpRight` by the store's mode, and the
  write-back supply), and `cmp_store_pre`: the backend's `Compaction` meets `store.Compact.spec`'s
  precondition from them.
- The answer of a chain's `Compaction` (`cmpAnswerIs`, `cmpRespOk`).
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

/-! ## The pure part -/

/-- **The chains whose `Compaction` reaches the backend**: the auth, quota and capped wrappers pass
it on (they do not override it), the corrupt applier answers `ErrCorrupt` (`corrupt.go`). -/
def chainCompacts : Chain → Bool
  | .backend => true
  | .auth _ c => chainCompacts c
  | .quota c => chainCompacts c
  | .capped c => chainCompacts c
  | .corrupt _ => false

/-- **The compaction revision after `Compact(rev)`** at `crev` (`updateCompactRev`): `rev` when
above, else unchanged (`ErrCompacted`). -/
def cmpRevAfter (crev : Int) (rev : w64) : Int :=
  if crev < sint.Z rev then sint.Z rev else crev

theorem cmpRevAfter_ge (crev : Int) (rev : w64) : crev ≤ cmpRevAfter crev rev := by
  unfold cmpRevAfter; split <;> omega

/-- **What a compaction at `rev` needs at the log `log`** (pure; written once, review round 1's
S-8): the store compacting (its backend in compaction mode: the KV invariant admits compaction
entries only in the cluster's compaction mode, and `envAgree`/`srvEnvOkD` tie the store's mode to
it) and the revision one of the log's (the committed log's claim, `cmpLogOk`). No `NoDelPutAt`:
the fork has etcd-io/etcd#22377 (review round 1's F-5; mvcc's specs drop the premise before the
switch). -/
def cmpAdmitRev (kb : Option mvcc.KBReal) (log : mvcc.Log) (rev : w64) : Prop :=
  mvcc.kbCmpM kb ∧ sint.Z rev < log.length

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-! ## The apply thread's compaction resources -/

/-- **The store's compaction right at `c`, by the mode**: a compacting store's restorable right
(`mvcc.compactRightR`: half the compaction revision's authority, the jobs' queue, the closer's and
the jobs' shares of the fields), at least `-1`; a store that does not compact, none, at `-1`. -/
def cmpRight (E : AEnv GF) (c : Int) : IProp GF :=
  if mvcc.kbCmpM E.γ.kb then iprop(mvcc.compactRightR E.s E.γ c ∗ ⌜-1 ≤ c⌝) else iprop(⌜c = -1⌝)

/-- **The apply thread's compaction resources at `c`**: the right by the mode and the compaction's
write-back supply (persistent; `True` off). -/
def cmpOwn (E : AEnv GF) (c : Int) : IProp GF :=
  iprop(cmpRight E c ∗ mvcc.kbWTSupplyM E.γ.kb)

theorem cmpOwn_off (E : AEnv GF) (c : Int) (h : ¬ mvcc.kbCmpM E.γ.kb) :
    cmpOwn (GF := GF) E c ⊢ ⌜c = -1⌝ := by
  unfold cmpOwn cmpRight
  simp only [h, ↓reduceIte]
  iintro ⟨%hc, -⟩
  ipureintro; exact hc

theorem cmpOwn_ge (E : AEnv GF) (c : Int) : cmpOwn (GF := GF) E c ⊢ ⌜-1 ≤ c⌝ := by
  unfold cmpOwn cmpRight
  split
  · iintro ⟨⟨-, %h⟩, -⟩; ipureintro; exact h
  · iintro ⟨%h, -⟩; ipureintro; omega

/-! ## The answers -/

/-- **A successful compaction's response** `rp` (owned: `EtcdServer.Compact` writes it): its
header, owned (`Compaction`'s last lines, `rr.Rev` of `KV.Range(context.TODO(), "compaction", …)`).
(2026-10-31, the switch: the draft's header revision `|log| - 1` dropped: no caller reads it,
`compactResultIs` only owns the header, and `readView.Range` takes no lower bound of the log it
reads, so the revision is that of some certified log, not provably the apply thread's.) -/
def cmpRespOk (rp : Loc) : IProp GF :=
  iprop(⌜rp ≠ null⌝ ∗ ∃ cv : etcdserverpb.CompactionResponse, rp ↦ cv ∗
    ∃ hv : etcdserverpb.ResponseHeader, cv.Header' ↦ hv)

/-- **The answer of the chain `c`'s `Compaction(rev)`** at the compaction revision
`crev`: through a chain that reaches the backend, a response at the current revision with its trace
(`rev` above `crev`), or `ErrCompacted` with no response and no trace (`rev` at or below `crev`); the
corrupt applier's `ErrCorrupt`. The channel (`Physc`) is not stated: the request path reads it only
of a physical compaction, which the proposers never send (`compactReqIs`). -/
def cmpAnswerIs (c : Chain) (crev : Int) (rev : w64) (resp : Loc) (ch : GoChan)
    (trace : Loc) (err : GoInterface) : IProp GF :=
  if chainCompacts c then
    iprop((⌜crev < sint.Z rev ∧ err = GoInterface.nil⌝ ∗ cmpRespOk resp ∗ traceRes trace) ∨
      (⌜sint.Z rev ≤ crev ∧ resp = null ∧ trace = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err))
  else
    iprop(⌜resp = null ∧ ch = chan.nil ∧ trace = null⌝ ∗
      txn.errVarIs go_etcd_io.etcd.server.v3.etcdserver.errors.ErrCorrupt err)

end defs

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
