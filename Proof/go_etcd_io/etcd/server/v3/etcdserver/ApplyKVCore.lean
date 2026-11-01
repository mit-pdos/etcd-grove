/-
**The apply thread's applier row without its auth part** (the auth plan's E3p, 2026-10-27;
`notes/decisions.md`, "E3p of the auth plan"): `srvApplyKVCore`, what the mode-off row
`srvApplyKV` and the mode-`on` row `srvApplyKVOn` share (the uber-applier at the field, its
applier facts, the KV writer, the backend's ownership, the minted revisions and the wait), the
footprint of `EtcdServer.snapshot`'s contract, which touches no auth store. `srvApplyKV_core`: the
mode-off row lends it (the mode-`on` row's, `srvApplyKVOn_core`, is in `ApplyNormalOn.lean`).

Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section core
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The applier row's part shared by both auth modes** at the uber-applier `ua` (`srvApplyKV`'s
without the auth store's apply-side resource). -/
def srvApplyKVCore (s : Loc) (E : apply.AEnv GF) (γw : GName) (x : apply.ApplyKV)
    (ua : GoInterface) : IProp GF :=
  iprop(srvUberApplyAddr s ↦ ua ∗ apply.applierFor ua E ∗ apply.applyKV E ua x ∗ srvBeOwn s E ∗
    revAuth E x.log ∗
    ∃ (w : GoInterface) (RD : IProp GF), srvWAddr s ↦□ w ∗
      waitOk w RD (fun ot id => waitRegdOpt γw id ot) (fun ot id => waitGoneOpt γw id ot) ∗ RD)

/-- The mode-off row lends its shared part. -/
theorem srvApplyKV_core (s : Loc) (E : apply.AEnv GF) (γw : GName) (x : apply.ApplyKV) :
    srvApplyKV (GF := GF) s E γw x ⊢
      ∃ ua, srvApplyKVCore s E γw x ua ∗ (srvApplyKVCore s E γw x ua -∗ srvApplyKV s E γw x) := by
  iintro H
  iunfold srvApplyKV at H
  icases H with ⟨%ua, Hua, #Hap, Hkv, Hbo, Hra, Har, Hw⟩
  iexists ua
  isplitl [Hua Hkv Hbo Hra Hw]
  · iunfold srvApplyKVCore
    isplitl [Hua]
    · iexact Hua
    isplitr
    · iexact Hap
    isplitl [Hkv]
    · iexact Hkv
    isplitl [Hbo]
    · iexact Hbo
    isplitl [Hra]
    · iexact Hra
    iexact Hw
  iintro Hc
  iunfold srvApplyKVCore at Hc
  icases Hc with ⟨Hua, -, Hkv, Hbo, Hra, Hw⟩
  iunfold srvApplyKV
  iexists ua
  isplitl [Hua]
  · iexact Hua
  isplitr
  · iexact Hap
  isplitl [Hkv]
  · iexact Hkv
  isplitl [Hbo]
  · iexact Hbo
  isplitl [Hra]
  · iexact Hra
  isplitl [Har]
  · iexact Har
  iexact Hw


/-- (2026-10-31, the snapshot track: #11's S6) **`s.KV().Commit()`'s resources, lent by the
shared row**: the store writer's fragment and its reader token of the backend (`txn.kvWriter`'s
and `apply.kvOwn`'s), and a write token from the budget for the commit's write-back
(`srvWTPool_take_extra`, for a receipt), given back after the commit. -/
theorem srvApplyKVCore_commit [go_etcd_io.etcd.server.v3.etcdserver.Assumptions] (s : Loc) (E : apply.AEnv GF) (γw : GName) (x : apply.ApplyKV)
    (ua : GoInterface) (γp : GName) :
    ⊢ srvWTPool (GF := GF) E γp -∗ ⧗ 1 -∗ srvApplyKVCore s E γw x ua ={⊤}=∗
      mvcc.writerFrag E.γ ∗ mvcc.writerOwn E.γ ∗ mvcc.storeWT E.γ ∗
      (mvcc.writerFrag E.γ ∗ mvcc.writerOwn E.γ -∗ srvApplyKVCore s E γw x ua) := by
  iintro #Hp Hr Hc
  iunfold srvApplyKVCore at Hc
  icases Hc with ⟨Hua, #Hap, Hkv, Hbo, Hra, Hw⟩
  imod srvWTPool_take_extra s E γp $$ Hp Hr Hbo with ⟨Hwt, Hbo⟩
  iunfold apply.applyKV at Hkv
  icases Hkv with ⟨%p, %Hpe, Huo, Hko, Hcmp⟩
  iunfold apply.kvOwn at Hko
  icases Hko with ⟨Hsr, Hkw, Hll, Hrd, Hwo⟩
  iunfold txn.kvWriter at Hkw
  icases Hkw with ⟨Hsw, Hwl, Hwf⟩
  imodintro
  iframe Hwf Hwo Hwt
  iintro ⟨Hwf, Hwo⟩
  ihave Hkv : apply.applyKV E ua x $$ [Huo Hsr Hsw Hwl Hwf Hll Hrd Hwo Hcmp]
  · iunfold apply.applyKV
    iexists p
    isplitr
    · ipureintro; exact Hpe
    iframe Huo Hcmp
    iunfold apply.kvOwn
    iframe Hsr Hll Hrd Hwo
    iunfold txn.kvWriter
    iframe Hsw Hwl Hwf
  iunfold srvApplyKVCore
  isplitl [Hua]
  · iexact Hua
  isplitr
  · iexact Hap
  isplitl [Hkv]
  · iexact Hkv
  isplitl [Hbo]
  · iexact Hbo
  isplitl [Hra]
  · iexact Hra
  iexact Hw

end core

end EtcdGrove
end Perennial
