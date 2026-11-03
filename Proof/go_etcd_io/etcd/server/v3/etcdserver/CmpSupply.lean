/-
**The compaction's closer split** (M2's apply side, `NewServer.specCompact`, 2026-10-31).
Until M2's item 15, stage B3, this file also held the compaction's write-back stock
(`srvCmpStock`, `N` tokens of their own beside the write budget's `N`); since then the
compaction's supply comes from the write budget's stock of the backend (`kbWTSupplyM_of_stock`,
the budget made by `NewServer`), one count for both.
The closer's split (`srvKVCloserW_cmpRight_of_new`): in compaction mode, `NewServer` hands out the
KV's closer without the right (`srvKVCloserW`) and gives the apply thread the compaction right at
`-1`, from the store's closer and its half of the compaction revision's authority (`crevRightM`).

Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvWatchBuilt
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.WsCloserR

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section supply
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The new store's closer, split** (compaction mode): the watchable store's closer and the
compaction revision's half (`mvcc.New`'s `crevRightM`) make the server's closer without the right and
the apply thread's compaction right at `-1` (the storage side's `srvKVCloserM_of_new` and
`srvKVCloserM_split`, at once). -/
theorem srvKVCloserW_cmpRight_of_new (s : Loc) (E : apply.AEnv GF) (h : mvcc.kbCmpM E.γ.kb)
    (hc : E.γ.cm = true) :
    ⊢ srvKVCloser (GF := GF) s E -∗ mvcc.crevRightM E.γ ={⊤}=∗
      srvKVCloserW s E ∗ apply.cmpRight E (-1) := by
  iintro Hcl Hcr
  iunfold srvKVCloser at Hcl
  icases Hcl with ⟨%wsl, #Hkv, Hcl⟩
  imod mvcc.wsCloserR_of_wsCloser wsl E.s E.γ hc ⊤ $$ Hcl Hcr with Hr
  icases (mvcc.wsCloserR_iff wsl E.s E.γ (-1)).1 $$ Hr with ⟨%stc, #Hstc, Hsc, Hw, Hr⟩
  imodintro
  unfold srvKVCloserW apply.cmpRight
  simp only [h, ↓reduceIte]
  iframe Hr
  isplitl [Hsc Hw]
  · iexists wsl
    iframe Hkv
    iexists stc
    iframe Hstc Hsc Hw
  · ipureintro; omega

/-- **The new store's closer by the mode, at `-1`** (`watchableStore.Close`'s, for `NewServer`'s error
returns): off the closer as it is; on, with the compaction revision's half (`crevRightM`). -/
theorem wsCloserM_of_new (s st : Loc) (γ : mvcc.StoreNames) (h : mvcc.kbCmpM γ.kb ↔ γ.cm = true) :
    ⊢ mvcc.wsCloser (GF := GF) s st γ -∗ mvcc.crevRightM γ ={⊤}=∗ mvcc.wsCloserM s st γ (-1) := by
  iintro Hcl Hcr
  by_cases hk : mvcc.kbCmpM γ.kb
  · imod mvcc.wsCloserR_of_wsCloser s st γ (h.1 hk) ⊤ $$ Hcl Hcr with Hr
    imodintro
    iapply (mvcc.wsCloserM_on s st γ (-1) hk).2
    iexact Hr
  · imodintro
    iapply (mvcc.wsCloserM_off s st γ (-1) hk).2
    iexact Hcl

end supply

end EtcdGrove
end Perennial
