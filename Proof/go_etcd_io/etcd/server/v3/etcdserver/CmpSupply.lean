/-
**The compaction's write-back supply** (M2's apply side, `NewServer.specCompact`, 2026-10-31):
`store.Compact` takes `mvcc.kbWTSupplyM` of the store's backend (persistent: a scheduled
compaction's job writes back later), which the server's write budget (`srvWTPool`, made by `start`)
cannot give before `start`, nor for good across a backend swap. In compaction mode the backend is
never swapped (a snapshot is installed only with the mode off, the interim restriction), so
`NewServer` sets the backend's extra write-back tokens aside in a stock of their own (`srvCmpStock`):
the write budget's pattern (a receipt in for a token out, `receiptBound ≤ a + n + 1`), its own
receipts. (The storage side's draft, `srvWTStockInv`, shares the pool's receipt counter so that one
stock per backend serves after a swap: what restore in compaction mode needs, the collaborator's.)
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

/-- The compaction stock's invariant's name. -/
def srvCmpStockN : Namespace := nroot .@ "srvCmpStock"

/-- **The backend `d`'s write-back tokens for compactions** (persistent): `n` tokens of `d` and the
`a` receipts paid for the ones taken, with `receiptBound ≤ a + n + 1`, so a take never finds it
empty (a receipt in for a token out). -/
def srvCmpStock (d : mvcc.KBReal) : IProp GF :=
  inv srvCmpStockN iprop(∃ (a n : Nat), ⧗ a ∗ ownToks d.γB.wb n ∗ ⌜receiptBound GF ≤ a + n + 1⌝)

instance srvCmpStock_persistent (d : mvcc.KBReal) : Persistent (srvCmpStock (GF := GF) d) := by
  unfold srvCmpStock; infer_instance

/-- **A stock from `n` fresh tokens**, `receiptBound ≤ n + 1` of them. -/
theorem srvCmpStock_alloc (d : mvcc.KBReal) (n : Nat) (h : receiptBound GF ≤ n + 1) (Ms : CoPset) :
    ⊢ ownToks (GF := GF) d.γB.wb n ={Ms}=∗ srvCmpStock d := by
  iintro Hn
  imod receipt_zero (GF := GF) with H0
  unfold srvCmpStock
  iapply inv_alloc srvCmpStockN Ms
  inext
  iexists 0, n
  iframe H0 Hn
  ipureintro; omega

/-- **The compaction's supply from the stock** (`kbWTSupplyM`): a token for a receipt, at any time. -/
theorem kbWTSupplyM_of_cmpStock (d : mvcc.KBReal) :
    srvCmpStock (GF := GF) d ⊢ mvcc.kbWTSupplyM (some d) := by
  iintro #Hs
  unfold mvcc.kbWTSupplyM
  split
  · unfold mvcc.kbWTSupply
    iintro !> Hr
    unfold srvCmpStock
    iinv Hs with ⟨%a, %n, >Ha, >Hn, >%Hb⟩ Hclose
    icases receipt_add_one_lt a $$ [Hr Ha] with ⟨%Hlt, Ha⟩
    · iframe
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    icases wbToks_split d n' $$ Hn with ⟨Ht, Hn⟩
    imod Hclose $$ [Ha Hn] with -
    · inext
      iexists a + 1, n'
      iframe Ha Hn
      ipureintro; omega
    imodintro
    iexact Ht
  · itrivial

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
