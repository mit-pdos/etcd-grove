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

end supply

end EtcdGrove
end Perennial
