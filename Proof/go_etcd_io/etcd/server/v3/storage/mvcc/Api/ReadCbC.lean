/-
**A read's callback, given the compaction revision too** (M4, track B, 2026-11-06, the coordinator's
decision 5). Lean-first (no Rocq counterpart).

`store.Read` runs its caller's callback under `s.revMu` (shared) with that lock's slot of the API's
view at the committed log `L` it reads and the compaction revision `c` (`slotX γ q L c`); `readCb`'s
result depends on `L` only. A read transaction's state (`mvccTxn (.read σ)`) records both
`σ.log` and `σ.crev`, and the latter is the transaction's (`store.Read` learns `c` is the
compaction revision its transaction observed): `readCbC`'s result takes both. `readCb` is the case
whose result ignores `c` (`readCbC_of`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **A read's callback, at the log read and the compaction revision**: run once by `store.Read`
under `s.revMu` (shared), with that lock's slot, giving `F L c` and the slot back. -/
def readCbC (γ : StoreNames) (F : Log → Int → IProp GF) : IProp GF :=
  iprop(∀ (q : Qp) (L : Log) (c : Int), slotX γ q L c ={⊤}=∗ slotX γ q L c ∗ F L c)

/-- A callback whose result ignores the compaction revision. -/
theorem readCbC_of (γ : StoreNames) (F : Log → IProp GF) :
    readCb γ F ⊢ readCbC γ (fun L _ => F L) := by
  iintro Hcb
  iunfold readCb at Hcb
  iunfold readCbC
  iintro %q %L %c HX
  iapply Hcb $$ %q %L %c HX

theorem readCbC_true (γ : StoreNames) : ⊢ readCbC (GF := GF) γ (fun _ _ => iprop(True)) := by
  unfold readCbC
  iintro %q %L %c H
  imodintro; iframe H

end defs

end mvcc
end EtcdGrove
end Perennial
