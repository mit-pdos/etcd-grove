/-
**The lessor's backend contract's law** (mvccfull's Probe, 2026-11-09, the unfold list):
`lessorApplyOk` at a given backend, for a client that moves the lessor to a new backend
(`Recover`) and needs its contract there. In a module of its own, so that adding it leaves `SnapRO`
(and its importers) as they were.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapRO

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The lessor `lp`'s backend contract at the backend `d`**, whose post-lock hook is `f` for good
(not `nil`), with the write right `RW` lending the lessor's write part. -/
theorem lessorApplyOk_at (lp : Loc) (d : mvcc.KBReal) (W Pk : IProp GF) (f : GoFunc)
    (RW : IProp GF) :
    lessorApplyOk lp ∗ backend.isBackend d.γB d.P W Pk d.be ∗ backend.plHookRO d.γB f ∗
      ⌜f ≠ func.nil⌝ ∗ rwLens RW (lease.lessorBeOn lp d.be) ⊢
    lease.lessorBackend lp Pk #f (backend.wbTok d.γB) RW (apply.bkRT d)
      (backend.rbPart d.γB (· = go!"lease")) := by
  iintro ⟨#Hok, #Hb, #Hh, %Hf, #Hl⟩
  iunfold lessorApplyOk at Hok
  iapply Hok $$ %d %W %Pk %f %RW
  · iexact Hb
  · iexact Hh
  · ipureintro; exact Hf
  · iexact Hl

end laws

end EtcdGrove
end Perennial
