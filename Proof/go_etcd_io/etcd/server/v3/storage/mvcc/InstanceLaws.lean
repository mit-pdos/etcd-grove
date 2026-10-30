/-
**The real backend instance's laws** (the backend-cmp Probe, 2026-10-30;
`notes/spec-first-study/backend-probe.md`, section 4, sites 18-20): the store's backend-instance
resources (`kbView`, `kbNoCmp`, `kbRegRight`, `kbWT`, `kbRT`) at the real backend `some d`, as
equations, so that a client outside mvcc (the server's boot and snapshot path) does not unfold them.
In a module of their own, so that adding them leaves mvcc's other modules as they were.

(M2, the storage side, 2026-10-30; `notes/m2-storage-plan.md`) The compaction's budgets at the real
backend, from what the backend's creator holds: the safe-range slot (`kbSRM_some`, from `newPost`'s
`srSlot`; Probe S3) and the write-back supply from a stock of write-back tokens (`kbWTSupplyM_alloc`;
Probe S1: until then no client outside mvcc could build `kbWTSupplyM` without unfolding it).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BackendBridge

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI backend

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- The view of the `Key` bucket at the real backend: the backend's clients' (`bkView`). -/
@[simp] theorem kbView_some (d : KBReal) (γb : GName) (q : Qp) (m : Bucket) :
    kbView (GF := GF) (some d) γb q m = bkView d.γB q m := rfl

/-- The no-compaction token at the real backend: the backend's flag at `0` (`bkNoCmp`). -/
@[simp] theorem kbNoCmp_some (d : KBReal) (γb : GName) :
    kbNoCmp (GF := GF) (some d) γb = bkNoCmp d.γB := rfl

/-- The right to register the store's lock resource at the real backend (`lateReg`). -/
@[simp] theorem kbRegRight_some (d : KBReal) : kbRegRight (GF := GF) (some d) = lateReg d.gx := rfl

/-- A write session's token at the real backend: a write-back's budget (`wbTok`). -/
@[simp] theorem kbWT_some (d : KBReal) : kbWT (GF := GF) (some d) = backend.wbTok d.γB := rfl

/-- A reader's token at the real backend (`bkRTx`). -/
@[simp] theorem kbRT_some (d : KBReal) : kbRT (GF := GF) (some d) = bkRTx d.γB d.P d.be := rfl

/-- **The mode at the real backend** (M2's storage side, review round 1's S2): the instance compacts
iff its creator chose it (`KBReal.cm`), so that a client outside mvcc does not unfold `kbCmpM`. -/
theorem kbCmpM_some (d : KBReal) : kbCmpM (some d) ↔ d.cm = true := Iff.rfl

/-- **The readers a compacting real backend keeps back** (S2): the compaction job's one. -/
theorem nJobRd_some_on (d : KBReal) (h : d.cm = true) : nJobRd (some d) = 1 := by
  unfold nJobRd; simp [h]

/-- **The safe-range slot by the mode, from the backend's** (Probe S3): what a creator holding
`backend.New`'s `srSlot` gives `NewStore` (`kbSRM`), in either mode. -/
theorem kbSRM_some (d : KBReal) : backend.srSlot (GF := GF) d.be ⊢ kbSRM (some d) := by
  unfold kbSRM kbSR
  split
  · exact .rfl
  · iintro -; itrivial

end laws

section supply
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The write-back supply's invariant name (`kbWTSupplyM_alloc`). -/
abbrev wtSupplyN : Namespace := nroot.@"mvcc_wtSupply"

/-- **The write-back supply from a stock** (Probe S1; persistent): `n` write-back tokens of the real
backend `d`, under `receiptBound GF ≤ n + 1`, make the compaction's supply (`kbWTSupplyM`: a token for
each time receipt), in an invariant holding, for the `a` tokens taken, `a` receipts and the `n'`
left, with `receiptBound GF ≤ a + n' + 1` (as the server's `srvWTPool`): a receipt more than the
`a` held is below the bound, so a token is left. For a creator other than the server (whose supply
is `srvWTPool`'s, R2-7): a stock of its own. The bound is the law's own, and its margin is small: a
creator holding the backend's `wbInit - 2` tokens left after `NewStore`'s two needs
`receiptBound GF ≤ wbInit - 1 = 2^40 - 2`, where the stores need only `receiptBound GF ≤ 2^48`
(review round 1's S8). -/
theorem kbWTSupplyM_alloc (d : KBReal) (n : Nat) (h : receiptBound GF ≤ n + 1) (E : CoPset) :
    ownToks (GF := GF) d.γB.wb n ⊢ |={E}=> kbWTSupplyM (some d) := by
  iintro Hn
  imod receipt_zero (GF := GF) with H0
  imod inv_alloc wtSupplyN E iprop(∃ a m : Nat, ⧗ a ∗ ownToks (GF := GF) d.γB.wb m ∗
      ⌜receiptBound GF ≤ a + m + 1⌝) $$ [H0 Hn] with #Hinv
  · inext
    iexists 0, n
    iframe H0 Hn
    ipureintro; omega
  imodintro
  unfold kbWTSupplyM
  split
  · unfold kbWTSupply
    iintro !> Hr
    iinv Hinv with ⟨%a, %m, >Ha, >Hm, >%Hb⟩ Hclose
    icases receipt_add_one_lt a $$ [Hr Ha] with ⟨%Hlt, Ha⟩
    · iframe
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    icases (ownToks_add 1 m' d.γB.wb).1 $$ Hm with ⟨Hm, Ht⟩
    imod Hclose $$ [Ha Hm] with -
    · inext
      iexists a + 1, m'
      iframe Ha Hm
      ipureintro; omega
    imodintro
    unfold backend.wbTok
    iexact Ht
  · itrivial

/-- **The backend's deletable keys fixed at the store's** (M2, the storage side, review round 1's S2:
a law, so the server's glue does not unfold `storeDlReg`). -/
theorem storeDlReg_fix (γB : backend.BNames) (γi : IdxNames) :
    backend.dlInit (GF := GF) γB ⊢ |==> storeDlReg γB γi := by
  iintro H
  unfold storeDlReg
  iapply backend.dlReg_fix γB _ $$ H

end supply

end mvcc
end EtcdGrove
end Perennial
