/-
Proof of `Spec/.../mvcc/storeTxnRead__End.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnRead__End


@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.storeTxnRead.End.wp_proof : mvcc.storeTxnRead.End.spec (GF := GF) (hG := hG) := by
  intro tr s trace ti rt γ log rev crev Z
  wp_start as ⟨#Hs, #Htr, Hrd, #Hidx0, Hmu0, HrevMu0, Hti0⟩
  ihave #HpoolS : mvcc.readerPool γ $$ []
  · iunfold mvcc.isStore at Hs; iNamed Hs; iexact Hpool
  iunfold mvcc.storeTxnReadIs at Htr
  iNamedSuffix Htr "T"
  iunfold mvcc.txReader at Hrd
  icases Hrd with ⟨%m, %m', %Rd, %Tok, Hrd⟩
  iNamed Hrd
  iunfold mvcc.keyReadLocked at Hsnap
  icases Hsnap with ⟨#HRU, -, -, -⟩
  wp_auto_lc 1
  -- `tr.tx.RUnlock()`
  wp_apply HRU $$ [$Htok] as Hrt
  (try wp_auto)
  -- the slot of the index's lock back in the readers' pool (D22 receiver epochs, S4)
  imod mvcc.readerPool_checkin γ $$ Hlc1 HpoolS [Hti0 Hrt] Htko with ⟨Htk, Hwr2⟩
  · iunfold mvcc.idxSlot; iexists ti; iframe Hidx0 Hti0 Hrt
  -- `tr.s.mu.RUnlock()`
  iunfold mvcc.muHeld at Hmu0
  icases Hmu0 with ⟨Hmu0, Hmua, Hfs⟩
  wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hmu0 Hmua Hwr Hwr2 Hfs] as Hmu0
  · inext; iunfold mvcc.muInv; iexists crev; iframe Hmua Hfs
    iapply (mvcc.wDep_halves γ).2; iframe Hwr Hwr2
  (try wp_auto)
  iapply HΦ
  iframe HZT
  iunfold mvcc.storeReaderC
  simp only [named]
  iframe Hmu0 HrevMu0 Htk

end proof

end EtcdGrove
end Perennial
