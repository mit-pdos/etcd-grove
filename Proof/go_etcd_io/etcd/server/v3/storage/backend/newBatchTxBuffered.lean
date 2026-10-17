/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/newBatchTxBuffered.lean`. The first
`Commit` is proved through its code (`Commit`, `batchTxBuffered.commit`, `unsafeCommit`,
`batchTx.commit`, the `Unlock`s), not through their specs, which take the backend's invariants
(`isBackend`) that do not exist yet; on this path no hook runs (the hooks field is still nil),
no read transaction is rolled back (none is open) and nothing is committed (no write transaction
is open): it only begins the two transactions. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.newBatchTxBuffered
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__begin
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.NewLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

set_option maxHeartbeats 0 in
theorem backend.newBatchTxBuffered.wp_proof
    (hBegin : backend.backend.begin.spec (GF := GF) (hG := hG)) :
    backend.newBatchTxBuffered.spec (GF := GF) (hG := hG) := by
  intro b rt db lim γrw γd D
  wp_start as ⟨#Hbc, #Hrt, #Hlim, %Hlimp, Hhk, Hrtx, #Hrw, Hst, Hmu, Hown, Hwr⟩
  wp_auto
  wp_apply wp_map_make1 (K := w64) (V := Loc) as %m0 Hm0
  wp_apply wp_map_make1 (K := w64) (V := Bool) as %s0 Hs0
  iStructNamed «$r0»
  iStructNamed batchTx
  iStructNamed buf
  ipersist backend
  wp_method_call
  wp_call
  wp_auto
  -- `t.lock()`: the promoted `batchTx.lock`, `t.Mutex.Lock()` on the owned mutex
  wp_method_call
  wp_call
  wp_method_call
  wp_call
  try wp_auto
  wp_apply (wp_Mutex_Lock_own (muOf «$r0_ptr»)) $$ [Mutex] as Mutex
  · iexact Mutex
  try wp_auto
  -- `t.commit(false)` (`batchTxBuffered.commit`): `readTx.Lock()`
  wp_method_call
  wp_call
  try wp_auto
  wp_method_call
  wp_call
  try wp_auto
  wp_apply_core (sync.rwmutex.RWMutex.wp_Lock γrw (rmuOf (baseOf rt)) (nroot.@"rw")) $$ [] [-]
  · iframe #
    iPkgInit
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists (rwmutex.RLocked 0)
  iframe Hst
  iintro %_ Hst
  imod Hmask with _
  imodintro
  try wp_auto
  -- `unsafeCommit(false)`: no hooks, no read transaction open
  wp_method_call
  wp_call
  try wp_auto
  -- `batchTx.commit(false)`: no write transaction open; `t.tx = b.begin(true)`
  wp_method_call
  wp_call
  try wp_auto
  wp_apply (hBegin γd b db D true) $$ [$Hmu $Hown Hwr] as %wtx ⟨Hmu, Hown, #Hwdb, Hwtx⟩
  · iframe #
    simp only [↓reduceIte]
    iexact Hwr
  try wp_auto
  -- `b.readTx.tx = b.begin(false)`
  wp_apply (hBegin γd b db D false) $$ [$Hmu $Hown] as %rtx ⟨Hmu, Hown, #Hrdb, Hrd⟩
  · iframe #
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial
  try wp_auto
  -- `readTx.Unlock()`
  wp_method_call
  wp_call
  try wp_auto
  wp_apply_core (sync.rwmutex.RWMutex.wp_Unlock γrw (rmuOf (baseOf rt)) (nroot.@"rw")) $$ [] [-]
  · iframe #
    iPkgInit
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iframe Hst
  iintro Hst
  imod Hmask with _
  imodintro
  try wp_auto
  -- `t.Unlock()` (`batchTxBuffered.Unlock`): nothing pending; `batchTx.Unlock`: below the limit
  wp_method_call
  wp_call
  try wp_auto
  wp_method_call
  wp_call
  try wp_auto
  wp_if_destruct
  · exfalso; word
  try wp_auto
  wp_apply (wp_Mutex_Unlock_own (muOf «$r0_ptr»)) $$ [Mutex] as Mutex
  · iexact Mutex
  try wp_auto
  icases Hrd with ⟨Hrl, #Hrs, Hrst⟩
  iapply HΦ
  iexists wtx, rtx
  iframe
  iframe #
  unfold ownWB ownBks bksAt
  iexists m0, s0
  iframe
  iexists ∅
  rw [GMap.fmap_empty]
  iframe
  isplitl
  · iapply bbs_empty
  · ipureintro
    intro id x es h
    simp at h

end proof

end EtcdGrove
end Perennial
