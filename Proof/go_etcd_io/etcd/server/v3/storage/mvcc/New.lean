/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.New
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.newWatchableStore
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__syncWatchersLoop
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__syncVictimsLoop
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.NewWatchableLemmas

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

/-- Two of the reader slots out of `n ≥ 2`. -/
theorem mvcc.slots_take2 (Q : IProp GF) (n : Nat) (h : 2 ≤ n) :
    ([∗list] _x ∈ List.replicate n (), Q) ⊢
      Q ∗ Q ∗ [∗list] _x ∈ List.replicate (n - 2) (), Q := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 2 = m by omega, List.replicate_succ, List.replicate_succ]
  iintro H
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H2, H⟩
  iframe

theorem mvcc.New.wp_proof
    (hNew : mvcc.newWatchableStore.spec (GF := GF) (hG := hG))
    (hSWL : mvcc.watchableStore.syncWatchersLoop.spec (GF := GF) (hG := hG))
    (hSVL : mvcc.watchableStore.syncVictimsLoop.spec (GF := GF) (hG := hG)) :
    mvcc.New.spec (GF := GF) (hG := hG) := by
  intro lg b le cfg γb γl P f
  wp_start as ⟨Hbk, Hbv, #Hlessor⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_apply hNew $$ [$Hbk $Hbv $Hlessor] as %s ⟨%st, %γ, %Hγ, #Hws, #Hhook, Hww, Hreaders,
    ⟨%stc, #Hstc, Hstop⟩, Hsclose, Hwg⟩
  (try wp_auto)
  imod sync.init_WaitGroup mvcc.wsWgWGN (mvcc.wsWgAddr s) $$ Hwg with ⟨%γwg, #HisWg, Hctr, Hwaiters⟩
  wp_apply mvcc.wp_wsWg_Add2_init s γwg $$ [$Hctr $Hwaiters] as ⟨Hctr, Hwaiters⟩
  · iframe #
  imod ownTokAuth_alloc (GF := GF) with ⟨%γd, Hauth⟩
  imod ownTokAuth_add 2 γd 0 $$ Hauth with ⟨Hauth, Hdone⟩
  icases (ownToks_add 1 1 γd).1 $$ Hdone with ⟨Hd1, Hd2⟩
  imod inv_alloc mvcc.wsWgN ⊤ (mvcc.wsWgInv γwg γd) $$ [Hctr Hauth] with #Hinv
  · inext
    iunfold mvcc.wsWgInv
    iexists W32 2, 0 + 2
    iframe Hctr Hauth
    ipureintro; decide
  have hN : 2 ≤ Int.toNat sync.rwmutex.actualMaxReaders := by
    rw [sync.rwmutex.actualMaxReaders_unseal]; decide
  icases mvcc.slots_take2 _ _ hN $$ Hreaders with ⟨Hr1, Hr2, Hreaders⟩
  (try wp_auto)
  wp_apply wp_fork $$ [Hr1 Hd1]
  · wp_apply hSWL s st γ $$ [$Hws $Hr1 Hd1]
    · iunfold mvcc.wsDone
      iexists γwg, γd
      iframe HisWg Hinv Hd1
    itrivial
  (try wp_auto)
  wp_apply wp_fork $$ [Hr2 Hd2]
  · wp_apply hSVL s st γ $$ [$Hws $Hr2 Hd2]
    · iunfold mvcc.wsDone
      iexists γwg, γd
      iframe HisWg Hinv Hd2
    itrivial
  (try wp_auto)
  iapply HΦ
  iexists st, γ
  iframe Hws Hhook Hww Hreaders
  isplitr
  · ipureintro; exact Hγ
  iunfold mvcc.wsCloser
  iexists stc
  iframe Hstc Hstop Hsclose
  iunfold mvcc.wsWaiter
  iexists γwg, γd
  iframe HisWg Hinv Hwaiters

end proof

end EtcdGrove
end Perennial
