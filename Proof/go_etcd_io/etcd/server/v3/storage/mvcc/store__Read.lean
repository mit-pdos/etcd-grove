/-
Proof of `Spec/.../mvcc/store__Read.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Read
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.newMetricsTxnRead

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.store.Read.wp_proof (hNew : mvcc.newMetricsTxnRead.spec (GF := GF) (hG := hG)) :
    mvcc.store.Read.spec (GF := GF) (hG := hG) := by
  intro s γ mode trace
  wp_start as ⟨#Hs, Hrd⟩
  ihave #Hs0 : mvcc.isStore s γ $$ []
  · iexact Hs
  iunfold mvcc.isStore at Hs
  iNamed Hs
  iunfold mvcc.storeReader at Hrd
  icases Hrd with ⟨%ti2, Hrd⟩
  iNamedSuffix Hrd "R"
  (try wp_auto)
  -- `s.mu.RLock()`
  wp_apply +noauto sync.RWMutex.wp_RLock $$ [$HmuR] as ⟨Hmul, -⟩
  (try wp_auto)
  -- `s.revMu.RLock()`
  wp_apply +noauto sync.RWMutex.wp_RLock $$ [$HrevMuR] as ⟨Hrevl, HP⟩
  wp_auto_lc 1
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.revMuInv s γ sync.rfrac)) $$ Hlc1 HP with HP
  iunfold mvcc.revMuInv at HP
  icases HP with ⟨%log, HP⟩
  iNamed HP
  iunfold mvcc.isKeyBackend at Hbk
  icases Hbk with ⟨%bi, %Hbi, #HC, #HR, -⟩
  subst Hbi
  (try wp_auto)
  -- the snapshot: `b.ConcurrentReadTx()` or `b.ReadTx()`
  wp_if_destruct <;> (try wp_auto)
  all_goals
    first
      | (ihave HCq := HC $$ %sync.rfrac %(mvcc.bucketMap log)
         wp_apply HCq $$ [$Hbucket] as %rt ⟨Hbucket, #Hsnap⟩)
      | (ihave HRq := HR $$ %sync.rfrac %(mvcc.bucketMap log)
         wp_apply HRq $$ [$Hbucket] as %rt ⟨Hbucket, #Hsnap⟩)
  all_goals
    (try wp_auto)
    ihave #Hsnap0 : mvcc.keyReadSnap rt (mvcc.bucketMap log) $$ []
    · iexact Hsnap
    iunfold mvcc.keyReadSnap at Hsnap
    icases Hsnap with ⟨#HRL, #HRU, #Hrange⟩
    -- `tx.RLock()`
    wp_apply HRL
    (try wp_auto)
    -- `s.revMu.RUnlock()`
    wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hrevl Hrev Hbucket Hclog Hcert] as HrevMuR
    · inext
      iunfold mvcc.revMuInv
      iexists log
      simp only [named]
      iframe Hrev Hbucket Hclog
      iframe #
      ipureintro; exact Hne
    (try wp_auto)
    wp_alloc tr as Htr
    iStructNamedPrefix Htr "T"
    iStructNamedPrefix TstoreTxnCommon "C"
    ipersist Cs
    ipersist Ctx
    ipersist CfirstRev
    ipersist Crev
    ipersist Ctrace
    ipersist Ttx
    (try wp_auto)
    wp_apply (hNew _) as %mw ⟨%trw, Hmw, Htrw⟩
    (try wp_auto)
    iStructNamedPrefix Htrw "W"
    iapply HΦ
    iexists log, (W64 ((log.length : Int) - 1))
    iunfold mvcc.isTxnRead
    iexists trw, tr, trace, ti2, rt, (W64 0)
    simp only [named]
    iframe Hmw Hmul HrevMuR HtiR WTxnRead
    isplitl []
    · iexact Hs0
    isplitl []
    · iunfold mvcc.storeTxnReadIs
      iexists (mvcc.bucketMap log)
      simp only [named]
      iframe #
      isplitl []
      · ipureintro; exact fun _ _ h => h
      ipureintro; exact ⟨Hne, trivial⟩
    iexact HidxR

end proof

end EtcdGrove
end Perennial
