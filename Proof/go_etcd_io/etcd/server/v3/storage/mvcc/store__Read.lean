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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.store.Read.wp_proof (hNew : mvcc.newMetricsTxnRead.spec (GF := GF) (hG := hG)) :
    mvcc.store.Read.spec (GF := GF) (hG := hG) := by
  intro s γ mode trace m log₀
  wp_start as ⟨#Hs, Hrd, Hmine, #Hc0, %Htrnn⟩
  iunfold mvcc.idxCert at Hc0
  icases Hc0 with ⟨-, -, -, #Hl0⟩
  ihave #Hs0 : mvcc.isStore s γ $$ []
  · iexact Hs
  iunfold mvcc.isStore at Hs
  iNamed Hs
  iunfold mvcc.storeReader at Hrd
  icases Hrd with ⟨%ti2, Hrd⟩
  iNamedSuffix Hrd "R"
  (try wp_auto)
  -- `s.mu.RLock()`: its part of `s.mu`'s resource, at a compaction revision the frozen fact
  -- says is `-1`
  wp_apply +noauto sync.RWMutex.wp_RLock $$ [$HmuR] as ⟨Hmul, HmuP⟩
  wp_auto_lc 1
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.muInv s γ sync.rfrac)) $$ Hlc1 HmuP with HmuP
  iunfold mvcc.muInv at HmuP
  icases HmuP with ⟨%cm, HmuP⟩
  iunfold mvcc.muInvAt at HmuP
  iNamed HmuP
  imod mvcc.crevFrozen_agree γ _ cm HcM $$ HfrzR HcrevM with ⟨HcrevM, %Hcm1⟩
  subst Hcm1
  -- `s.revMu.RLock()`
  wp_apply +noauto sync.RWMutex.wp_RLock $$ [$HrevMuR] as ⟨Hrevl, HP⟩
  wp_auto_lc 1
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.revMuInv s γ sync.rfrac)) $$ Hlc1 HP with HP
  iunfold mvcc.revMuInv at HP
  icases HP with ⟨%log, %ntok, %c, HP⟩
  iNamed HP
  imod mvcc.crevFrozen_agree γ _ c Hc.1 $$ HfrzR Hcrev with ⟨Hcrev, %Hc1⟩
  subst Hc1
  -- the caller's tokens are among the budget's
  icombine Htoks Hmine gives %Hle
  -- the caller's certificate is below the committed log
  ihave %Hpre := mono_list_auth_lb_valid γ.idx.log _ _ _ $$ Hlog Hl0
  iunfold mvcc.isKeyBackendG at Hbk
  icases Hbk with ⟨%bi, %Hbi, #HC, #HR, -⟩
  subst Hbi
  (try wp_auto)
  -- the snapshot: `b.ConcurrentReadTx()` or `b.ReadTx()`
  wp_if_destruct <;> (try wp_auto)
  all_goals
    first
      | (ihave HCq := HC $$ %sync.rfrac.half %(mvcc.bucketMap log)
         wp_apply HCq $$ [$Hbucket $HrtR] as %rt ⟨Hbucket, Hsnap⟩)
      | (ihave HRq := HR $$ %sync.rfrac.half %(mvcc.bucketMap log)
         wp_apply HRq $$ [$Hbucket $HrtR] as %rt ⟨Hbucket, Hsnap⟩)
  all_goals
    (try wp_auto)
    icases Hsnap with ⟨%L, HL, #Hsnap⟩
    iunfold mvcc.keyReadSnap at Hsnap
    -- `tx.RLock()`, with the view (`s.revMu`'s, held)
    wp_bind (App (Val #(methods rt.ty go!"RLock" rt.v)) _)
    iapply Hsnap $$ %sync.rfrac.half [HL Hbucket]
    · iframe HL Hbucket
    inext
    iintro ⟨Hbucket, %m', %Rd, %Tok, Htok, #Hsnap0, #Hthin⟩
    -- the snapshot misses no key: the store is not compacted
    icases mvcc.snapThin_crev γ _ _ _ $$ [$HcrevM $Hthin] with ⟨HcrevM, %Hm'⟩
    subst Hm'
    (try wp_auto)
    -- `s.revMu.RUnlock()`
    wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hrevl Hrev Hbucket Hclog Hcert Htoks Hlog Hcmp Hcrev]
      as HrevMuR
    · inext
      iunfold mvcc.revMuInv
      iexists log, ntok, -1
      simp only [named]
      iframe Hrev Hbucket Hclog Htoks Hlog Hcmp Hcrev
      iframe #
      ipureintro; exact ⟨Hne, Hbudget, Hc⟩
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
    ihave Hmuh : mvcc.muHeld s γ (-1) $$ [Hmul HcmpM HcrevM]
    · iunfold mvcc.muHeld
      iframe Hmul
      iunfold mvcc.muInvAt
      iframe HcmpM HcrevM
      iframe #
      ipureintro; decide
    wp_apply (hNew _) as %mw ⟨%trw, Hmw, Htrw⟩
    (try wp_auto)
    iStructNamedPrefix Htrw "W"
    iapply HΦ
    iexists log, (W64 ((log.length : Int) - 1))
    isplitr [Hmine]
    rotate_left
    · iframe Hmine; ipureintro; exact ⟨Hpre.2, by omega⟩
    iunfold mvcc.isTxnRead
    iexists trw, tr, trace, ti2, rt, (W64 0)
    simp only [named]
    iframe Hmw HrevMuR HtiR WTxnRead Hmuh
    isplitl []
    · iexact Hs0
    isplitl []
    · iunfold mvcc.storeTxnReadIs
      simp only [named]
      iframe #
      ipureintro; first | exact ⟨Hne, trivial, Htrnn⟩ | exact ⟨Hne, Htrnn⟩
    isplitl [Htok]
    · iunfold mvcc.txReader
      iexists (mvcc.bucketMap log), Rd, Tok
      simp only [named]
      iframe Htok
      isplitr
      · iapply mvcc.keyReadLocked_weaken $$ Hsnap0
      ipureintro; exact fun _ _ h => h
    iexact HidxR

end proof

end EtcdGrove
end Perennial
