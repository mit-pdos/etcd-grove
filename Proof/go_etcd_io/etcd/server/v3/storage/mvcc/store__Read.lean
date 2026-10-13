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
  intro s γ mode trace m log₀ clb Z
  wp_start as ⟨#Hs, Hrd, #HZ, Hmine, #Hc0, #Hclb, %Htrnn⟩
  iunfold mvcc.idxCert at Hc0
  icases Hc0 with ⟨-, -, -, #Hl0⟩
  ihave #Hs0 : mvcc.isStore s γ $$ []
  · iexact Hs
  iunfold mvcc.isStore at Hs
  iNamed Hs
  iunfold mvcc.storeReaderC at Hrd
  icases Hrd with ⟨%ti2, Hrd⟩
  iNamedSuffix Hrd "R"
  (try wp_auto)
  -- `s.mu.RLock()`: its part of `s.mu`'s resource, at the compaction revision `cm`, at or above
  -- the caller's lower bound
  wp_apply +noauto sync.RWMutex.wp_RLock $$ [$HmuR] as ⟨Hmul, HmuP⟩
  wp_auto_lc 1
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.muInv s γ sync.rfrac)) $$ Hlc1 HmuP with HmuP
  iunfold mvcc.muInv at HmuP
  icases HmuP with ⟨%cm, HmuP⟩
  iunfold mvcc.muInvAt at HmuP
  iNamed HmuP
  icases mvcc.crevUB_lb_keep γ.idx _ cm clb HcM $$ [$HcrevM $Hclb] with ⟨HcrevM, %Hclbc⟩
  icases mvcc.crevUB_get_lb γ.idx _ cm $$ HcrevM with ⟨HcrevM, #Hlbc⟩
  -- `s.revMu.RLock()`
  wp_apply +noauto sync.RWMutex.wp_RLock $$ [$HrevMuR] as ⟨Hrevl, HP⟩
  wp_auto_lc 1
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.revMuInv s γ sync.rfrac)) $$ Hlc1 HP with HP
  iunfold mvcc.revMuInv at HP
  icases HP with ⟨%log, %ntok, %c, HP⟩
  iNamed HP
  ihave %Hcc := mvcc.crevUB_agree γ.idx _ _ cm c HcM Hc.1 $$ HcrevM Hcrev
  subst Hcc
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
    (try wp_auto)
    -- `s.revMu.RUnlock()`
    wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hrevl Hrev Hbucket Hclog Hcert Htoks Hlog Hcmp Hcrev]
      as HrevMuR
    · inext
      iunfold mvcc.revMuInv
      iexists log, ntok, cm
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
    ihave Hmuh : mvcc.muHeld s γ cm $$ [Hmul HcmpM HcrevM]
    · iunfold mvcc.muHeld
      iframe Hmul
      iunfold mvcc.muInvAt
      iframe HcmpM HcrevM
      iframe #
      ipureintro; exact HcM
    wp_apply (hNew _) as %mw ⟨%trw, Hmw, Htrw⟩
    (try wp_auto)
    iStructNamedPrefix Htrw "W"
    iapply HΦ
    iexists log, (W64 ((log.length : Int) - 1)), cm
    isplitr [Hmine]
    rotate_left
    · iframe Hmine Hlbc; ipureintro; exact ⟨Hpre.2, by omega, Hclbc⟩
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
      ipureintro
      first
        | exact ⟨Hne, trivial, Htrnn, HcM, Hc.2⟩
        | exact ⟨Hne, Htrnn, HcM, Hc.2⟩
        | exact ⟨Hne, rfl, Htrnn, HcM, Hc.2⟩
    isplitl [Htok]
    · iunfold mvcc.txReader
      iexists (mvcc.bucketMap log), m', Rd, Tok
      simp only [named]
      iframe Htok Hthin
      isplitr
      · iapply mvcc.keyReadLocked_weaken $$ Hsnap0
      ipureintro; exact fun _ _ h => h
    iexact HidxR

end proof

end EtcdGrove
end Perennial
