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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.store.Read.wp_proof (hNew : mvcc.newMetricsTxnRead.spec (GF := GF) (hG := hG)) :
    mvcc.store.Read.spec (GF := GF) (hG := hG) := by
  intro s γ mode trace m log₀ te clb Z oa
  wp_start as ⟨#Hs, Hrd, #HZ, Hmine, #Hc0, #Hclb, %Htrnn, Htrc, HoA⟩
  ihave Htrc : iprop(∃ te' : Bool, traceutil.ownTrace trace te') $$ [Htrc]
  · iexists te; iexact Htrc
  iunfold mvcc.idxCert at Hc0
  icases Hc0 with ⟨-, -, #Hl0, -⟩
  ihave #Hs0 : mvcc.isStore s γ $$ []
  · iexact Hs
  iunfold mvcc.isStore at Hs
  iNamed Hs
  iunfold mvcc.storeReaderC at Hrd
  iNamedSuffix Hrd "R"
  (try wp_auto)
  -- `s.mu.RLock()`: its part of `s.mu`'s resource, at the compaction revision `cm`, at or above
  -- the caller's lower bound
  wp_apply +noauto sync.RWMutex.wp_RLock $$ [$HmuR] as ⟨Hmul, HmuP⟩
  wp_auto_lc 2
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.muInv s γ sync.rfrac)) $$ Hlc1 HmuP with HmuP
  iunfold mvcc.muInv at HmuP
  icases HmuP with ⟨%cm, HmuP, Hwr, Hfs⟩
  -- the share of the fields at the current objects and physical names `p` (D22 receiver epochs,
  -- S5b): the transaction is at `γ.withPhys p`
  iunfold mvcc.fieldShare at Hfs
  icases Hfs with ⟨%p, %o, Hfs⟩
  iunfold mvcc.fieldShareAt at Hfs
  iNamed Hfs
  iunfold mvcc.physOk at Hph
  iNamed Hph
  withPhys_simp
  -- a slot of the index's lock, out of the readers' pool (D22 receiver epochs, S4)
  icases (mvcc.wDep_halves γ).1 $$ Hwr with ⟨Hwr, Hwr2⟩
  imod mvcc.readerPool_checkout_p γ p _ o $$ Hlc2 Hpool Hcur HtkR Hwr2 with ⟨Hslot, Htko, Hcur⟩
  iunfold mvcc.idxSlot at Hslot
  icases Hslot with ⟨HtiR, HrtR⟩
  iunfold mvcc.storeFields at Hflds
  iNamed Hflds
  iunfold mvcc.muInvAt at HmuP
  iNamed HmuP
  icases mvcc.crevUB_lb_keep γ.idx _ cm clb HcM $$ [$HcrevM $Hclb] with ⟨HcrevM, %Hclbc⟩
  icases mvcc.crevUB_get_lb γ.idx _ cm $$ HcrevM with ⟨HcrevM, #Hlbc⟩
  -- `s.revMu.RLock()`
  wp_apply +noauto sync.RWMutex.wp_RLock $$ [$HrevMuR] as ⟨Hrevl, HP⟩
  wp_auto_lc 1
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.revMuInv s γ sync.rfrac)) $$ Hlc1 HP with HP
  icases mvcc.revMuInv_open_pin s γ p _ _ _ o $$ [HP Hfrst Hcur] with ⟨HP, HrstR, Hfrst, Hcur⟩
  · iframe HP Hfrst Hcur
  iunfold mvcc.revMuBody at HP
  icases HP with ⟨%log, %ntok, %c, HP⟩
  iNamed HP
  icases mvcc.logLent_agree γ.idx _ log oa $$ [$Hlog $HoA] with ⟨Hlog, HoA, %HoaL⟩
  ihave %Hcc := mvcc.crevUB_agree γ.idx _ _ cm c HcM Hc.1 $$ HcrevM Hcrev
  subst Hcc
  -- the caller's tokens are among the budget's
  icombine Htoks Hmine gives %Hle
  -- the caller's certificate is below the committed log
  ihave %Hpre := mono_list_auth_lb_valid γ.idx.log _ _ _ $$ Hlog Hl0
  ihave #Hbk0 := Hbk
  iunfold mvcc.isKeyBackendG at Hbk
  icases Hbk with ⟨%bi, %Hbi, #HC, #HR, -⟩
  (try wp_auto)
  -- the snapshot: `b.ConcurrentReadTx()` or `b.ReadTx()`
  rw [Hbi]
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
    wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hrevl Hrev Hbucket Hclog Hcert Htoks Hlog Hcmp Hcrev HrstR]
      as HrevMuR
    · inext
      iapply mvcc.revMuInv_close; iframe HrstR; iunfold mvcc.revMuBody
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
    ihave Hfs : mvcc.fieldShareAt s (γ.withPhys p) sync.rfrac.half o $$ [Hcur Hfb Hfidx Hfsch Hfstop Hfrst]
    · iunfold mvcc.fieldShareAt
      simp only [named]
      withPhys_simp
      iframe Hcur Hfrst
      isplitl
      · iunfold mvcc.storeFields; simp only [named]; rw [Hbi]; iframe Hfb Hfidx Hfsch Hfstop
      iunfold mvcc.physOk
      iexists Ph, Dep
      simp only [named]
      withPhys_simp
      rw [Hbi]
      iframe #
      ipureintro; simpa using Hcmt
    ihave Hmul : sync.ownRWMutexRLocked (mvcc.muAddr s) (mvcc.muInv s (γ.withPhys p)) $$ [Hmul]
    · rw [mvcc.muInv_withPhys]; iexact Hmul
    ihave Hmuh : mvcc.muHeld s (γ.withPhys p) cm o.ti $$ [Hmul HcmpM HcrevM Hfs]
    · iunfold mvcc.muHeld
      iframe Hmul
      isplitr [Hfs]
      · rw [mvcc.muInvAt_withPhys]
        iunfold mvcc.muInvAt
        iframe HcmpM HcrevM
        iframe #
        ipureintro; exact HcM
      iexists o
      iframe Hfs
      ipureintro; rfl
    wp_apply (hNew _) as %mw ⟨%trw, Hmw, Htrw⟩
    (try wp_auto)
    iStructNamedPrefix Htrw "W"
    iapply HΦ
    iexists log, (W64 ((log.length : Int) - 1)), cm
    isplitr [Hmine HoA]
    rotate_left
    · iframe Hmine Hlbc Hok HoA
      ipureintro; exact ⟨⟨Hpre.2, by omega, Hclbc⟩, HoaL⟩
    iunfold mvcc.isTxnRead
    iexists p, trw, tr, o.ti, rt, (W64 0)
    simp only [named]
    iframe Hmw HrevMuR HtiR WTxnRead Hmuh Htrc
    isplitl []
    · iexact Hs0
    isplitl []
    · iunfold mvcc.storeTxnReadIs
      simp only [named]
      withPhys_simp
      iframe #
      ipureintro
      first
        | exact ⟨Hne, trivial, Htrnn, HcM, Hc.2⟩
        | exact ⟨Hne, Htrnn, HcM, Hc.2⟩
        | exact ⟨Hne, rfl, Htrnn, HcM, Hc.2⟩
    iunfold mvcc.txReader
    iexists (mvcc.bucketMap log), m', Rd, Tok
    simp only [named]
    withPhys_simp
    iframe Htok Hthin Hwr Htko
    isplitr
    · iapply mvcc.keyReadLocked_weaken $$ Hsnap0
    ipureintro; exact fun _ _ h => h

end proof

end EtcdGrove
end Perennial
