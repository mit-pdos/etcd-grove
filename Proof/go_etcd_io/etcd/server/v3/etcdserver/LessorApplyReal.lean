/-
**The lessor's backend contract, of the real backend** (prove-ps2-newlessor5, 2026-11-21):
`lessorApplyOk lp` (`SnapRO.lean`, what `lease.NewLessor.spec`'s post gives) from the backend's specs
(`backend.BatchTx`, `batchTxBuffered.LockInsideApply`/`UnsafePut`/`Unlock`) and schema's `Lease`
bucket, as mvcc's `BackendBridge.lean` derives the store's (`bt_lockIn`, `bt_leaseDel`, `bt_unlockD`).
The lock's token holds the batch lock in a session that changed nothing the readers see (the put is
into `Lease`, a hook bucket: `viewSame_putHB`), with its write-back token, the lock's resource `W`
and, behind the critical section's view shift, the batch lock's invariant `Pk` and the caller's `X`;
the pending count is below the batch limit, plus one after the session's one put (`leaseBatchTx`
allows one), which leaves the `Unlock` room for the commit's hook (`BParams.Wf`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapRO
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BackendBridge

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section real
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [bk_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- The lessor's batch-lock token over the real backend (`leaseBatchTx`'s `Lk`): the batch lock
held in a session that changed nothing the readers see, its pending count below the limit (plus one
after the put, `p`), out of the hook's window; the write-back token, the lock's resource `W`, and
the batch lock's invariant `Pk` with `X` after a view shift (the critical section's). -/
def lessorLk (γ : backend.BNames) (P : backend.BParams) (b : Loc) (W Pk : IProp GF) (p : Bool)
    (X : IProp GF) : IProp GF :=
  iprop(∃ st : backend.BSess, backend.batchLocked γ P b st ∗ backend.wbTok γ ∗ W ∗
    (|={⊤}=> Pk ∗ X) ∗
    ⌜backend.viewSame P st ∧ st.cnt.hw = false ∧
      sint.Z st.pend < sint.Z P.limit + (if p then 1 else 0)⌝)

/-- **The lessor's backend contract at the real backend `d`** whose parameters let the lessor write
`Lease` (`mvcc.leaseParams`), its hook `f` frozen and not `nil`, the write right `RW` lending the
lessor's half of `le.b`. -/
theorem lessorBackend_real
    (hBT : backend.backend.BatchTx.spec (GF := GF) (hG := hG))
    (hLI : backend.batchTxBuffered.LockInsideApply.spec (GF := GF) (hG := hG))
    (hUP : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (hUL : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (lp : Loc) (d : mvcc.KBReal) (W Pk : IProp GF) (f : GoFunc) (RW : IProp GF)
    (hlp : mvcc.leaseParams d.P) (hf : f ≠ func.nil) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      backend.isBackend d.γB d.P W Pk d.be ∗ backend.plHookRO d.γB f ∗
      rwLens RW (lease.lessorBeOn lp d.be) ⊢
    lease.lessorBackend lp Pk #f (backend.wbTok d.γB) RW (apply.bkRT d)
      (backend.rbPart d.γB (· = go!"lease")) := by
  iintro ⟨#Hbpkg, #Hspkg, #HB, #Hhk, #Hlens⟩
  obtain ⟨hhas, hRB, hhk⟩ := hlp
  icases backend.isBackend_b d.γB d.P W Pk d.be $$ HB with ⟨%t', %rt, %db, %lg, -, -, -, -, -, -, -,
    -, -, -, -, %HPw⟩
  ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hspkg
  icases Hsi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨%bk, #HL, -⟩, -⟩
  ihave #Hbk := mvcc.lease_isBucket hID hName hSafe bk $$ [$Hspkg $HL]
  have hHB : d.P.HB mvcc.leaseBI.name = true := by
    show decide (mvcc.leaseName ≠ go_etcd_io.etcd.server.v3.storage.schema.keyName) = true
    decide
  have hSB : d.P.SB mvcc.leaseBI.name = false := by
    show decide (mvcc.leaseName = go_etcd_io.etcd.server.v3.storage.schema.keyName) = false
    decide
  have hrp : ∀ S, backend.rbPut (GF := GF) d.γB d.P mvcc.leaseBI.name S =
      backend.rbPart d.γB (· = mvcc.leaseName) (backend.rbData d.P S) := by
    intro S
    unfold backend.rbPut; rw [show mvcc.leaseBI.name = mvcc.leaseName from rfl, hRB]; rfl
  rw [show (go!"lease" : GoString) = mvcc.leaseName from rfl]
  iunfold lease.lessorBackend
  iexists (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be)
  isplitl
  · iunfold lease.leaseBackend
    isplitr
    · iexists bk; iexact HL
    iexists ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty, #d.be⟩
    isplitr
    · ipureintro; rfl
    iintro !> %Φ !> - HΦ
    wp_apply (hBT d.γB d.P W Pk d.be) $$ [$Hbpkg $HB] as %t #Ht
    iapply HΦ
    iunfold lease.leaseBatchTx
    iexists (lessorLk d.γB d.P d.be W Pk)
    isplitr
    · -- `LockInsideApply()`
      iintro !> %g %Pre %Q %Post %Hfg %Φ' !> ⟨Hcs, Hwb, Hrt⟩ HΦ'
      have hg : f = g := by
        have h := Hfg
        rw [go.intoVal_unfold GoFunc] at h
        obtain ⟨f1, f2, f3⟩ := f
        obtain ⟨g1, g2, g3⟩ := g
        injection h with h1 h2 h3
        subst h1 h2 h3
        rfl
      subst hg
      iunfold srvApi.csContractA at Hcs
      icases Hcs with ⟨Hpre, Hrun, Hcl⟩
      have hrun : mvcc.api.hookRun (GF := GF) Pk f Pre Q =
          iprop(□ {{ Pk ∗ Pre }} (App (Val #f) (Val #())) {{ RET #(); Q }}) := by
        unfold mvcc.api.hookRun; exact if_neg hf
      rw [hrun]
      iunfold apply.bkRT at Hrt
      icases Hrt with ⟨Hrd, Ho⟩
      wp_apply (hLI d.γB d.P W Pk d.be t backend.rdOpen DFrac.discard f Pre Q)
        $$ [$Hbpkg $HB $Ht $Ho $Hhk $Hpre Hrun] as ⟨%st, Hl, %Hfree, HW, HQ, Ho, -⟩
      · iright
        iframe Hrun
        ipureintro; exact hf
      iapply HΦ'
      iunfold lessorLk
      iexists st
      iframe Hl Hwb HW
      isplitl [HQ Hcl Hrd Ho]
      · ihave HPP := Hcl $$ HQ
        imod HPP with ⟨HPk, HPost⟩
        imodintro
        iframe HPk HPost
        iunfold apply.bkRT
        iframe Hrd Ho
      ipureintro
      refine ⟨backend.viewSame_of_freeOk Hfree, Hfree.2.2.2.2.1, ?_⟩
      simp only [Bool.false_eq_true, ↓reduceIte, Int.add_zero]
      exact Hfree.2.1
    isplitr
    · -- `UnsafePut(Lease, key, val)`
      iintro !> %X %bk' %key %val %kb %vb %r %Φ' !> ⟨%Hkl, HLk, #HL', #Hkey, #Hval, Hrb⟩ HΦ'
      icombine HL HL' gives %Hbk'
      subst Hbk'
      iunfold lessorLk at HLk
      icases HLk with ⟨%st, Hl, Hwb, HW, HX, %Hs⟩
      obtain ⟨hvs, hhw, hpend⟩ := Hs
      simp only [Bool.false_eq_true, ↓reduceIte, Int.add_zero] at hpend
      have hlim := HPw.2.2.1
      have hpend1 : sint.Z st.pend + 1 < 2 ^ 58 := by omega
      icases backend.batchLocked_rbPart d.γB d.P d.be st (· = mvcc.leaseName) r $$ [$Hl $Hrb]
        with ⟨Hl, Hrb, %Hr⟩
      ihave Hrb : backend.rbPut d.γB d.P mvcc.leaseBI.name st.S $$ [Hrb]
      · rw [hrp]
        iapply (backend.rbPart_congr d.γB _ (backend.rbData d.P st.S) r (fun n hn => Hr n hn)).2 $$ Hrb
      ihave Hhkp := backend.hkPut_of_not_HK (GF := GF) d.γB d.P mvcc.leaseBI.name kb st.S
        (by
          have h := hhk kb
          unfold backend.BParams.hk at h
          rw [show mvcc.leaseName = mvcc.leaseBI.name from rfl, hHB] at h
          simpa using h)
      ihave Hfkp := backend.fkPut_other (GF := GF) d.γB mvcc.leaseBI.name kb (mvcc.lease_not_fk kb)
      wp_apply (hUP d.γB d.P W Pk d.be t st bk mvcc.leaseBI key val kb vb hhas (by rw [Hkl]; decide)
          (by rw [Hkl]; decide) hpend1 (fun h => absurd h (by rw [hSB]; decide))
          (fun h => absurd h (mvcc.lease_not_fk kb)) false false (_hkc := by decide))
        $$ [$Hbpkg $HB $Ht $Hl $Hbk $Hkey $Hval $Hhkp $Hrb $Hfkp] as ⟨Hl, -, Hrb, -⟩
      iapply HΦ'
      isplitl [Hl Hwb HW HX]
      · iunfold lessorLk
        iexists (st.put mvcc.leaseBI kb vb false false)
        iframe Hl Hwb HW HX
        ipureintro
        refine ⟨mvcc.viewSame_putHB HPw hHB hhas hvs, hhw, ?_⟩
        simp only [↓reduceIte]
        show sint.Z (st.pend + W64 1) < _
        have : sint.Z (st.pend + W64 1) = sint.Z st.pend + 1 := by word
        omega
      -- the part, at the record put
      have hS' : (st.put mvcc.leaseBI kb vb false false).S =
          st.S.insert mvcc.leaseName ((backend.bktOf st.S mvcc.leaseName).insert kb vb) := rfl
      have hbk : backend.bktOf st.S mvcc.leaseName = (r.lookup mvcc.leaseName).getD ∅ := by
        rw [← Hr _ rfl, backend.rbData_lookup, hRB]; rfl
      have hcg : ∀ n, n = mvcc.leaseName →
          (backend.rbData d.P (st.S.insert mvcc.leaseName
            ((backend.bktOf st.S mvcc.leaseName).insert kb vb))).lookup n =
            (mvcc.rbSet r mvcc.leaseName kb vb).lookup n := by
        rintro n rfl
        rw [mvcc.rbData_insert_tracked _ hRB, GMap.lookup_insert, hbk]
        unfold mvcc.rbSet
        rw [GMap.lookup_insert]
      have hrp2 : ∀ S, backend.rbPut (GF := GF) d.γB d.P mvcc.leaseName S =
          backend.rbPart d.γB (· = mvcc.leaseName) (backend.rbData d.P S) := hrp
      rw [hrp2]
      iapply (backend.rbPart_congr d.γB _ _ _ hcg).1 $$ Hrb
    · -- `Unlock()`
      iintro !> %p %X %Φ' !> HLk HΦ'
      iunfold lessorLk at HLk
      icases HLk with ⟨%st, Hl, Hwb, HW, HX, %Hs⟩
      obtain ⟨hvs, hhw, hpend⟩ := Hs
      have hroom : sint.Z st.pend + d.P.hookMax < 2 ^ 58 := by
        have h1 := HPw.2.2.1
        have h2 := HPw.2.2.2.1
        cases p <;> simp only [Bool.false_eq_true, ↓reduceIte, Int.add_zero] at hpend <;> omega
      ihave ⟨#Hth, %Hnw⟩ := backend.viewSame_thin d.γB d.P st hvs
      imod HX with ⟨HPk, HX⟩
      -- (`wp_apply` aborts here without a message, as in mvcc's `bt_unlock`: the triple applied by hand)
      iapply ((backend.batchTxBuffered.Unlock.bare hUL) d.γB d.P W Pk d.be t st X hhw hroom)
        $$ %Φ' [Hl Hwb HW HPk HX] HΦ'
      iframe Hbpkg HB Ht Hl Hwb
      ileft; iframe HW HPk HX Hth; ipureintro; exact Hnw
  · -- the lent part lends `le.b`
    iintro !> HRW
    iunfold rwLens at Hlens
    icases Hlens $$ HRW with ⟨Hx, Hcl⟩
    iunfold lease.lessorBeOn at Hx
    iexists _
    iframe Hx
    iintro Hx
    iapply Hcl
    iunfold lease.lessorBeOn
    iexact Hx

/-- **`lessorApplyOk lp` of the real backend** (what `newLessor`'s proof gives `NewLessor`'s post):
`lessorBackend_real` at every backend it quantifies over. -/
theorem lessorApplyOk_real
    (hBT : backend.backend.BatchTx.spec (GF := GF) (hG := hG))
    (hLI : backend.batchTxBuffered.LockInsideApply.spec (GF := GF) (hG := hG))
    (hUP : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (hUL : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG)) (lp : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ⊢
    lessorApplyOk lp := by
  iintro ⟨#Hbpkg, #Hspkg⟩
  iunfold lessorApplyOk
  iintro !> %d %W %Pk %f %RW %hlp #HB #Hhk %hf #Hlens
  iapply lessorBackend_real hBT hLI hUP hUL hID hName hSafe lp d W Pk f RW hlp hf
  iframe #

end real

end EtcdGrove
end Perennial
