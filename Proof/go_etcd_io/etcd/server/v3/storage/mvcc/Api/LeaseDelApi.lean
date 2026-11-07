/-
**`mvccTxn_leaseDelete.law`** (2026-11-06). Lean-first (no Rocq counterpart). Over the sealed
definitions of `Api.lean` and `EtcdBackend.lean` (imported with `import all`).

The lessor's `Revoke` deletes a lease's record from the `Lease` bucket through the batch transaction
of an open write transaction (`le.b.BatchTx().UnsafeDelete`, under the store's lock). The API's
write transaction (`mvccTxnI`'s write arm) holds the inner store's transaction, whose
`storeTxnWriteIs_leaseDel` gives that delete (the right `storeRb`: the lease bucket's part of the
tracked buckets and `leaseParams`, which the backend share records, `mvccBackend`), leaving a
transaction whose lock token only `Unlock` takes (`ld = true`). Its `End` is `Txn.End.contract`'s
at the transaction's type, at `ld = true` (`txnW_end`: `EndApi`'s and `WatchTxnApi`'s write arms
with `ld` general).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.EtcdBackend
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.EtcdBackend
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.EndApi
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.WatchTxnApi
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.TrackedLemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

local notation "pkgInit" => isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc

/-- `isTxnWriteT_endY` at any lock token `ld`. -/
theorem isTxnWriteT_endY_ld (mw s : Loc) (γ : StoreNames) (p p' : PhysNames) (trace : Loc)
    (ilog : Log) (pend : List Change) (puts deletes putSize : w64) (crev : Int) (Z Tr : IProp GF)
    (ld : Bool) (σ : MvccState) (dq : DFrac) (o' : StoreObjs) (hl : σ.log = ilog)
    (hc : σ.crev = crev) :
    isTxnWriteT (GF := GF) mw s (γ.withPhys p) trace ilog pend puts deletes putSize crev Z ld Tr ∗
      curAt (γ.withPhys p') dq o' ⊢
      isTxnEndY mw s (γ.withPhys p) trace (.write ilog pend puts deletes putSize) crev Z
        (Yat (γ.withPhys p) σ) Tr ∗ curAt (γ.withPhys p') dq o' ∗ ⌜p = p'⌝ := by
  subst hl hc
  iintro ⟨H, Hc⟩
  iunfold isTxnWriteT at H
  iNamed H
  icases storeTxnWriteIs_split tw s (γ.withPhys p) σ.log pend σ.crev Z ld $$ Htw
    with ⟨%chs, %ps, Hcore, -, -⟩
  iunfold storeTxnWriteCore at Hcore
  iNamed Hcore
  icases muHeld_cur s (γ.withPhys p) σ.crev ti $$ Hmu with ⟨%o, %Ho, Hpin, Hmub⟩
  ihave %Hv := curAt_agree (γ.withPhys p) (γ.withPhys p') rfl _ _ o o' $$ [Hpin Hc]
  · iframe Hpin Hc
  ihave Hmu := Hmub $$ Hpin
  iunfold slotY at HY
  icases HY with ⟨%cy, HYa, HYp, HYr, HYw⟩
  icases muHeld_wcr s (γ.withPhys p) σ.crev ti _ cy $$ [$Hmu $HYw]
    with ⟨Hmu, HYw, %Hcy⟩
  subst Hcy
  iframe Hc
  isplitl
  · simp only [isTxnEndY]
    iexists chs, ps, false, ld
    iunfold isTxnWriteCoreY
    iexists tw, ranges
    iframe Hmw Htrc
    iunfold storeTxnWriteCoreY
    iexists ti, bt, Locked, ntok, Pw, fw, Dep
    simp only [named]
    iframe Htoks Htok Htw Hcap Hlocked Hw Hclog Hcur Hbv Hwv Htko Hmu HrevMu Hti Hrt Hcres Hlrd
    iframe #
    iunfold Yat
    iframe HYa HYp HYr HYw
    ipureintro; exact ⟨Hbudget, Hps, Hne, Htrnn, Hcrev⟩
  ipureintro; exact Hv.2

/-- **The write transaction's `End`, at any lock token `ld`** (`Txn.End.contract`'s write arm, over
the transaction's contents: `mvccTxnI`'s write arm with `ld` in place of `false`). -/
private theorem txnW_end (hEndM : mvcc.metricsTxnWrite.End.spec (GF := GF) (hG := hG))
    (hEndW : mvcc.watchableStoreTxnWrite.End.spec (GF := GF) (hG := hG))
    (ty : go.GoType) (v : val) (γ : StoreNames) (trace : Loc) (σ₀ : MvccState) (pend : List Change)
    (mw s : Loc) (p : PhysNames) (puts deletes putSize : w64) (ld : Bool) :
    ⌜σ₀.pending = none⌝ ∗
      isTxnWriteT mw s (γ.withPhys p) trace σ₀.log pend puts deletes putSize σ₀.crev iprop(True) ld
        iprop(True) ∗
      tokBack s (γ.withPhys p) ∗ certFree (γ.withPhys p) ∗
      wrWrap (interface.mkOk ty v) (γ.withPhys p) s mw σ₀.log ⊢
    ∀ (q : Qp) (B : MvccStorage) (P Q : IProp GF) (Φ : val → IProp GF),
      pkgInit ∗ mvccBackend γ q B P ∗ P ∗
          AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅
            <{ ⌜σ = σ₀⌝ ∗ mvccState γ (σ.notify pend) ∗ ⧖ (logCh (σ.log ++ [pend])), COMM
                AU <{ ∃∃ (σ' : MvccState), mvccState γ σ' }> @ ⊤ \ ↑mvccN, ∅
                  <{ ⌜σ' = σ₀.notify pend⌝ ∗ mvccState γ σ'.commitPending, COMM Q }> }> -∗
        ▷ (mvccReaders γ 1 ∗ mvccBackend γ q B P ∗ Q -∗ Φ #()) -∗
        WP (App (Val #(methods ty go!"End" v)) (Val #())) {{ Φ }} := by
  iintro ⟨%Hpn, Htx, Hback, #Hfree, Hwrap⟩ %q %B %P %Q %Φ ⟨#Hpkg, HB, HP, Hau⟩ HΦ
  iapply wp_fupd
  iunfold mvccBackend at HB
  icases HB with ⟨HF, %p', %o', %d, Hcur', %Hd, #Hbk, #Hrg, #Hhp, #Hwts, %Hlp⟩
  iunfold wrWrap at Hwrap
  icases Hwrap with (⟨%Hk, %Hwq⟩ | ⟨%tw, %sw, %γw, ⟨%Hk, %hγw⟩, Hwrap⟩)
  · -- a store without watchers: `*metricsTxnWrite`
    rw [interface_mkOk_inj] at Hk
    obtain ⟨rfl, rfl⟩ := Hk
    icases isTxnWriteT_endY_ld mw s γ p p' trace σ₀.log pend puts deletes putSize σ₀.crev iprop(True)
        iprop(True) ld σ₀ _ o' rfl rfl $$ [$Htx $Hcur'] with ⟨Hte, Hcur', %hpp⟩
    subst hpp
    have hwq' : (γ.withPhys p).watchQ = false := by simpa using Hwq
    iunfold mvccState at Hau
    have hcb := endCb_of_au (GF := GF) (γ.withPhys p) σ₀ σ₀.log pend σ₀.crev Q hwq' rfl Hpn
    simp only [endAU, StoreNames.withPhys_api] at hcb
    ihave Hcb := hcb $$ Hau
    ihave #Hx : □ (slotF (γ.withPhys p) ∗ api.shareTok γ.api q -∗ False) $$ []
    · iintro !> H
      iapply (slotF_share_excl (γ := γ.withPhys p) (a := γ.api) rfl q) $$ H
    ihave #Hok := certFree_certOkNext (γ.withPhys p) σ₀.log pend $$ Hfree
    iapply (hEndM trace mw s (γ.withPhys p) (.write σ₀.log pend puts deletes putSize) σ₀.crev
        iprop(True) (Yat (γ.withPhys p) σ₀) (api.shareTok γ.api q) Q iprop(True))
        $$ [Hte HP HF Hcb] [HΦ Hback Hcur']
    · iframe Hpkg Hte
      isplitl [HP]
      · simp only [txnEndPreH]
        iexists P
        iframe Hhp HP Hok
        rw [logQPre_plain _ _ _ hwq']
        itrivial
      simp only [txnEndX]
      iframe HF Hcb Hx
    inext
    iintro ⟨Hrd, -, -, -, HGR⟩
    simp only [txnEndXPost]
    icases HGR with ⟨HF, HQ⟩
    iunfold tokBack at Hback
    imod Hback $$ Hrd with Hrt
    ihave Hrt : ownToks (GF := GF) γ.api.rdk 1 $$ [Hrt]
    · rw [show γ.api = (γ.withPhys p).api from rfl]; iexact Hrt
    imodintro
    iapply HΦ
    iunfold mvccReaders
    iframe Hrt HQ
    iunfold mvccBackend
    iframe HF
    iexists p, o', d
    iframe Hcur' Hbk Hrg Hhp Hwts
    ipureintro; exact ⟨Hd, Hlp⟩
  · -- a watchable store's: `*watchableStoreTxnWrite`
    rw [interface_mkOk_inj] at Hk
    obtain ⟨rfl, rfl⟩ := Hk
    icases isTxnWriteT_names mw s γ p p' trace σ₀.log pend puts deletes putSize σ₀.crev iprop(True)
        ld iprop(True) _ o' $$ [$Htx $Hcur'] with ⟨Htx, Hcur', %hpp⟩
    subst hpp
    ihave Htx : isTxnWriteT mw s γw.st trace σ₀.log pend puts deletes putSize σ₀.crev iprop(True)
        ld iprop(True) $$ [Htx]
    · rw [hγw]; iexact Htx
    ihave #Hwq : ⌜γw.st.watchQ = true⌝ $$ [Hwrap]
    · iunfold wsWrap at Hwrap
      icases Hwrap with ⟨-, #Hws, -⟩
      iunfold isWatchableStore at Hws
      iNamed Hws
      ipureintro; exact Hwq
    icases Hwq with %Hwq
    ihave Htw := wsWrap_join tw sw s γw mw trace σ₀.log pend puts deletes putSize σ₀.crev ld
      iprop(True) $$ [$Hwrap $Htx]
    iunfold mvccState at Hau
    have hcb := wsEndCbY_of_au (GF := GF) γw σ₀ pend Q Hwq Hpn
    have ha : γw.st.api = γ.api := by rw [hγw]; rfl
    simp only [endAU, ha] at hcb
    ihave Hcb := hcb $$ Hau
    ihave #Hx : □ (slotF γw.st ∗ api.shareTok γ.api q -∗ False) $$ []
    · iintro !> H
      iapply (slotF_share_excl (γ := γw.st) (a := γ.api) ha q) $$ H
    ihave #Hok : certOkNext γw.st σ₀.log pend $$ []
    · rw [hγw]; iapply certFree_certOkNext; iexact Hfree
    ihave #Hhp' : hookP γw.st P $$ []
    · rw [hγw]; iexact Hhp
    wp_apply (hEndW trace tw sw s γw σ₀.log pend puts deletes putSize P σ₀.crev ld
        (api.shareTok γ.api q) Q iprop(True)) $$ [$Htw HP HF Hcb]
      as ⟨Hrd, -, -, HF, HQ⟩
    · iframe HP HF Hcb Hx Hok Hhp'
    iunfold tokBack at Hback
    ihave Hrd : storeReaderC s (γ.withPhys p) $$ [Hrd]
    · rw [← hγw]; iexact Hrd
    imod Hback $$ Hrd with Hrt
    ihave Hrt : ownToks (GF := GF) γ.api.rdk 1 $$ [Hrt]
    · rw [show γ.api = (γ.withPhys p).api from rfl]; iexact Hrt
    imodintro
    iapply HΦ
    iunfold mvccReaders
    iframe Hrt HQ
    iunfold mvccBackend
    iframe HF
    iexists p, o', d
    iframe Hcur' Hbk Hrg Hhp Hwts
    ipureintro; exact ⟨Hd, Hlp⟩

/-- `S`'s part of the tracked buckets: the lease bucket's and the rest's. -/
private theorem rbPart_lease_split (γB : backend.BNames) (S : GoString → Prop) (hS : S leaseName)
    (r : GMap GoString backend.BktData) :
    backend.rbPart (GF := GF) γB S r ⊣⊢
      iprop(backend.rbPart γB (· = leaseName) r ∗
        backend.rbPart γB (fun n => S n ∧ n ≠ leaseName) r) := by
  have hset : ∀ n, S n ↔ (n = leaseName ∨ (S n ∧ n ≠ leaseName)) := by
    intro n
    constructor
    · intro h; by_cases hn : n = leaseName
      · exact Or.inl hn
      · exact Or.inr ⟨h, hn⟩
    · rintro (h | ⟨h, -⟩)
      · subst h; exact hS
      · exact h
  refine (backend.rbPart_set γB S _ r hset).trans ?_
  exact backend.rbPart_split γB (· = leaseName) (fun n => S n ∧ n ≠ leaseName) r
    (fun n h1 h2 => h2.2 h1)

theorem mvccTxn_leaseDelete.law_holds (hEndM : mvcc.metricsTxnWrite.End.spec (GF := GF) (hG := hG))
    (hEndW : mvcc.watchableStoreTxnWrite.End.spec (GF := GF) (hG := hG)) :
    mvccTxn_leaseDelete.law (GF := GF) := by
  intro twI (γ : mvcc.StoreNames) trace σ pend q bk Pk t b key k dq S r Φ hS
  iintro ⟨Htx, HB, #Ht, #Hb, Hkey, Hrb, HΦ⟩
  iunfold mvccTxn at Htx
  simp only [mvccTxnI]
  icases Htx with ⟨%mw, %s, %p, %puts, %deletes, %putSize, %Hk0, Htx, Hback, #Hfree, Hwrap⟩
  iunfold mvccBackend at HB
  icases HB with ⟨HF, %p', %o', %d, Hcur', %Hd, #Hbk, #Hrg, #Hhp, #Hwts, %Hlp⟩
  obtain ⟨hpk, hcm, hdB⟩ := Hd
  have hdb : d = bk := hdB
  subst hdb
  icases isTxnWriteT_names mw s γ p p' trace σ.log pend puts deletes putSize σ.crev iprop(True)
      false iprop(True) _ o' $$ [$Htx $Hcur'] with ⟨Htx, Hcur', %hpp⟩
  subst hpp
  -- the delete, through the inner transaction's batch transaction
  iunfold isTxnWriteT at Htx
  iNamed Htx
  icases storeTxnWriteIs_leaseDel tw s (γ.withPhys p) σ.log pend σ.crev iprop(True) $$ Htw
    with ⟨%bt, #HbtB, Hdel⟩
  have ebt : ∀ x, storeBt (GF := GF) (γ.withPhys p) x = bkBt d.be x := by
    intro x; unfold storeBt kbBt; simp only [StoreNames.withPhys_kb, hpk]
  have erb : ∀ x, storeRb (GF := GF) (γ.withPhys p) x =
      iprop(backend.rbPart d.γB (· = leaseName) x ∗ ⌜leaseParams d.P⌝) := by
    intro x; unfold storeRb kbRb; simp only [StoreNames.withPhys_kb, hpk]
  ihave #HbtB' : bkBt (GF := GF) d.be bt $$ []
  · rw [← ebt]; iexact HbtB
  iunfold bkBt at HbtB'
  icases HbtB' with ⟨%t', %hbt, #Ht', -⟩
  icombine Ht Ht' gives %Htt
  subst hbt
  subst Htt
  -- the lease bucket's part, with the backend's parameters (the share's)
  icases (rbPart_lease_split d.γB S hS r).1 $$ Hrb with ⟨HrbL, HrbR⟩
  ihave HrbL : storeRb (GF := GF) (γ.withPhys p) r $$ [HrbL]
  · rw [erb]
    iframe HrbL; ipureintro; exact Hlp
  iapply Hdel $$ %b %key %k %dq %r %Φ Hb Hkey HrbL
  inext
  iintro Htw' Hkey HrbL'
  ihave HrbL' : backend.rbPart (GF := GF) d.γB (· = leaseName) (rbDel r leaseName k) $$ [HrbL']
  · rw [erb]
    icases HrbL' with ⟨H, -⟩; iexact H
  ihave HrbR' : backend.rbPart (GF := GF) d.γB (fun n => S n ∧ n ≠ leaseName) (rbDel r leaseName k)
      $$ [HrbR]
  · iapply (backend.rbPart_congr d.γB _ r (rbDel r leaseName k) ?_).1 $$ HrbR
    intro n hn
    unfold rbDel
    rw [GMap.lookup_insert_ne _ _ (Ne.symm hn.2)]
  iapply HΦ $$ [HF Hcur'] Hkey [HrbL' HrbR']
  · iunfold mvccBackend
    iframe HF
    iexists p, o', d
    iframe Hcur' Hbk Hrg Hhp Hwts
    ipureintro; exact ⟨⟨hpk, hcm, rfl⟩, Hlp⟩
  · iapply (rbPart_lease_split d.γB S hS _).2; iframe HrbL' HrbR'
  -- `End`'s triple: the transaction at `ld = true`
  iintro %Q
  iapply (txnW_end hEndM hEndW twI.ty twI.v γ trace σ pend mw s p puts deletes putSize true) $$
    [Hmw Htw' Htrc Hback Hwrap] %q %(etcdStorage d) %Pk %Q
  iframe Hback Hfree Hwrap
  isplitr
  · ipureintro; exact Hk0.1
  iunfold isTxnWriteT
  iexists tw, ranges
  iframe Hmw Htw' Htrc

end proof

end api
end mvcc
end EtcdGrove
end Perennial
