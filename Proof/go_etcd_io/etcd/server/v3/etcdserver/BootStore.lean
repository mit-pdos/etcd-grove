/-
**The boot's storage over mvcc's API** (R6 of the `lean` merge, 2026-11-07): what `NewServer` makes
of the backend `bootstrap` opened (`bootOk`'s `newPostK … (bootLeft N)`) before `mvcc.New`, the store's
storage `mvccStorageFor` at `mvccStart` (`mvccImage_fresh.law`, `etcdStorage_open.law`), and the
write budget (`srvWTPool`) whose stock backs the storage's receipt-paid write-back supply
(`wbSupply_of_stock`: the one stock, shared with the server's own writes). Lean-first (no Rocq
counterpart).

The budget's invariant holds the storage-version monitor's read token of the backend (`apply.bkRT`)
and must exist before the storage is opened (the open takes the supply), when every counted reader
slot of the backend (`rdStock`) is still the opener's: the token's slot is one of the pool's
`rdPoolN` (`backend.rdPool` made from `rdPoolN - 1`, enough for `threadBound GF ≤ rdPoolN`) and its
open share one of the stock's; the open gives two counted slots back, one the apply thread's, the
other dropped.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BootBackend
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.EtcdBackend
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Image

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section boot
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The write budget reads only the environment's backend variable.** -/
theorem srvWTPool_congr (E E' : apply.AEnv GF) (γp : WTNames) (h : E.γbe = E'.γbe) :
    srvWTPool (GF := GF) E γp = srvWTPool E' γp := by
  unfold srvWTPool; rw [h]

/-- **The constructor's reader slots, split for the boot**: the pool from `rdPoolN - 1` of them,
one spare, the auth share and the counted stock. -/
theorem bootRdToks_split (hT : threadBound GF ≤ backend.rdPoolN) (E : CoPset)
    (γ : backend.BNames) (P : backend.BParams) (b : Loc) :
    ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
      backend.rdTok (GF := GF) γ P b) ⊢
      |={E}=> backend.rdPool γ P b ∗ backend.rdTok γ P b ∗ backend.rdAuth γ P b ∗
        backend.rdStock γ P b := by
  rewrite [← backend.rdPoolN_add_rdStockN]
  iintro Hs
  icases (backend.bigSepL_replicate_add _ (backend.rdPoolN + backend.authRdN) backend.rdStockN).1
    $$ Hs with ⟨Hp, Hs⟩
  icases (backend.bigSepL_replicate_add _ backend.rdPoolN backend.authRdN).1 $$ Hp with ⟨Hp, Ha⟩
  rw [show backend.rdPoolN = (backend.rdPoolN - 1) + 1 by unfold backend.rdPoolN; omega]
  icases (backend.bigSepL_replicate_add _ (backend.rdPoolN - 1) 1).1 $$ Hp with ⟨Hp, H1⟩
  imod backend.rdPool_init γ P b E (backend.rdPoolN - 1)
    (by unfold backend.rdPoolN at hT ⊢; omega) $$ Hp with Hp
  rw [List.replicate_one]
  icases BigSepL.bigSepL_cons.1 $$ H1 with ⟨H1, -⟩
  imodintro
  unfold backend.rdAuth backend.rdStock
  iframe

/-- **The boot's storage and write budget** (see the file header): from `bootstrap`'s backend
(`newPostK` at the store's write invariant `mvccW bk.gx` and the batch lock's `Pk`, with the payment
rights `bootLeft N`), the store's registration, `keySized` and the budget's quarter of the backend's
ghost variable `γbe`, over fresh data: the budget (`srvWTPool` at every environment of variable
`γbe`, its counter at `0`, its register empty, its stock of `bk`'s `N` write-back tokens), the store's
storage at the empty history (`mvccStorageFor`), and the client's rest: the backend and its stop
channels, its hook at `nil`, the tracked buckets' half, the reader pool with its shares, the auth
store's share of the slots, the constructors' half of the open token, the apply thread's read token
(a counted slot the open gave back, with its share), and five write-back tokens for the
construction's own writes. -/
theorem boot_storage
    (hfresh : mvcc.api.mvccImage_fresh.law (GF := GF))
    (hopen : mvcc.api.etcdStorage_open.law (GF := GF))
    (hrest : mvcc.api.backendRest_open.law (GF := GF))
    (hT : threadBound GF ≤ backend.rdPoolN) (N : Nat) (hrb : receiptBound GF ≤ N + 1)
    (bk : mvcc.KBReal) (Pk : backend.BNames → IProp GF) (D : backend.Data)
    (E₁ : apply.AEnv GF) (γbe : GName)
    (hbp : mvcc.bridgeParams bk.P) (hlp : mvcc.leaseParams bk.P) (hcm : bk.cm = true)
    (hk : ∀ k, backend.dget D mvcc.keyName k = none) (hnc : mvcc.noCmpData D) :
    backend.newPostK bk.γB bk.P (fun _ => mvcc.api.mvccW bk.gx) Pk (bootLeft N) bk.be D ∗
      mvcc.api.mvccWReg bk.gx ∗ □ (∀ (γ' : backend.BNames) (b' : Loc), mvcc.keySized γ' bk.P b') ∗
      dghostVar γbe (DFrac.own (1 : Qp).half.half) (bkKey bk) ⊢ |={⊤}=>
    ∃ γp : WTNames,
      □ (∀ E : apply.AEnv GF, ⌜E.γbe = γbe⌝ -∗ srvWTPool E γp) ∗ srvWTAt γp.cnt (W64 0) ∗
      dghostVar γp.reg (DFrac.own 1) (none : Option GName) ∗ srvWTStockInv γp.cnt bk ∗
      mvcc.api.mvccStorageFor (mvcc.api.etcdStorage bk) (Pk bk.γB) mvcc.api.mvccStart.log
        mvcc.api.mvccStart.crev false ∗
      backend.isBackend bk.γB bk.P (mvcc.api.mvccW bk.gx) (Pk bk.γB) bk.be ∗
      backend.isStopChans bk.γB bk.P (mvcc.api.mvccW bk.gx) (Pk bk.γB) bk.be ∗
      backend.plHook bk.γB func.nil ∗ backend.rbOwn bk.γB (backend.rbData bk.P D) ∗
      backend.bkRPool bk.γB bk.P bk.be ∗ backend.rdAuth bk.γB bk.P bk.be ∗
      backend.bOpen bk.γB (1 : Qp).half ∗ apply.bkRT bk ∗ ownToks bk.γB.wb 5 := by
  iintro ⟨Hnew, Hreg, #Hsz, Hq⟩
  iunfold backend.newPostK at Hnew
  icases Hnew with ⟨#HnB, #HnSC, HK, HnV, HnH, HnRB, HnRd, HnDl, HnFk, HnSr⟩
  iunfold bootLeft at HK
  icases HK with ⟨HnWb, Ho⟩
  -- the open token's shares: the constructors' half, the pool's, the stock's
  icases (backend.bOpen_one_pool bk.γB).1 $$ Ho with ⟨Ho, Hop, Hos⟩
  have hS := backend.rdStockN_val
  rw [show backend.rdStockN = ((backend.rdStockN - 2) + 1) + 1 by omega]
  icases (backend.bigSepL_replicate_add _ ((backend.rdStockN - 2) + 1) 1).1 $$ Hos with ⟨Hos, HoA⟩
  icases (backend.bigSepL_replicate_add _ (backend.rdStockN - 2) 1).1 $$ Hos with ⟨Hos, HoM⟩
  rw [List.replicate_one]
  icases BigSepL.bigSepL_cons.1 $$ HoA with ⟨HoA, -⟩
  icases BigSepL.bigSepL_cons.1 $$ HoM with ⟨HoM, -⟩
  -- the reader slots: the pool (one fewer), the spare (the monitor's), the auth share, the stock
  imod bootRdToks_split hT ⊤ bk.γB bk.P bk.be $$ HnRd with ⟨HnPool, HrtM, HnRA, HnRT⟩
  -- the write-back tokens: the budget's `N`, the store's two, the construction's five
  rw [show N + 7 = N + (2 + 5) by omega]
  icases (ownToks_add (2 + 5) N bk.γB.wb).1 $$ HnWb with ⟨HwN, Hw7⟩
  icases (ownToks_add 5 2 bk.γB.wb).1 $$ Hw7 with ⟨Hw2, Hw5⟩
  icases (ownToks_add 1 1 bk.γB.wb).1 $$ Hw2 with ⟨Hwa, Hwb⟩
  -- the write budget, with the monitor's read token
  let E₂ : apply.AEnv GF := { E₁ with γbe := γbe, BkTie := srvBkTie bk }
  imod srvWTPool_alloc E₂ N ⊤ hrb $$ [Hq HwN HrtM HoM] with
    ⟨%γp, #Hpool, #Hat0, ⟨%d0, %Hd0, #Hstock⟩, Hrg⟩
  · iunfold srvWTStock
    iexists bk
    iframe Hq HwN
    isplitr
    · ipureintro; rfl
    iunfold apply.bkRT; iframe HrtM HoM
  have hd0 : d0 = bk := (srvBkTie_inj d0 bk Hd0.symm)
  subst hd0
  ihave #Hsup := wbSupply_of_stock E₂ γp d0 $$ [$Hpool $Hstock]
  -- the storage, over the fresh data
  imod (hfresh D hk hnc.1 hnc.2) with #Him
  ihave HPKP : backend.newPostKP d0.γB d0.P (fun _ => mvcc.api.mvccW d0.gx) Pk
      (fun _ => iprop(True)) d0.be D $$ [HnV HnH HnRB HnPool HnRA HnRT HnDl HnFk HnSr]
  · unfold backend.newPostKP
    iframe HnB HnSC HnV HnH HnRB HnPool HnRA HnRT HnDl HnFk HnSr
  imod (hopen d0 Pk (fun _ => iprop(True)) D mvcc.api.mvccStart.log mvcc.api.mvccStart.crev false
      hbp hlp hcm) $$ [Hsz Him HPKP Hreg Hwa Hwb Hsup Hos]
    with ⟨Hsto, Hrest, HrtA, -⟩
  · iframe Hsz Him HPKP Hreg Hsup Hos
    unfold backend.wbTok
    iframe Hwa Hwb
  ihave ⟨-, -, HnH, HnRB, #HnPool, HnRA⟩ := hrest d0.γB d0.P _ d0.be D $$ Hrest
  ihave HbkP := backend.bkRPool_intro d0.γB d0.P d0.be $$ [$HnPool $Hop]
  imodintro
  iexists γp
  iframe Hat0 Hrg Hstock Hsto HnB HnSC HnH HnRB HbkP HnRA Ho Hw5
  isplitr
  · iintro !> %E %hE
    rw [srvWTPool_congr E E₂ γp hE]
    iexact Hpool
  iunfold apply.bkRT; iframe HrtA HoA

/-- **The boot's storage and write budget at a restart** (restart S6, 2026-11-13; probe P2): as
`boot_storage`, over the stopped member's image instead of fresh data: the image's store part
(`mvccImage D L c u`, `srvDiskImageAt`'s, at the KV model's history `L` and compaction revision `c`,
an unfinished compaction iff `u`) in place of `mvccImage_fresh.law`'s fresh facts; the storage at that
history (`mvccStorageFor … L c u`). -/
theorem boot_storageR
    (hopen : mvcc.api.etcdStorage_open.law (GF := GF))
    (hrest : mvcc.api.backendRest_open.law (GF := GF))
    (hT : threadBound GF ≤ backend.rdPoolN) (N : Nat) (hrb : receiptBound GF ≤ N + 1)
    (bk : mvcc.KBReal) (Pk : backend.BNames → IProp GF) (D : backend.Data)
    (E₁ : apply.AEnv GF) (γbe : GName)
    (hbp : mvcc.bridgeParams bk.P) (hlp : mvcc.leaseParams bk.P) (hcm : bk.cm = true)
    (L : mvcc.Log) (c : Int) (u : Bool) :
    mvcc.api.mvccImage D L c u ∗
    backend.newPostK bk.γB bk.P (fun _ => mvcc.api.mvccW bk.gx) Pk (bootLeft N) bk.be D ∗
      mvcc.api.mvccWReg bk.gx ∗ □ (∀ (γ' : backend.BNames) (b' : Loc), mvcc.keySized γ' bk.P b') ∗
      dghostVar γbe (DFrac.own (1 : Qp).half.half) (bkKey bk) ⊢ |={⊤}=>
    ∃ γp : WTNames,
      □ (∀ E : apply.AEnv GF, ⌜E.γbe = γbe⌝ -∗ srvWTPool E γp) ∗ srvWTAt γp.cnt (W64 0) ∗
      dghostVar γp.reg (DFrac.own 1) (none : Option GName) ∗ srvWTStockInv γp.cnt bk ∗
      mvcc.api.mvccStorageFor (mvcc.api.etcdStorage bk) (Pk bk.γB) L c u ∗
      backend.isBackend bk.γB bk.P (mvcc.api.mvccW bk.gx) (Pk bk.γB) bk.be ∗
      backend.isStopChans bk.γB bk.P (mvcc.api.mvccW bk.gx) (Pk bk.γB) bk.be ∗
      backend.plHook bk.γB func.nil ∗ backend.rbOwn bk.γB (backend.rbData bk.P D) ∗
      backend.bkRPool bk.γB bk.P bk.be ∗ backend.rdAuth bk.γB bk.P bk.be ∗
      backend.bOpen bk.γB (1 : Qp).half ∗ apply.bkRT bk ∗ ownToks bk.γB.wb 5 := by
  iintro ⟨Him, Hnew, Hreg, #Hsz, Hq⟩
  iunfold backend.newPostK at Hnew
  icases Hnew with ⟨#HnB, #HnSC, HK, HnV, HnH, HnRB, HnRd, HnDl, HnFk, HnSr⟩
  iunfold bootLeft at HK
  icases HK with ⟨HnWb, Ho⟩
  -- the open token's shares: the constructors' half, the pool's, the stock's
  icases (backend.bOpen_one_pool bk.γB).1 $$ Ho with ⟨Ho, Hop, Hos⟩
  have hS := backend.rdStockN_val
  rw [show backend.rdStockN = ((backend.rdStockN - 2) + 1) + 1 by omega]
  icases (backend.bigSepL_replicate_add _ ((backend.rdStockN - 2) + 1) 1).1 $$ Hos with ⟨Hos, HoA⟩
  icases (backend.bigSepL_replicate_add _ (backend.rdStockN - 2) 1).1 $$ Hos with ⟨Hos, HoM⟩
  rw [List.replicate_one]
  icases BigSepL.bigSepL_cons.1 $$ HoA with ⟨HoA, -⟩
  icases BigSepL.bigSepL_cons.1 $$ HoM with ⟨HoM, -⟩
  -- the reader slots: the pool (one fewer), the spare (the monitor's), the auth share, the stock
  imod bootRdToks_split hT ⊤ bk.γB bk.P bk.be $$ HnRd with ⟨HnPool, HrtM, HnRA, HnRT⟩
  -- the write-back tokens: the budget's `N`, the store's two, the construction's five
  rw [show N + 7 = N + (2 + 5) by omega]
  icases (ownToks_add (2 + 5) N bk.γB.wb).1 $$ HnWb with ⟨HwN, Hw7⟩
  icases (ownToks_add 5 2 bk.γB.wb).1 $$ Hw7 with ⟨Hw2, Hw5⟩
  icases (ownToks_add 1 1 bk.γB.wb).1 $$ Hw2 with ⟨Hwa, Hwb⟩
  -- the write budget, with the monitor's read token
  let E₂ : apply.AEnv GF := { E₁ with γbe := γbe, BkTie := srvBkTie bk }
  imod srvWTPool_alloc E₂ N ⊤ hrb $$ [Hq HwN HrtM HoM] with
    ⟨%γp, #Hpool, #Hat0, ⟨%d0, %Hd0, #Hstock⟩, Hrg⟩
  · iunfold srvWTStock
    iexists bk
    iframe Hq HwN
    isplitr
    · ipureintro; rfl
    iunfold apply.bkRT; iframe HrtM HoM
  have hd0 : d0 = bk := (srvBkTie_inj d0 bk Hd0.symm)
  subst hd0
  ihave #Hsup := wbSupply_of_stock E₂ γp d0 $$ [$Hpool $Hstock]
  -- the storage, over the image (in place of the fresh data's)
  ihave HPKP : backend.newPostKP d0.γB d0.P (fun _ => mvcc.api.mvccW d0.gx) Pk
      (fun _ => iprop(True)) d0.be D $$ [HnV HnH HnRB HnPool HnRA HnRT HnDl HnFk HnSr]
  · unfold backend.newPostKP
    iframe HnB HnSC HnV HnH HnRB HnPool HnRA HnRT HnDl HnFk HnSr
  imod (hopen d0 Pk (fun _ => iprop(True)) D L c u
      hbp hlp hcm) $$ [Hsz Him HPKP Hreg Hwa Hwb Hsup Hos]
    with ⟨Hsto, Hrest, HrtA, -⟩
  · iframe Hsz Him HPKP Hreg Hsup Hos
    unfold backend.wbTok
    iframe Hwa Hwb
  ihave ⟨-, -, HnH, HnRB, #HnPool, HnRA⟩ := hrest d0.γB d0.P _ d0.be D $$ Hrest
  ihave HbkP := backend.bkRPool_intro d0.γB d0.P d0.be $$ [$HnPool $Hop]
  imodintro
  iexists γp
  iframe Hat0 Hrg Hstock Hsto HnB HnSC HnH HnRB HbkP HnRA Ho Hw5
  isplitr
  · iintro !> %E %hE
    rw [srvWTPool_congr E E₂ γp hE]
    iexact Hpool
  iunfold apply.bkRT; iframe HrtA HoA

/-- **The monitor's read token back from a write budget no one used** (the construction's error
paths after the budget is made, `NewServer`'s, which close the backend and need every share of its
open token): with the budget's register still empty (no goroutine registered) and a part of the
backend variable, the budget's invariant is closed at its checked-out arm (the register set, at a
fresh receipt's name), and the token's open share comes out. -/
theorem srvWTPool_reclaim (E : apply.AEnv GF) (γp : WTNames) (k : backend.BNames × Loc) (q : Qp) :
    £ 1 ∗ srvWTPool (GF := GF) E γp ∗ dghostVar γp.reg (DFrac.own 1) (none : Option GName) ∗
      dghostVar E.γbe (DFrac.own q) k ⊢
      |={⊤}=> backend.bOpen k.1 backend.rdOpen := by
  iintro ⟨Hlc, #Hp, Hreg, Hq⟩
  unfold srvWTPool
  iinv Hp with ⟨%a, %d0, >Ha, >Hg0, #Hs0, >Hc, Hrt⟩ Hclose
  ihave %Hdd := dghostVar_agree E.γbe k _ (bkKey d0) _ $$ Hq Hg0
  subst Hdd
  imod lc_fupd_elim_later (E := ⊤ \ ↑srvWTN) $$ Hlc Hrt with Hrt
  icases Hrt with (Hrt | ⟨%q', -, %r, #Hreg', -⟩)
  · imod ownTokAuth_alloc (GF := GF) with ⟨%r, Hra⟩
    imod ownTokAuth_S r 0 $$ Hra with ⟨-, Hr1⟩
    imod dghostVar_update (some r) γp.reg (none : Option GName) $$ Hreg with Hreg
    imod dghostVar_persist γp.reg 1 (some r) $$ Hreg with #Hreg
    imod Hclose $$ [Ha Hg0 Hc Hq Hr1] with -
    · inext
      iexists a, d0
      iframe Ha Hg0 Hs0 Hc
      iright
      iexists q
      iframe Hq
      iexists r
      iframe Hreg
      ileft; iexact Hr1
    imodintro
    iunfold apply.bkRT at Hrt
    icases Hrt with ⟨-, Ho⟩
    iExactEq Ho; rfl
  · ihave %Hv := dghostVar_valid_2 γp.reg _ _ _ _ $$ Hreg Hreg'
    exfalso
    obtain ⟨Hv, -⟩ := Hv
    have h := DFrac.valid_own_op_discard.1 Hv
    simp at h

end boot

end EtcdGrove
end Perennial
