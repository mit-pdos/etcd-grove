/-
**The writing methods' resources, split** (strict M1, 2026-11-05): `mPreW` (the chain's
precondition of a method whose component writes the backend) split into the writer's half (for
`newHeader`), the critical-section contract at the backend `B`'s lock, the backend's write and read
tokens and its tie (what a component's write takes, `Contracts.lean`), the chain's resources and the
rest of the thread's KV resources (`kvRest`); and `mPostW` rebuilt from them. Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Chain

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apply

open Iris Iris.BI Iris.ProofMode
open mvcc.api (mvccBackend hookIs mvccLeases)

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **The thread's KV resources but the writer's half and the tie**, at the backend `B`: the
backend's whole share and its hook, the live leases, the auth store's reader resource. -/
def kvRest (E : AEnv GF) (log : mvcc.Log) (B : mvcc.KBReal) : IProp GF :=
  iprop(mvccBackend E.γ 1 B (E.Pk B) ∗ hookIs B E.f ∗ leasesLive E (mvcc.stateAfter log) ∗ E.RD)

/-- `mPreW`, split (see the file header). -/
theorem mPreW_split (E : AEnv GF) (c : Chain) (a : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    mPreW E c a info log Pre Q Post ⊢ ∃ (cr : Int) (B : mvcc.KBReal), srvApi.wSt E.γs log cr ∗
      srvApi.csContractA (E.Pk B) E.f Pre Q Post ∗ bkWT B ∗ bkRT B ∗ E.BkTie B ∗
      chainRes c a info ∗ kvRest E log B := by
  iintro H
  iunfold mPreW at H
  icases H with ⟨⟨%cr, Hw⟩, Hll, Hrd, Hres, %B, Hbk, Hhk, Htie, Hwt, Hrt, Hcs⟩
  iexists cr, B
  iframe Hw Hcs Hwt Hrt Htie Hres
  iunfold kvRest
  iframe Hbk Hhk Hll Hrd

/-- The thread's KV resources from the split. -/
theorem kvOwn_of_split (E : AEnv GF) (log : mvcc.Log) (B : mvcc.KBReal) (cr : Int) :
    srvApi.wSt E.γs log cr ∗ E.BkTie B ∗ kvRest E log B ⊢ kvOwn E log := by
  iintro ⟨Hw, Htie, Hr⟩
  iunfold kvRest at Hr
  icases Hr with ⟨Hbk, Hhk, Hll, Hrd⟩
  iunfold kvOwn
  isplitl [Hw]
  · iexists cr; iexact Hw
  isplitl [Hbk Hhk Htie]
  · iunfold kvBk; iexists B; iframe Hbk Hhk Htie
  iframe Hll Hrd

/-- **`mPostW` at the backend**, from the split's pieces, the caller's outcome and the reader
token back. -/
theorem mPostW_backend (E : AEnv GF) (a : GoInterface) (log : mvcc.Log) (Pre Post : IProp GF)
    (B : mvcc.KBReal) (cr : Int) :
    srvApi.wSt E.γs log cr ∗ E.BkTie B ∗ kvRest E log B ∗ (Post ∨ Pre) ∗ bkRT B ⊢
      mPostW E .backend a log Pre Post := by
  iintro ⟨Hw, Htie, Hr, HPP, Hrt⟩
  icases bkRTOf_intro E B $$ [$Htie $Hrt] with ⟨Htie, Hrt⟩
  iunfold mPostW
  isplitr [Hrt]
  · iapply mPost_backend
    iframe HPP
    iapply kvOwn_of_split E log B cr
    iframe Hw Htie Hr
  · iexact Hrt

/-- `mPreV` (the cluster methods', with `v3`), split as `mPreW`. -/
theorem mPreV_split (v3 : Bool) (E : AEnv GF) (c : Chain) (a : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    mPreV v3 E c a info log Pre Q Post ⊢ ∃ (cr : Int) (B : mvcc.KBReal), srvApi.wSt E.γs log cr ∗
      cPre v3 (E.Pk B) E.f Pre Q Post ∗ bkWT B ∗ bkRT B ∗ E.BkTie B ∗
      chainRes c a info ∗ kvRest E log B := by
  iintro H
  iunfold mPreV at H
  icases H with ⟨⟨%cr, Hw⟩, Hll, Hrd, Hres, %B, Hbk, Hhk, Htie, Hwt, Hrt, Hcs⟩
  iexists cr, B
  iframe Hw Hcs Hwt Hrt Htie Hres
  iunfold kvRest
  iframe Hbk Hhk Hll Hrd

/-- **`mPostV`** from the split's pieces, the writer's outcome and the reader token back. -/
theorem mPostV_of (v3 : Bool) (E : AEnv GF) (c : Chain) (a : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (log : mvcc.Log) (Pre Post : IProp GF)
    (B : mvcc.KBReal) (cr : Int) :
    srvApi.wSt E.γs log cr ∗ E.BkTie B ∗ kvRest E log B ∗ chainRes c a info ∗
      cPost v3 Pre Post ∗ bkRT B ⊢ mPostV v3 E c a info log Pre Post := by
  iintro ⟨Hw, Htie, Hr, Hres, HPP, Hrt⟩
  icases bkRTOf_intro E B $$ [$Htie $Hrt] with ⟨Htie, Hrt⟩
  iunfold mPostV
  iframe Hres HPP
  isplitl [Hw Htie Hr]
  · iapply kvOwn_of_split E log B cr
    iframe Hw Htie Hr
  · iexact Hrt

/-- **`mPre` without the chain's resources** (strict M1, 2026-11-05): what a wrapper passes on
unchanged, or gives back with `Pre` when it rejects (`mPreRest_reject`). -/
def mPreRest (E : AEnv GF) (log : mvcc.Log) (Pre Q Post : IProp GF) : IProp GF :=
  iprop((∃ cr : Int, srvApi.wSt E.γs log cr) ∗ leasesLive E (mvcc.stateAfter log) ∗ E.RD ∗
    ∃ B : mvcc.KBReal, mvccBackend E.γ 1 B (E.Pk B) ∗ hookIs B E.f ∗ E.BkTie B ∗
      srvApi.csContractA (E.Pk B) E.f Pre Q Post)

/-- `mPre` is `mPreRest` and the chain's resources. -/
theorem mPre_split_chain (E : AEnv GF) (c : Chain) (a : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    mPre E c a info log Pre Q Post ⊢ mPreRest E log Pre Q Post ∗ chainRes c a info := by
  iintro H
  iunfold mPre at H
  icases H with ⟨Hw, Hll, Hrd, Hres, Hb⟩
  iunfold mPreRest
  iframe

/-- `mPre` from `mPreRest` and the chain's resources. -/
theorem mPre_of_rest (E : AEnv GF) (c : Chain) (a : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    mPreRest E log Pre Q Post ∗ chainRes c a info ⊢ mPre E c a info log Pre Q Post := by
  iintro ⟨H, Hres⟩
  iunfold mPreRest at H
  icases H with ⟨Hw, Hll, Hrd, Hb⟩
  iunfold mPre
  iframe

/-- **A rejection**: the thread's KV resources and `Pre` back. -/
theorem mPreRest_reject (E : AEnv GF) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    mPreRest E log Pre Q Post ⊢ kvOwn E log ∗ Pre := by
  iintro H
  iunfold mPreRest at H
  icases H with ⟨Hw, Hll, Hrd, %B, Hbk, Hhk, Htie, Hcs⟩
  iunfold srvApi.csContractA at Hcs
  icases Hcs with ⟨HPre, -, -⟩
  iframe HPre
  iunfold kvOwn
  iframe Hw Hll Hrd
  iunfold kvBk
  iexists B
  iframe

/-- **A rejection of a writing method**: the thread's KV resources, the chain's, `Pre` and the
reader token back. -/
theorem mPreW_reject (E : AEnv GF) (c : Chain) (a : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    mPreW E c a info log Pre Q Post ⊢ kvOwn E log ∗ chainRes c a info ∗ Pre ∗ bkRTOf E := by
  iintro H
  icases mPreW_split E c a info log Pre Q Post $$ H with
    ⟨%cr, %B, Hw, Hcs, -, Hrt, Htie, Hres, Hkv⟩
  icases bkRTOf_intro E B $$ [$Htie $Hrt] with ⟨Htie, Hrt⟩
  iunfold srvApi.csContractA at Hcs
  icases Hcs with ⟨HPre, -, -⟩
  iframe HPre Hres
  isplitr [Hrt]
  · iapply kvOwn_of_split E log B cr
    iframe
  · iexact Hrt

/-- **`mPreW` without the chain's resources** (as `mPreRest`). -/
def mPreWRest (E : AEnv GF) (log : mvcc.Log) (Pre Q Post : IProp GF) : IProp GF :=
  iprop((∃ cr : Int, srvApi.wSt E.γs log cr) ∗ leasesLive E (mvcc.stateAfter log) ∗ E.RD ∗
    ∃ B : mvcc.KBReal, mvccBackend E.γ 1 B (E.Pk B) ∗ hookIs B E.f ∗ E.BkTie B ∗ bkWT B ∗ bkRT B ∗
      srvApi.csContractA (E.Pk B) E.f Pre Q Post)

theorem mPreW_split_chain (E : AEnv GF) (c : Chain) (a : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    mPreW E c a info log Pre Q Post ⊢ mPreWRest E log Pre Q Post ∗ chainRes c a info := by
  iintro H
  iunfold mPreW at H
  icases H with ⟨Hw, Hll, Hrd, Hres, Hb⟩
  iunfold mPreWRest
  iframe

theorem mPreW_of_rest (E : AEnv GF) (c : Chain) (a : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    mPreWRest E log Pre Q Post ∗ chainRes c a info ⊢ mPreW E c a info log Pre Q Post := by
  iintro ⟨H, Hres⟩
  iunfold mPreWRest at H
  icases H with ⟨Hw, Hll, Hrd, Hb⟩
  iunfold mPreW
  iframe

/-- **A rejection, the contract kept** (the auth layer's rejection lemmas take it). -/
theorem mPreRest_reject_cs (E : AEnv GF) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    mPreRest E log Pre Q Post ⊢
      kvOwn E log ∗ ∃ B : mvcc.KBReal, srvApi.csContractA (E.Pk B) E.f Pre Q Post := by
  iintro H
  iunfold mPreRest at H
  icases H with ⟨Hw, Hll, Hrd, %B, Hbk, Hhk, Htie, Hcs⟩
  isplitr [Hcs]
  · iunfold kvOwn
    iframe Hw Hll Hrd
    iunfold kvBk
    iexists B
    iframe
  · iexists B; iexact Hcs

/-- The auth store's reader resource and the lease owner's resource of `mPreRest`, lent out (as
`kvOwn_lend`). -/
theorem mPreRest_lend (E : AEnv GF) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    mPreRest E log Pre Q Post ⊢ E.RD ∗ ∃ L : List w64,
      lease.lessorUser (mvccLeases E.γ) L (mvcc.leaseItemsOf (mvcc.stateAfter log)) ∗
      (E.RD -∗ lease.lessorUser (mvccLeases E.γ) L (mvcc.leaseItemsOf (mvcc.stateAfter log)) -∗
        mPreRest E log Pre Q Post) := by
  iintro H
  iunfold mPreRest at H
  icases H with ⟨Hw, Hll, Hrd, Hb⟩
  iunfold leasesLive at Hll
  icases Hll with ⟨%L, #Hk, Hu, Hlt⟩
  iframe Hrd
  iexists L
  iframe Hu
  iintro Hrd Hu
  iunfold mPreRest
  iframe Hw Hrd Hb
  iunfold leasesLive
  iexists L
  iframe Hk Hu Hlt

/-- The auth store's reader resource of `mPreRest`, lent out (as `kvOwn_rd`). -/
theorem mPreRest_rd (E : AEnv GF) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    mPreRest E log Pre Q Post ⊢ E.RD ∗ (E.RD -∗ mPreRest E log Pre Q Post) := by
  iintro H
  iunfold mPreRest at H
  icases H with ⟨Hw, Hll, Hrd, Hb⟩
  iframe Hrd
  iintro Hrd
  iunfold mPreRest
  iframe

/-- The auth store's reader resource of `mPreWRest`, lent out. -/
theorem mPreWRest_rd (E : AEnv GF) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    mPreWRest E log Pre Q Post ⊢ E.RD ∗ (E.RD -∗ mPreWRest E log Pre Q Post) := by
  iintro H
  iunfold mPreWRest at H
  icases H with ⟨Hw, Hll, Hrd, Hb⟩
  iframe Hrd
  iintro Hrd
  iunfold mPreWRest
  iframe

/-- **A rejection of a writing method** from `mPreWRest`. -/
theorem mPreWRest_reject (E : AEnv GF) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    mPreWRest E log Pre Q Post ⊢ kvOwn E log ∗ Pre ∗ bkRTOf E := by
  iintro H
  iunfold mPreWRest at H
  icases H with ⟨Hw, Hll, Hrd, %B, Hbk, Hhk, Htie, -, Hrt, Hcs⟩
  icases bkRTOf_intro E B $$ [$Htie $Hrt] with ⟨Htie, Hrt⟩
  iunfold srvApi.csContractA at Hcs
  icases Hcs with ⟨HPre, -, -⟩
  iframe HPre
  isplitr [Hrt]
  · iunfold kvOwn
    iframe Hw Hll Hrd
    iunfold kvBk
    iexists B
    iframe
  · iexact Hrt

/-- **`mPreV` without the chain's resources** (as `mPreRest`). -/
def mPreVRest (v3 : Bool) (E : AEnv GF) (log : mvcc.Log) (Pre Q Post : IProp GF) : IProp GF :=
  iprop((∃ cr : Int, srvApi.wSt E.γs log cr) ∗ leasesLive E (mvcc.stateAfter log) ∗ E.RD ∗
    ∃ B : mvcc.KBReal, mvccBackend E.γ 1 B (E.Pk B) ∗ hookIs B E.f ∗ E.BkTie B ∗ bkWT B ∗ bkRT B ∗
      cPre v3 (E.Pk B) E.f Pre Q Post)

theorem mPreV_split_chain (v3 : Bool) (E : AEnv GF) (c : Chain) (a : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    mPreV v3 E c a info log Pre Q Post ⊢ mPreVRest v3 E log Pre Q Post ∗ chainRes c a info := by
  iintro H
  iunfold mPreV at H
  icases H with ⟨Hw, Hll, Hrd, Hres, Hb⟩
  iunfold mPreVRest
  iframe

theorem mPreV_of_rest (v3 : Bool) (E : AEnv GF) (c : Chain) (a : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    mPreVRest v3 E log Pre Q Post ∗ chainRes c a info ⊢ mPreV v3 E c a info log Pre Q Post := by
  iintro ⟨H, Hres⟩
  iunfold mPreVRest at H
  icases H with ⟨Hw, Hll, Hrd, Hb⟩
  iunfold mPreV
  iframe

/-! ### `kvOwnPre` (`uberApplier.dispatch`'s and `Apply`'s resources), split per method -/

/-- `kvOwnPre` is `mPreV`'s rest (the same resources). -/
theorem kvOwnPre_eq_rest (v3 : Bool) (E : AEnv GF) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    kvOwnPre v3 E log Pre Q Post = mPreVRest v3 E log Pre Q Post := rfl

/-- **For a cluster method**: `mPreV` from `kvOwnPre` and the chain's resources. -/
theorem kvOwnPre_mPreV (v3 : Bool) (E : AEnv GF) (c : Chain) (a : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    kvOwnPre v3 E log Pre Q Post ∗ chainRes c a info ⊢ mPreV v3 E c a info log Pre Q Post := by
  rw [kvOwnPre_eq_rest]; exact mPreV_of_rest v3 E c a info log Pre Q Post

/-- **For a method that does not write** (a read, `AuthStatus`, a request with nothing to do):
the thread's KV resources, the reader token, and `Pre` (the contract unused; the write-back token
dropped). -/
theorem kvOwnPre_kvOwn (v3 : Bool) (E : AEnv GF) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    kvOwnPre v3 E log Pre Q Post ⊢ kvOwn E log ∗ bkRTOf E ∗ Pre := by
  iintro H
  iunfold kvOwnPre at H
  icases H with ⟨Hw, Hll, Hrd, %B, Hbk, Hhk, Htie, -, Hrt, Hc⟩
  icases bkRTOf_intro E B $$ [$Htie $Hrt] with ⟨Htie, Hrt⟩
  isplitl [Hw Hll Hrd Hbk Hhk Htie]
  · iunfold kvOwn
    iframe Hw Hll Hrd
    iunfold kvBk
    iexists B
    iframe Hbk Hhk Htie
  isplitl [Hrt]
  · iexact Hrt
  iapply cPre_pre; iexact Hc

/-- **For a KV method that writes through the store** (`Put`, `DeleteRange`, `Txn`,
`Compaction`): `mPre` from `kvOwnPre true` and the chain's resources, the reader token aside (the
write-back token dropped: the store's own write takes none). -/
theorem kvOwnPre_mPre (E : AEnv GF) (c : Chain) (a : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    kvOwnPre true E log Pre Q Post ∗ chainRes c a info ⊢
      mPre E c a info log Pre Q Post ∗ bkRTOf E := by
  iintro ⟨H, Hres⟩
  iunfold kvOwnPre at H
  icases H with ⟨Hw, Hll, Hrd, %B, Hbk, Hhk, Htie, -, Hrt, Hc⟩
  icases bkRTOf_intro E B $$ [$Htie $Hrt] with ⟨Htie, Hrt⟩
  isplitr [Hrt]
  · iunfold mPre
    iframe Hw Hll Hrd Hres
    iexists B
    iframe Hbk Hhk Htie
    simp only [cPre, ↓reduceIte]
    iexact Hc
  iexact Hrt

/-- **For a method whose component writes the backend** (the merge of `lean`, 2026-11-06: the
lessor's grant, `grantPre`): `mPreW` from `kvOwnPre true` and the chain's resources. -/
theorem kvOwnPre_mPreW (E : AEnv GF) (c : Chain) (a : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    kvOwnPre true E log Pre Q Post ∗ chainRes c a info ⊢ mPreW E c a info log Pre Q Post := by
  iintro ⟨H, Hres⟩
  iunfold kvOwnPre at H
  icases H with ⟨Hw, Hll, Hrd, %B, Hbk, Hhk, Htie, Hwt, Hrt, Hc⟩
  iunfold mPreW
  iframe Hw Hll Hrd Hres
  iexists B
  iframe Hbk Hhk Htie Hwt Hrt
  simp only [cPre, ↓reduceIte]
  iexact Hc

/-- **`kvOwnPre` lends the auth store's reader resource** (`uberApplier.Apply`'s `rdLend`, as
`rdLend_kvOwn`). -/
theorem rdLend_kvOwnPre (v3 : Bool) (E : AEnv GF) (X : IProp GF) (log : mvcc.Log)
    (Pre Q Post Y : IProp GF) :
    ⊢ rdLend E iprop(X ∗ kvOwnPre v3 E log Pre Q Post ∗ Y) := by
  unfold rdLend
  iintro !> ⟨HX, Hkv, HY⟩
  iunfold kvOwnPre at Hkv
  icases Hkv with ⟨Hw, Hll, Hrd, Hb⟩
  iframe Hrd
  iintro Hrd
  iframe HX HY
  iunfold kvOwnPre
  iframe

end lemmas

end apply
end EtcdGrove
end Perennial
