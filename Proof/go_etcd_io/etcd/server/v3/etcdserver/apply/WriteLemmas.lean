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
open mvcc.api (BkRef mvccBackend hookIs)

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **The thread's KV resources but the writer's half and the tie**, at the backend `B`: the
backend's whole share and its hook, the live leases, the auth store's reader resource. -/
def kvRest (E : AEnv GF) (log : mvcc.Log) (B : BkRef) : IProp GF :=
  iprop(mvccBackend E.γ 1 B (E.Pk B) ∗ hookIs B E.f ∗ leasesLive E.γ (mvcc.stateAfter log) ∗ E.RD)

/-- `mPreW`, split (see the file header). -/
theorem mPreW_split (E : AEnv GF) (c : Chain) (a : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    mPreW E c a info log Pre Q Post ⊢ ∃ (cr : Int) (B : BkRef), srvApi.wSt E.γs log cr ∗
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
theorem kvOwn_of_split (E : AEnv GF) (log : mvcc.Log) (B : BkRef) (cr : Int) :
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
    (B : BkRef) (cr : Int) :
    srvApi.wSt E.γs log cr ∗ E.BkTie B ∗ kvRest E log B ∗ (Post ∨ Pre) ∗ bkRT B ⊢
      mPostW E .backend a log Pre Post := by
  iintro ⟨Hw, Htie, Hr, HPP, Hrt⟩
  iunfold mPostW
  isplitr [Hrt]
  · iapply mPost_backend
    iframe HPP
    iapply kvOwn_of_split E log B cr
    iframe Hw Htie Hr
  · iexists B; iexact Hrt

/-- `mPreV` (the cluster methods', with `v3`), split as `mPreW`. -/
theorem mPreV_split (v3 : Bool) (E : AEnv GF) (c : Chain) (a : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    mPreV v3 E c a info log Pre Q Post ⊢ ∃ (cr : Int) (B : BkRef), srvApi.wSt E.γs log cr ∗
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
    (B : BkRef) (cr : Int) :
    srvApi.wSt E.γs log cr ∗ E.BkTie B ∗ kvRest E log B ∗ chainRes c a info ∗
      cPost v3 Pre Post ∗ bkRT B ⊢ mPostV v3 E c a info log Pre Post := by
  iintro ⟨Hw, Htie, Hr, Hres, HPP, Hrt⟩
  iunfold mPostV
  iframe Hres HPP
  isplitl [Hw Htie Hr]
  · iapply kvOwn_of_split E log B cr
    iframe Hw Htie Hr
  · iexists B; iexact Hrt

end lemmas

end apply
end EtcdGrove
end Perennial
