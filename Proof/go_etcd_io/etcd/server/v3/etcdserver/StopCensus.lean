/-
**The census (gap 4) over mvcc's API: the backend's whole open token at the shutdown** (the `lean`
merge, 2026-11-06, the reader tokens; `notes/decisions.md`, "mvcc's API: the store's readers as
client-held tokens"). Lean-first (no Rocq counterpart).

On `lean` the census retired every store reader (`mvcc.storeReaders_retire`) and gave
`backend.Close` the stock's shares of the open token with what `kv.Close` returned
(`mvcc.wsCloseRes`). Over the API: `kv.Close` posts `mvccClosed γ`; with every reader token
(`mvccReaders γ mvccReaderN`: no read of the store in flight) and a share of the store's backend,
`mvccClosed_rest.law` gives the storage's rest, at etcd's backend `rdStockN - 2` shares of the open
token (`etcdStorage_rest`); the server adds its own: the two counted slots `etcdStorage_open.law`
handed it (the apply thread's and the storage-version monitor's backend readers, each
`rdTok ∗ bOpen rdOpen`), the constructors' half and the client pool's and auth store's shares
(`backend.bOpen_one_pool`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.EtcdBackend
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BackendBridge
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.RdPool

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section census
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The census at the open shares** (gap 4, as `NewServer`'s error path R-D1; the reader tokens,
2026-11-06; R6, 2026-11-07, at the shares themselves): the open shares of the server's two counted
reader slots of the backend `d`, the constructors' half and the pool's and auth store's shares of
the open token make, with the closed store (`kv.Close`'s post), every reader token and a share of
the store's backend, the whole open token: `backend.Close`'s precondition; the share given back
(for the stopped backend's image, `mvccImage_stop.law`). -/
theorem stop_census_open (hCR : mvcc.api.mvccClosed_rest.law (GF := GF)) (γ : mvcc.api.MvccName)
    (d : mvcc.KBReal) (q : Qp) (Pk : IProp GF) :
    backend.bOpen (GF := GF) d.γB backend.rdOpen ∗ backend.bOpen d.γB backend.rdOpen ∗
      backend.bOpen d.γB (1 : Qp).half ∗
      ([∗list] _x ∈ List.replicate (backend.rdPoolN + backend.authRdN) (),
        backend.bOpen d.γB backend.rdOpen) ⊢
    (mvcc.api.mvccClosed γ ∗ mvcc.api.mvccReaders γ mvcc.api.mvccReaderN ∗
        mvcc.api.mvccBackend γ q (mvcc.api.etcdStorage d) Pk ={⊤}=∗
      backend.bOpen d.γB 1 ∗ mvcc.api.mvccBackend γ q (mvcc.api.etcdStorage d) Pk) := by
  have hR := hCR γ q (mvcc.api.etcdStorage d) Pk
  rw [mvcc.api.etcdStorage_rest] at hR
  have hN : backend.rdStockN - 2 + 1 + 1 = backend.rdStockN := by
    rw [backend.rdStockN_val]
  iintro ⟨Ho1, Ho2, Hhalf, Hpool⟩ Hcl
  imod hR $$ Hcl with ⟨Hrest, Hmb⟩
  ihave Hst : [∗list] _x ∈ List.replicate (backend.rdStockN - 2 + 1 + 1) (),
      backend.bOpen d.γB backend.rdOpen $$ [Hrest Ho1 Ho2]
  · rw [List.replicate_succ', List.replicate_succ']
    iapply BigSepL.bigSepL_append.2
    isplitl [Hrest Ho1]
    · iapply BigSepL.bigSepL_append.2
      iframe Hrest
      iapply BigSepL.bigSepL_cons.2
      iframe Ho1
      iapply BigSepL.bigSepL_nil.2
      itrivial
    iapply BigSepL.bigSepL_cons.2
    iframe Ho2
    iapply BigSepL.bigSepL_nil.2
    itrivial
  rw [hN]
  imodintro
  iframe Hmb
  iapply (backend.bOpen_one_pool d.γB).2
  iframe Hhalf Hpool Hst

/-- **The census** (`stop_census_open` at the server's two counted slots, `bkRTx`, each with its
open share). -/
theorem stop_census (hCR : mvcc.api.mvccClosed_rest.law (GF := GF)) (γ : mvcc.api.MvccName)
    (d : mvcc.KBReal) (q : Qp) (Pk : IProp GF) :
    mvcc.bkRTx (GF := GF) d.γB d.P d.be ∗ mvcc.bkRTx d.γB d.P d.be ∗
      backend.bOpen d.γB (1 : Qp).half ∗
      ([∗list] _x ∈ List.replicate (backend.rdPoolN + backend.authRdN) (),
        backend.bOpen d.γB backend.rdOpen) ⊢
    (mvcc.api.mvccClosed γ ∗ mvcc.api.mvccReaders γ mvcc.api.mvccReaderN ∗
        mvcc.api.mvccBackend γ q (mvcc.api.etcdStorage d) Pk ={⊤}=∗
      backend.bOpen d.γB 1 ∗ mvcc.api.mvccBackend γ q (mvcc.api.etcdStorage d) Pk) := by
  iintro ⟨H1, H2, Hhalf, Hpool⟩
  iunfold mvcc.bkRTx at H1 H2
  icases H1 with ⟨-, Ho1⟩
  icases H2 with ⟨-, Ho2⟩
  iapply stop_census_open hCR γ d q Pk
  iframe Ho1 Ho2 Hhalf Hpool

end census

end EtcdGrove
end Perennial
