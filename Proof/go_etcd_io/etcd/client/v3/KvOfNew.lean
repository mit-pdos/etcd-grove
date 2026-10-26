/-
**`New`'s client is a client of etcd's KV** (`isKv`, D44; 2026-10-26). Lean-first (no Rocq
counterpart).

The step between a started server and a program above the KV's API: the program's proof sees
`isKv api γk dup` (with the client's `KV` field), never the members. `isKv_of_newClient`: `New`'s
client of the endpoint `ep` (`isNewClient`), the KV methods registered there by the member's
server (`kvRegsAt`, what the server's start gives), at the KV `γk`'s state name, a client that
sends a write at most once (`clientWriteOnce`: the endpoint never refuses a request), the store's
receipts bounded: its `KV` field is a client of `γk` that sends a write at most once.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.KVService
public import Proof.go_etcd_io.etcd.client.v3.InvClientNewResult
public import Proof.go_etcd_io.etcd.client.v3.InvServerKV

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proofs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **`New`'s client is a client of etcd's KV** (see the file header). -/
theorem isKv_of_newClient (cl : Loc) (ep : GoString) (V : WEnv GF) (E : apply.AEnv GF)
    (γr : ReadNames) (cid mid : w64) (γk : KVNames) (hst : γr.kv.st = γk.st)
    (hrb : receiptBound GF ≤ 2 ^ 62) :
    isNewClient cl [ep] V ∗ clientWriteOnce cl [ep] ∗
        kvRegsAt (⟨ep, E, γr, cid, mid⟩ : SrvAt GF) ⊢
      |==> ∃ api : Loc,
        structFieldRef go_etcd_io.etcd.client.v3.Client go!"KV" cl ↦□
          GoInterface.ok (kvIfaceOf api) ∗ isKv api γk false := by
  iintro ⟨#Hnc, #Hwo, #Hreg⟩
  iunfold clientWriteOnce at Hwo
  icases Hwo with %Hwo
  iunfold isNewClient at Hnc
  icases Hnc with ⟨-, -, ⟨%api, #Hkvf, #Hkv⟩, -⟩
  imod (srvStart_alloc (GF := GF) [(⟨ep, E, γr, cid, mid⟩ : SrvAt GF)]) with #Hs
  imodintro
  iexists api
  isplitr
  · iExactEq Hkvf; rfl
  iapply (isKv_intro api γk false [(⟨ep, E, γr, cid, mid⟩ : SrvAt GF)]
    (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact hst)
    (fun _ x hx => by simp only [List.mem_singleton] at hx; subst hx; exact Hwo ep (by simp)) hrb)
  iframe #
  isplitr
  · iExactEq Hkv; rfl
  unfold kvRegs
  iapply BigSepL.bigSepL_singleton.2
  iexact Hreg

end proofs

end client
end EtcdGrove
end Perennial
