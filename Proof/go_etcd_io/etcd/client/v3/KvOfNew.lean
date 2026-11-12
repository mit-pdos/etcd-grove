/-
**`New`'s client is a client of etcd's KV** (`isKv`, D44; 2026-10-26). Lean-first (no Rocq
counterpart).

The step between a started server and a program above the KV's API: the program's proof sees
`isKv api γk dup` (with the client's `KV` field), never the members. `isKv_of_newClient`: `New`'s
client of the members `ms`' endpoints (`isNewClient`; one member, or a cluster's members at their
bridges, K6 of `notes/k8s-compactor-plan.md`, 2026-11-05: until then one endpoint), the KV methods
registered at each by its member's server (`kvRegsAt`, what the server's start gives), each member
at names the same as the KV `γk`'s, a client that sends a write at most once (`clientWriteOnce`: no
endpoint refuses a request), the store's receipts bounded: its `KV` field is a client of `γk` that
sends a write at most once.
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **`New`'s client is a client of etcd's KV** (see the file header). -/
theorem isKv_of_newClient (cl : Loc) (ms : List (SrvAt GF)) (eps : List GoString) (V : WEnv GF)
    (γk : KVNames) (heps : ms.map SrvAt.addr = eps) (hst : ∀ x ∈ ms, kvSame x.γr.kv γk)
    (hrb : receiptBound GF ≤ 2 ^ 62) :
    isNewClient cl eps V ∗ clientWriteOnce cl eps ∗ ([∗list] x ∈ ms, kvRegsAt x) ⊢
      |==> ∃ api : Loc,
        structFieldRef go_etcd_io.etcd.client.v3.Client go!"KV" cl ↦□
          GoInterface.ok (kvIfaceOf api) ∗ isKv api γk false := by
  subst heps
  iintro ⟨#Hnc, #Hwo, #Hreg⟩
  iunfold clientWriteOnce at Hwo
  icases Hwo with %Hwo
  iunfold isNewClient at Hnc
  icases Hnc with ⟨-, -, ⟨%api, #Hkvf, #Hkv⟩, -⟩
  imod (srvStart_alloc (GF := GF) ms) with #Hs
  imodintro
  iexists api
  isplitr
  · iExactEq Hkvf; rfl
  iapply (isKv_intro api γk false ms hst
    (fun _ x hx => Hwo x.addr (List.mem_map_of_mem hx)) hrb)
  iframe #
  unfold kvRegs
  iexact Hreg

end proofs

end client
end EtcdGrove
end Perennial
