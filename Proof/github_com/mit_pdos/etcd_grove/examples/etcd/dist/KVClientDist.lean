/- Lean-first (no Rocq counterpart).

# What the clientv3 KV contracts across machines take of the client (`notes/etcd-dist-plan.md` §18.4)

`kvClientAt cl api eps V Γ`: `New`'s client `cl` of the endpoints `eps` (no proxy dial path), its `KV`
field the `*kv` `api`, every endpoint serving a member of the cluster view `Γ` (`membersAt`). The
precondition every interim KV contract (`KV_Put_dist`, `KV_Get_dist`, `KV_Delete_dist`, `KV_Compact_dist`,
`Txn_Commit_dist`) shares; `kvClient_of_new` builds it from `New`'s result.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.S2Interim
public import Proof.go_etcd_io.etcd.client.v3.InvClientNewResult
public import Proof.go_etcd_io.etcd.client.v3.InvClientNew

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProofMode Net client

section kv
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **What every KV contract across machines takes of the client** (persistent; see the file header). -/
def kvClientAt [π : NetProtoGS] (cl api : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView) :
    IProp GF :=
  iprop(isNewClient cl eps V ∗ clientNoProxy cl ∗
    clientF cl go!"KV" ↦□ interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty) #api ∗
    membersAt (Gg := hG.goose_globalGS) eps Γ)

instance kvClientAt_persistent [π : NetProtoGS] (cl api : Loc) (eps : List GoString) (V : WEnv GF)
    (Γ : DistView) : Persistent (kvClientAt cl api eps V Γ) := by
  unfold kvClientAt; infer_instance

/-- **`New`'s client of endpoints serving the view, with no proxy dial path, is a KV client of it**:
`isNewClient` names its `KV` field's `*kv`. -/
theorem kvClient_of_new [π : NetProtoGS] (cl : Loc) (eps : List GoString) (V : WEnv GF)
    (Γ : DistView) :
    isNewClient cl eps V ∗ clientNoProxy cl ∗ membersAt (Gg := hG.goose_globalGS) eps Γ ⊢
      ∃ api : Loc, kvClientAt cl api eps V Γ := by
  iintro ⟨#Hcl, #Hnp, #Hms⟩
  ihave #Hcl' := Hcl
  iunfold isNewClient at Hcl'
  icases Hcl' with ⟨-, -, ⟨%api, #Hkvf, -⟩, -⟩
  iexists api
  iunfold kvClientAt
  iframe #

end kv

end etcd_dist
end EtcdGrove
end Perennial

end
