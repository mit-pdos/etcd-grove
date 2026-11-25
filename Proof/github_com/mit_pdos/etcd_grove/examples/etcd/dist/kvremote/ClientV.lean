/-
# The kv client machine's client facts at the cluster view

`kvClientV svc cl api eps V Γ` (N2's drafts, `dist/ClientViewDist.lean`), what `Call_dist.spec` takes,
from what a client machine holds after `etcdstart.NewClients eps`: `New`'s client (`isNewClient`, which
already names its `KV` field's `*kv`), no proxy (`clientNoProxy`), and every endpoint a member of the
view (`membersAtV`, the start's share). So the `KV` field pointer is not a premise of its own: it is
`isNewClient`'s.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.ClientViewDist

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist
namespace view

open Iris Iris.BI Iris.ProofMode Net client

section kv
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **A client machine's client is a client of the view**: `isNewClient`'s `KV` field gives `api`. -/
theorem kvClientV_intro (svc : DistView → w64 → GrpcSvc GF) [π : NetProtoGS] (cl : Loc)
    (eps : List GoString) (V : WEnv GF) (Γ : DistView) :
    isNewClient cl eps V ∗ clientNoProxy cl ∗ membersAtV (Gg := hG.goose_globalGS) svc eps Γ ⊢
      ∃ api : Loc, kvClientV svc cl api eps V Γ := by
  iintro ⟨#Hn, #Hnp, #Hm⟩
  ihave #Hn' := Hn
  iunfold isNewClient at Hn'
  icases Hn' with ⟨-, -, ⟨%api, #Hf, -⟩, -⟩
  iexists api
  unfold kvClientV
  iframe #

end kv

end view
end etcd_dist
end EtcdGrove
end Perennial
