/- Lean-first (no Rocq counterpart).

# What the clientv3 watch contracts across machines take of the client (`notes/etcd-dist-plan.md` §22.3)

`watchClientAt cl w eps V Γ`: `New`'s client `cl` of the endpoints `eps` (no proxy dial path), its `Watcher`
field the `*watcher` `w`, every endpoint serving a member of the cluster view `Γ` (`membersAt`).
`kvClientAt`'s counterpart for the `Watcher` field (`KVClientDist.lean`); the precondition the interim watch
contracts (`Watch_dist`, `RequestProgress_dist`: `WatchDist.lean`) share. `watchClient_of_new` builds it
from `New`'s result, as `kvClient_of_new` builds `kvClientAt`.
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

section watch
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **What the watch contracts across machines take of the client** (persistent; see the file header):
`New`'s client `cl` of the endpoints `eps` (no proxy dial path), its `Watcher` field the `*watcher` `w`
(the one `isNewClient` names: the field is read-only, so `w` is unique), every endpoint serving a member
of the cluster view `Γ`. The watcher is over `New`'s environment restricted to the dialed endpoints
(`V.atEps eps`, `isNewClient`); the contracts' posts read nothing of it (`notes/etcd-dist-plan.md` §25). -/
def watchClientAt [π : NetProtoGS] (cl w : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView) :
    IProp GF :=
  iprop(isNewClient cl eps V ∗ clientNoProxy cl ∗
    clientF cl go!"Watcher" ↦□ GoInterface.ok (watcherIfaceOf w) ∗
    membersAt (Gg := hG.goose_globalGS) eps Γ)

instance watchClientAt_persistent [π : NetProtoGS] (cl w : Loc) (eps : List GoString) (V : WEnv GF)
    (Γ : DistView) : Persistent (watchClientAt cl w eps V Γ) := by
  unfold watchClientAt; infer_instance

/-- **`New`'s client of endpoints serving the view, with no proxy dial path, is a watch client of it**:
`isNewClient` names its `Watcher` field's `*watcher`. -/
theorem watchClient_of_new [π : NetProtoGS] (cl : Loc) (eps : List GoString) (V : WEnv GF)
    (Γ : DistView) :
    isNewClient cl eps V ∗ clientNoProxy cl ∗ membersAt (Gg := hG.goose_globalGS) eps Γ ⊢
      ∃ w : Loc, watchClientAt cl w eps V Γ := by
  iintro ⟨#Hcl, #Hnp, #Hms⟩
  ihave #Hcl' := Hcl
  iunfold isNewClient at Hcl'
  icases Hcl' with ⟨-, -, -, ⟨%w, %conn, %wc, %lg, %ics, #Hwf, -⟩, -⟩
  iexists w
  iunfold watchClientAt
  iframe #

end watch

end etcd_dist
end EtcdGrove
end Perennial

end
