/-
**M2, the storage side: the watch clients' side of F1, drafted** (`notes/m2-storage-plan.md`,
"After review round 1"; `notes/spec-first-study/m2-storage-review-1.md`, F1, the user's decision:
"no watchers in compaction mode" is a premise of the Watch stream's client-facing contract).
Imported by nothing; no `axiom`, no `sorry`.

A watch client presents the "no compactor" fact of each member it watches (`mvcc.crevFrozen` at the
member's store names): one more conjunct of the member's facts (`watchMemberFactsD`, in
`watchConnFactsD`, and in `watchAddrFactsD` for `NewWatcher`'s client), which its create requests
carry with their watch token (`v3rpc.watchUpD`, `watchUpD_create`). A client that never watches
(`putgetc`'s: `client.New` without `isNewClient_watcher`) owes nothing. The examples whose clients
watch (`watchkv`, `linkv3p`, `cachekv`) take the fact from `NewServer.spec`'s post, which gains
`mvcc.crevFrozen E.γ` (from `mvcc.isWatchableStoreD_frozen` at `cm = false`; the plan has the
text); a compacting server's post has none to give.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvClientNewResult
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.M2StorageDraft

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.client.v3 client
open go_etcd_io.etcd.cache.v3

section draft
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **Draft of `client.watchMemberFacts`** (F1): a member's facts gain its store's "no compactor"
fact, which the client's create requests carry. The rest as today. -/
def client.watchMemberFactsD (V : WEnv GF) : IProp GF :=
  iprop(mvcc.watchTokPool V.R.γ ∗ mvcc.crevFrozen V.R.γ.st ∗ srvLogsSmall V.R ∗
    ⌜V.R.γ.st = V.R.E.γ⌝ ∗ watchLaws V ∗ srvKVFacts V)

instance client.watchMemberFactsD_persistent (V : WEnv GF) :
    Persistent (client.watchMemberFactsD V) := by
  unfold client.watchMemberFactsD; infer_instance

/-- **Draft of `client.watchConnFacts`** (F1): each member's facts are `watchMemberFactsD`'s, and
the registered content is `v3rpc.watchUpD`. The rest as today. -/
def client.watchConnFactsD (V : WEnv GF) : IProp GF :=
  iprop(grpcConn V.conn V.addrs V.ics [] ∗
    isGrpcStreams (Req := v3rpc.pbWatchRequest) (Rep := v3rpc.pbWatchResponse) V.addrs
      go!"/etcdserverpb.Watch/Watch" (fun a => v3rpc.watchUpD (V.memOf a).γ)
      (fun a => v3rpc.watchSpec (V.memOf a)) ∗
    v3rpc.watchDescOk ∗ (□ ∀ i : Nat, ⌜i < V.nm⌝ -∗ client.watchMemberFactsD (V.atIdx i)) ∗
    eofOk ∗ errorsNewOk ∗ ctxErrClientAllW ∗ clientWatchVars ∗
    ⌜V.pfx ≠ [] ∧ V.addrs.Nodup ∧ ∃ i, i < V.nm ∧ V.mem i = (V.addr, V.R)⌝)

/-- **Draft of `watchAddrFacts`** (F1; `InvClientNewResult.lean`, what `isNewClient_watcher` adds):
the server's "no compactor" fact beside its watch-token pool, and the registered content
`v3rpc.watchUpD`. The rest as today. -/
def watchAddrFactsD (V : WEnv GF) : IProp GF :=
  iprop(isGrpcStream (Req := v3rpc.pbWatchRequest) (Rep := v3rpc.pbWatchResponse) V.addr
      go!"/etcdserverpb.Watch/Watch" (v3rpc.watchUpD V.R.γ) (v3rpc.watchSpec V.R) ∗
    mvcc.watchTokPool V.R.γ ∗ mvcc.crevFrozen V.R.γ.st ∗
    srvLogsSmall V.R ∗
    eofOk ∗ ⌜V.R.γ.st = V.R.E.γ ∧ V.pfx ≠ []⌝ ∗
    watchLaws V ∗
    srvKVFacts V)

/-- **A create request's content, from the member's facts** (F1; the client's three create sites in
`watchGRPCStream.run`, each with a token from the pool): a restricted create with a watch token is
`watchUpD`'s. -/
theorem client.watchUpD_create (V : WEnv GF) (i : Nat) (c : v3rpc.CreateReqM)
    (h : v3rpc.watchReqOk (.create c)) :
    client.watchMemberFactsD V ∗ mvcc.watchTok V.R.γ ⊢ v3rpc.watchUpD V.R.γ i (.create c) := by
  iintro ⟨#Hm, Ht⟩
  iunfold client.watchMemberFactsD at Hm
  icases Hm with ⟨-, #Hf, -⟩
  unfold v3rpc.watchUpD
  dsimp only
  iframe Ht Hf
  ipureintro; exact h

end draft

end EtcdGrove
end Perennial
