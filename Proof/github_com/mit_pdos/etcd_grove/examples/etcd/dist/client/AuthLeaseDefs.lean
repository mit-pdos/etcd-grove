/-
The vocabulary of the dist authLease workload's helpers (`examples/etcd/dist/client/{authlease,auth}.go`; F7
stage S4, `notes/etcd-dist-f7.md`, "Handoff S3-1", item 2). Lean-first (no Rocq counterpart).

- `reqMd who`: the outgoing metadata of `reqCtx(who)`'s context (the bad principal's `token: badtoken`, no
  metadata otherwise); `outTokOk_reqMd`: it is admitted by the auth-on contracts (`outTokOk`) for an anonymous
  principal, and for any principal when `who ≠ "bad"`.
- `userCli cl addr V cfg`: what `newUserClient(addr, ...)` returns: `New`'s client of the one endpoint `addr`, with
  no proxy, its configuration `cfg` read-only (no preset token); `userClientAt_of_userCli`,
  `leaseUserAt_of_userCli`: the auth-on contracts' client facts from it, at the member the caller names.
- `barrierFloor Γ γR L₀ addr`: what `barrier(addr)` leaves: the member `addr` serves and its `authFloorD`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.AuthViewDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.ClientAuth
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.LeaseDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Net client
open etcd_dist etcd_dist.authd

/-- The outgoing metadata of `reqCtx(who)`'s context: the bad principal's carries `token: badtoken`,
every other none. -/
def reqMd [GooseExts] (who : GoString) : Option (GoString → Option (List GoString)) :=
  if who = go!"bad" then metadata.mdAdd none go!"token" etcd_auth.badToken else none

/-- **`reqCtx`'s metadata is admitted by the auth-on contracts**: no token for every principal but the
bad one, whose `badtoken` has no simple token's shape (`etcd_auth.simpleTok_ne_badToken`), admitted for an
anonymous principal. -/
theorem outTokOk_reqMd [GooseExts] (P : Option GoString) (who : GoString)
    (h : who = go!"bad" → P = none) : outTokOk P (reqMd who) := by
  unfold reqMd
  by_cases hw : who = go!"bad"
  · rw [if_pos hw]
    right
    refine ⟨h hw, ?_⟩
    intro t ht hsh
    rw [metadata.mdVals_mdAdd] at ht
    simp only [metadata.mdVals, Option.bind_none, Option.getD_none, List.nil_append,
      List.mem_singleton] at ht
    subst ht
    obtain ⟨pre, idx, he, -⟩ := hsh
    exact etcd_auth.simpleTok_ne_badToken pre idx he.symm
  · rw [if_neg hw]
    left
    rfl

section client
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

open Iris.ProofMode

/-- **A user client of one endpoint** (persistent; `newUserClient`'s result): `New`'s client of `[addr]`,
dialing with no proxy, its configuration `cfg` (read-only), with no preset token. -/
def userCli (cl : Loc) (addr : GoString) (V : WEnv GF) (cfg : go_etcd_io.etcd.client.v3.Config) :
    IProp GF :=
  iprop(isNewClient cl [addr] V ∗ clientNoProxy cl ∗ clientF cl go!"cfg" ↦□ cfg ∗ ⌜cfg.Token' = []⌝)

instance userCli_persistent (cl : Loc) (addr : GoString) (V : WEnv GF)
    (cfg : go_etcd_io.etcd.client.v3.Config) : Persistent (userCli cl addr V cfg) := by
  unfold userCli; infer_instance

instance userClientAt_persistent [π : NetProtoGS] (cl api : Loc) (eps : List GoString) (V : WEnv GF)
    (Γ : DistView) (cfg : go_etcd_io.etcd.client.v3.Config) :
    Persistent (userClientAt cl api eps V Γ cfg) := by
  unfold userClientAt; infer_instance

instance leaseUserAt_persistent [π : NetProtoGS] (cl lp : Loc) (ep : GoString) (V : WEnv GF)
    (Γ : DistView) (mid : w64) (cfg : go_etcd_io.etcd.client.v3.Config) :
    Persistent (leaseUserAt cl lp ep V Γ mid cfg) := by
  unfold leaseUserAt; infer_instance

instance writeAuD_persistent (γk : KVNames) (P : Option GoString) (op : KVOp) (L₀ : List EntryModel)
    (Q : KVState → IProp GF) : Persistent (writeAuD γk P op L₀ Q) := by
  unfold writeAuD; infer_instance

instance servedBy_persistent [π : NetProtoGS] (eps : List GoString) (Γ : DistView) (mid : w64) :
    Persistent (servedBy (GF := GF) eps Γ mid) := by
  unfold servedBy; infer_instance

instance writeCheckedD_persistent [π : NetProtoGS] (eps : List GoString) (Γ : DistView)
    (γR : ServerRaftNames) (P : Option GoString) (rq : apply.IRRModel) (L₀ : List EntryModel) :
    Persistent (writeCheckedD (GF := GF) eps Γ γR P rq L₀) := by
  unfold writeCheckedD; infer_instance

instance authFloorD_persistent (Γ : DistView) (γR : ServerRaftNames) (mid : w64)
    (L₀ : List EntryModel) (m : Nat) : Persistent (authFloorD (GF := GF) Γ γR mid L₀ m) := by
  unfold authFloorD; infer_instance

/-- A user client of an endpoint serving the view is an auth-on KV client of it. -/
theorem userClientAt_of_userCli [π : NetProtoGS] (cl : Loc) (addr : GoString) (V : WEnv GF)
    (cfg : go_etcd_io.etcd.client.v3.Config) (Γ : DistView) :
    userCli cl addr V cfg ∗ membersAt (Gg := hG.goose_globalGS) [addr] Γ ⊢
      ∃ api : Loc, userClientAt cl api [addr] V Γ cfg := by
  iintro ⟨#Hu, #Hms⟩
  iunfold userCli at Hu
  icases Hu with ⟨#Hnc, #Hnp, #Hcfg, %Htok⟩
  ihave ⟨%api, #Hkv⟩ := etcd_dist.kvClient_of_new cl [addr] V Γ $$ [Hnc Hnp Hms]
  · iframe #
  iexists api
  iunfold userClientAt
  iframe #
  ipureintro; exact Htok

/-- A user client of an endpoint serving member `mid` is an auth-on lease client of `mid`. -/
theorem leaseUserAt_of_userCli [π : NetProtoGS] (cl : Loc) (addr : GoString) (V : WEnv GF)
    (cfg : go_etcd_io.etcd.client.v3.Config) (Γ : DistView) (mid : w64) :
    userCli cl addr V cfg ∗ etcdAddrAt (Gg := hG.goose_globalGS) addr Γ mid ⊢
      ∃ lp : Loc, leaseUserAt cl lp addr V Γ mid cfg := by
  iintro ⟨#Hu, #Ha⟩
  iunfold userCli at Hu
  icases Hu with ⟨#Hnc, #Hnp, #Hcfg, %Htok⟩
  ihave #Hnc' := Hnc
  iunfold isNewClient at Hnc'
  icases Hnc' with ⟨-, -, -, -, ⟨%lp, #Hlf, -⟩, -⟩
  iexists lp
  iunfold leaseUserAt
  iunfold view.leaseClientAt
  iframe #
  ipureintro; exact Htok

/-- **What a barrier at `addr` leaves** (persistent): `addr` serves a member `mid` of the view, whose published
auth index `m` is at least a state of the history after a requested prefix extending `L₀` (`authFloorD`). -/
def barrierFloor [π : NetProtoGS] (Γ : DistView) (γR : ServerRaftNames) (L₀ : List EntryModel)
    (addr : GoString) : IProp GF :=
  iprop(∃ (mid : w64) (m : Nat), etcdAddrAt (Gg := hG.goose_globalGS) addr Γ mid ∗ authFloorD Γ γR mid L₀ m)

instance barrierFloor_persistent [π : NetProtoGS] (Γ : DistView) (γR : ServerRaftNames)
    (L₀ : List EntryModel) (addr : GoString) : Persistent (barrierFloor (GF := GF) Γ γR L₀ addr) := by
  unfold barrierFloor; infer_instance

end client

end etcd_dist_client
end EtcdGrove
end Perennial
