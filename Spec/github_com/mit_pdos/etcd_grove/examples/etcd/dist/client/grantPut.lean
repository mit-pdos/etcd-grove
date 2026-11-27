/-
`grantPut(cli, k)` (`examples/etcd/dist/client/authlease.go`; authlease's, copied): a lease of TTL `maxLeaseTTL`
granted through `cli`, then `k` put with it, each in a context with the request timeout. Auth on, revocable mode,
at the cluster view: the grant over `etcd_dist.authd.Lease_GrantOn_dist` at the member `mid` the client's one
endpoint serves, the put over `KV_PutOn_dist`. As the single-process `etcd_authlease.grantPut.spec`, the caller's
updates are persistent offers (`writeAuD`): the grant's at every id, and the put's handed over by the caller's
step at the granted id (from its `R`). On success: the lease (non-zero) is live at `Γ.ls mid`, the put's result
and its check (`writeCheckedD`: granted to the client's principal at the history after a requested prefix
extending `L₀`). Lean-first (no Rocq counterpart); F7 stage S4.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthLeaseDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Net client
open github_com.mit_pdos.etcd_grove.examples.etcd.dist
open etcd_dist etcd_dist.authd

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- The leased put `grantPut` makes: `k := "v"` with the lease `id`. -/
abbrev grantPutOp (k : GoString) (id : w64) : OpFull :=
  putWireOf (opPutModel k go!"v" [withLeaseM id])

/-- `grantPut(cli, k)`, auth on, revocable mode, `cli` a user client (`userCli`) of the endpoint `addr` serving
member `mid`: `(id, true)`, the lease `id` (non-zero) live at member `mid`'s lessor, the caller's `R' id` (its step
at the grant), the put's result `Qp id σ` and its check; or `false`. -/
abbrev grantPut.spec : Prop :=
  ∀ [π : NetProtoGS] (cl : Loc) (addr k : GoString) (V : WEnv GF) (Γ : DistView) (mid : w64)
    (cfg : go_etcd_io.etcd.client.v3.Config) (γR : ServerRaftNames) (L₀ : List EntryModel) (n₀ : Nat)
    (Qg Qp : w64 → KVState → IProp GF) (R : IProp GF) (R' : w64 → IProp GF),
  (∀ a b : w64, Γ.au a = Γ.au b → a = b) → (∀ a b : w64, Γ.ls a = Γ.ls b → a = b) →
  Γ.auth = true → Γ.kv.lm = .revocable → γR.raft.log = Γ.kv.rlog →
  (∀ id : w64, opSizeOk (opPutModel k go!"v" [withLeaseM id])) →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      levelTok 0 ∗ userCli cl addr V cfg ∗ etcdAddrAt (Gg := hG.goose_globalGS) addr Γ mid ∗
      srvReqLogLb γR L₀ ∗ auth.authPubLbM (.on (Γ.au mid)) n₀ ∗
      □ (∀ id : w64, writeAuD Γ.kv (principalOf cfg) (.leaseGrant id (W64 9000000000)) L₀ (Qg id)) ∗ R ∗
      (∀ id : w64, ⌜id ≠ W64 0⌝ -∗ (∃ σ, Qg id σ) -∗ R ={⊤}=∗ R' id ∗
        writeAuD Γ.kv (principalOf cfg) (.put (grantPutOp k id)) L₀ (Qp id)) }}
    (App (App (Val (@! client.grantPut)) (Val #cl)) (Val #k))
  {{ (id : w64) (ok : Bool), RET (PairV #id #ok); levelTok 0 ∗ (⌜ok = false⌝ ∨
      (⌜ok = true ∧ id ≠ W64 0⌝ ∗ R' id ∗ (∃ σ, Qp id σ) ∗
        (∃ (i : Nat) (l : Loc), lease.leaseLiveFrom (Γ.ls mid) i id l) ∗
        writeCheckedD [addr] Γ γR (principalOf cfg) (irrPut (grantPutOp k id)) L₀)) }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
