/-
`absent(root, k, why)` (`examples/etcd/dist/client/authlease.go`; authlease's, copied): root's linearizable `Get`
of `k`; `false` on its error, `true` if it found no key, a panic if it found one. Auth on, at the cluster view,
over `etcd_dist.authd.KV_GetOn_dist` with the caller's read update `Q` (as the single-process
`etcd_authlease.absent.spec`): the caller shows that no state its update can be told has the key `k` (so the panic
is unreachable), and a `true` exposes the read's `□ Q σ`. Lean-first (no Rocq counterpart); F7 stage S4.
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

/-- `absent(root, k, why)`, auth on, `root` a user client (`userCli`) of the endpoint `addr` serving a member of
the view, with the caller's read update `Q` (none, `Q = True`, or an atomic update at `etcdKV Γ.kv`), every state
`Q` can hold of having no key `k`: no panic; `true` with the read's `□ Q σ`, or `false`. -/
abbrev absent.spec : Prop :=
  ∀ [π : NetProtoGS] (root : Loc) (addr k why : GoString) (V : WEnv GF) (Γ : DistView)
    (cfg : go_etcd_io.etcd.client.v3.Config) (γR : ServerRaftNames) (L₀ : List EntryModel)
    (Q : KVState → IProp GF),
  (∀ a b : w64, Γ.au a = Γ.au b → a = b) → Γ.auth = true → γR.raft.log = Γ.kv.rlog →
  opSizeOk (opGetModel k []) →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      levelTok 0 ∗ userCli root addr V cfg ∗ membersAt (Gg := hG.goose_globalGS) [addr] Γ ∗
      srvReqLogLb γR L₀ ∗
      □ (⌜Q = fun _ => iprop(True)⌝ ∨
        AU <{ ∃∃ (σ : KVState), etcdKV Γ.kv σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
        <{ etcdKV Γ.kv σ ∗ ⌜kvRoom σ⌝, COMM □ Q σ }>) ∗
      □ (∀ σ : KVState, □ Q σ -∗ ⌜∀ v ∈ σ.kvs, v.key ≠ k⌝) }}
    (App (App (App (Val (@! client.absent)) (Val #root)) (Val #k)) (Val #why))
  {{ (ok : Bool), RET #ok; levelTok 0 ∗ (⌜ok = false⌝ ∨ (⌜ok = true⌝ ∗ ∃ σ : KVState, □ Q σ)) }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
