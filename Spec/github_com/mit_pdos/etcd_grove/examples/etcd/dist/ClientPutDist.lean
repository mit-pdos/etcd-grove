/-
`cli.Put(ctx, key, val)` by `New`'s client of a member at another machine, the client's first call
(`notes/putget-dist-plan.md` §12; a trust-boundary axiom until #24's S2:
`Proof/.../etcd/dist/ClientPutDist.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.S2Interim
public import Proof.go_etcd_io.etcd.client.v3.InvClientNewResult
public import Proof.go_etcd_io.etcd.client.v3.InvKVConn
public import Proof.go_etcd_io.etcd.client.v3.InvOp

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Net client go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **`cli.Put(ctx, key, val)` by `New`'s client of a member at another machine, before the client
knows the member's view** (the pub form of `client.client_Put_own`): a client that dials with no
proxy (`clientNoProxy`, `etcdstart.NewClient`'s post) of an address set to serve etcd's KV calls
(`etcdAddrAt`); the caller gives, for every view published at `γE`, a putget invariant at read
names whose KV state variable is the view's, under a later (review F2: the caller reads it out of the
publication invariant, `envAt_pub`); and it lends its level-0 token (`levelTok 0`, given back, as
`client_Put_own`). On `nil`, a view published at `γE`, such an invariant and the put's flag. -/
abbrev Client_Put_dist.spec : Prop :=
  ∀ [π : NetProtoGS] (cl : Loc) (ep : GoString) (V : WEnv GF) (γE : GName) (mid : w64)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (key val : GoString)
    (sl : GoSlice),
  opSizeOk (opPutModel key val []) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      isNewClient cl [ep] V ∗
      clientNoProxy cl ∗ etcdAddrAt (Gg := hG.goose_globalGS) ep γE mid ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
      □ (∀ ν : EnvView, envAt (Gg := hG.goose_globalGS) γE ν ={⊤}=∗
          ▷ ∃ (γr : ReadNames) (γf : GName), ⌜γr.kv.st = ν.st⌝ ∗ putGetInv γr γf key val) }}
    (App (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
        go!"Put")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #val)) (Val #sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ (
      (⌜err = GoInterface.nil⌝ ∗ ∃ (ν : EnvView) (γr : ReadNames) (γf : GName),
          envAt (Gg := hG.goose_globalGS) γE ν ∗ ⌜γr.kv.st = ν.st⌝ ∗
          putGetInv γr γf key val ∗ monoNatLbOwn γf 1) ∨
        ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

end spec

end etcd_dist
end EtcdGrove
end Perennial
