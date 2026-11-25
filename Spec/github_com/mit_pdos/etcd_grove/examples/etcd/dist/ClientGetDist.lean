/-
`cli.Get(ctx, key)` by `New`'s client of a member at another machine, at the member's published view
(`notes/putget-dist-plan.md` §12; a trust-boundary axiom until #24's S2:
`Proof/.../etcd/dist/ClientGetDist.lean`). Lean-first (no Rocq counterpart).
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

/-- **`cli.Get(ctx, key)` by `New`'s client of a member at another machine, at its published view,
after the put fired** (`client.client_Get_own` with `kvRegsAt` replaced by the address fact and the
published view; the client dials with no proxy, `clientNoProxy`): `nil` and a reply whose first
key-value's value is `val`; or an error. -/
abbrev Client_Get_dist.spec : Prop :=
  ∀ [π : NetProtoGS] (cl : Loc) (ep : GoString) (V : WEnv GF) (γE : GName) (mid : w64)
    (ν : EnvView) (γr : ReadNames) (γf : GName) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key val : GoString) (sl : GoSlice),
  opSizeOk (opGetModel key []) →
  γr.kv.st = ν.st →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isNewClient cl [ep] V ∗
      clientNoProxy cl ∗
      etcdAddrAt (Gg := hG.goose_globalGS) ep γE mid ∗ envAt (Gg := hG.goose_globalGS) γE ν ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
      putGetInv γr γf key val ∗ monoNatLbOwn γf 1 }}
    (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
        go!"Get")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ m : RangeRespM, rangeRespMsg resp m ∗
          ⌜m.kvs.head?.map EtcdKv.value = some val⌝) ∨
        ⌜err ≠ GoInterface.nil ∧ resp = null⌝ }}

end spec

end etcd_dist
end EtcdGrove
end Perennial
