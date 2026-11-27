/-
**`client_Put_km`, as a hypothesis** (the import tiers, 2026-11-18): `WatchWritesLinked.lean`'s
statement as `client_Put_km.law : Prop`, which `writer`'s proof takes instead of importing
`WatchWritesLinked`; `client_Put_km_law_holds` proves it, and the `Link` passes it.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.partition.WatchWrites

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_partition

open Iris Iris.BI Iris.ProofMode Iris.Std go_etcd_io.etcd.server.v3.etcdserver
open go_etcd_io.etcd.api.v3 go_etcd_io.etcd.client.v3

section laws1
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- `client_Put_km`'s statement (`WatchWritesLinked.lean`, a linking module), as a hypothesis of the
proofs that use it (the import tiers); `client_Put_km_law_holds` proves it. -/
abbrev client_Put_km.law : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (cl : Loc) (ms : List (client.SrvAt GF))
      (V : client.WEnv GF) (γk : KVNames) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
      (key val : GoString) (sl : GoSlice) (Q : KVState → IProp GF)
      (hsz : opSizeOk (opPutModel key val [])),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗ (isNewClient cl (ms.map client.SrvAt.addr) V ∗
          client.clientWriteOnce cl (ms.map client.SrvAt.addr) ∗
          ([∗list] x ∈ ms, memberPut γk x) ∗
          ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
          kvOpAu1 γk (.put (client.putKeyOp key val)) Q) }}
        (App (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
            go!"Put")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #val)) (Val #sl))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : PutRespM) (σ : KVState), putRespMsg resp m ∗ Q σ ∗
            ⌜m.hdr.revision = W64 ((σ.rev + 1 : Nat) : Int) ∧ σ.compacted = 0 ∧ 1 ≤ σ.rev ∧
              σ.rev + 4 < 2 ^ 63⌝) ∨
            ⌜err ≠ GoInterface.nil⌝) }}

end laws1

end etcd_partition
end EtcdGrove
end Perennial
