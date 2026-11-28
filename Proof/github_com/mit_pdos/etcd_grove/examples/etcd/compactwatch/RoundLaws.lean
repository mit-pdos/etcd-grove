/-
**`client_Get_rev`, as a hypothesis** (the import tiers, 2026-11-18): `RoundCalls.lean`'s statement
as `client_Get_rev.law : Prop`, which `checkCompactRev`'s proof takes instead of importing
`RoundCalls`; `client_Get_rev_law_holds` proves it, and `MainLinked` passes it.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.compactwatch.Rounds

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_compactwatch

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver
  client

section laws1
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `client_Get_rev`'s statement (`RoundCalls.lean`, a linking module), as a hypothesis of the
proofs that use it (the import tiers); `client_Get_rev_law_holds` proves it. -/
abbrev client_Get_rev.law : Prop :=
  ∀ (cl : Loc) (ep : GoString) (V : WEnv GF) (E : apply.AEnv GF) (γr : ReadNames) (γf γl γv : GName)
      (keys : List GoString) (val : GoString) (k : GoString) (r : Nat) (c cid mid : w64)
      (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (sl : GoSlice) (F : mvcc.Log)
      (hsz : opSizeOk (opGetModel k [])),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗ (isNewClient cl [ep] V ∗
          kvRegsAt (⟨ep, E, γr, cid, mid⟩ : SrvAt GF) ∗
          ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗ committedAtLeast γr c ∗
          roundsInv γr γf γl γv keys val ∗ monoNatLbOwn γv r ∗ srvApi.kvLogLb E.γs F) }}
        (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
            go!"Get")) (Val #(GoInterface.ok ci))) (Val #k)) (Val #sl))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ ((⌜err = GoInterface.nil⌝ ∗ ∃ m : RangeRespM, rangeRespMsg resp m ∗
              ⌜(r : Int) ≤ sint.Z m.hdr.revision⌝) ∨
            ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

end laws1

end etcd_compactwatch
end EtcdGrove
end Perennial
