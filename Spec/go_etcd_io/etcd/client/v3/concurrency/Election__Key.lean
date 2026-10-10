/-
`concurrency.Election.Key()` (`client/v3/concurrency/election.go`). Lean-first (no Rocq counterpart); see
`InvElection.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvElection

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- **`e.Key()`**: `leaderKey`. -/
abbrev Election.Key.spec : Prop :=
  ∀ (e s : Loc) (st : ElectionSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ electionState e s st }}
    (App (Val (e @!! go.GoType.PointerType Election.ty @!! go!"Key")) (Val #()))
  {{ RET #st.key; electionState e s st }}

end spec

end concurrency
end EtcdGrove
end Perennial
