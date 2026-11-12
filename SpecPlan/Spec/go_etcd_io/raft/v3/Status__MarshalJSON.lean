/-
## `Status.MarshalJSON()` (`status.go`)

**Users.** etcd's expvar `raft.status` (`server/etcdserver/raft.go:55-63`, through `encoding/json`),
`Status.String`. **Proof sketch.** `fmt.Sprintf` of the basic status, the progress map's entries
(R1's `statusOwn_progress`: read), a closing brace. **Changes.** New (round 1). **Margin.** The
bytes are not stated. `%q` of `RaftState.String()` indexes `stmap` (`raft_init`): `statusOwn`
carries that the role is one of the four (verify-round, A4 S3).
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.ApiCore

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Raft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The status as JSON (never an error). -/
def Status.MarshalJSON.spec : Prop :=
  ∀ (s : go_etcd_io.raft.v3.Status),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ statusOwn s }}
    (App (Val (s @!! go_etcd_io.raft.v3.Status.ty @!! go!"MarshalJSON")) (Val #()))
  {{ (bs : GoSlice) (err : GoInterface), RET (PairV #bs #err); statusOwn s ∗
      ⌜err = interface.nil⌝ ∗ ∃ b : List w8, ownSlice bs b (DFrac.own 1) }}

end spec
end Raft
end EtcdGrove
end Perennial
