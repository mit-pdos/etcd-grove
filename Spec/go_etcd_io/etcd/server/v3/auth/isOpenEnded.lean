/-
`isOpenEnded` (`server/auth/range_perm_cache.go`). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/auth/InvAuth.lean` (unit P2; the auth plan's S2, 2026-10-23).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth auth

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- `isOpenEnded(rangeEnd)`: `len(rangeEnd) == 1 && rangeEnd[0] == 0`, the model's `isOpenEnded`. -/
abbrev auth.isOpenEnded.spec : Prop :=
  ∀ (re : GoSlice) (e : List w8) (de : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ re ↦*{de} e }}
    (App (Val (@! go_etcd_io.etcd.server.v3.auth.isOpenEnded)) (Val #re))
  {{ RET #(decide (auth.isOpenEnded e)); re ↦*{de} e }}

end spec

end EtcdGrove
end Perennial
