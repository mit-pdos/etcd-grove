/-
`membership.RaftCluster.ValidateConfigurationChange(cc, shouldApplyV3)` (`cluster.go`): with
`shouldApplyV3`, the members and removed members the backend holds
(`c.be.MustReadMembersFromBackend()`), then the change checked against them; without, `nil`.
Lean-first (no Rocq counterpart); D43 M4 (2026-10-26, the user's decision: proved, over
`json.Unmarshal`'s trust-boundary spec).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRest

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section pure
variable [GooseExts]

/- `membership.urlTaken` and `membership.ccValidM` are in `InvRest.lean` (D43 M5b′, 2026-10-26:
`ccValidOn` is defined from them). -/

end pure

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/- `membership.memberURLsAt` and `membership.membersRead` are in the package's `Defs.lean` (D43
M5b′: the backend's read contract names them). -/

/-- The backend's read of the members (`c.be`, the interface `bi`,
`MustReadMembersFromBackend()`), by the caller's triple (persistent): from `Pr`, the members map
(`membersRead` of `mems`) and the removed map `rmv`, and `Pr` back. -/
def membership.beReadOk (bi : GoInterfaceOk) (Pr : IProp GF) (mems : GMap w64 (List GoString))
    (rmv : GMap w64 Bool) : IProp GF :=
  iprop(□ ({{ Pr }}
    (App (Val #(methods bi.ty go!"MustReadMembersFromBackend" bi.v)) (Val #()))
    {{ (mp rp : Loc), RET (PairV #mp #rp); Pr ∗ membership.membersRead mp mems ∗ rp ↦$ rmv }}))

instance membership.beReadOk_persistent (bi : GoInterfaceOk) (Pr : IProp GF)
    (mems : GMap w64 (List GoString)) (rmv : GMap w64 Bool) :
    Persistent (membership.beReadOk (GF := GF) bi Pr mems rmv) := by
  unfold membership.beReadOk; infer_instance

/-- `c.ValidateConfigurationChange(cc, v3)`, of a change `m` (read-only at `dq`) an `AddNode` (its
context decoding to a member, not a promotion) or a `RemoveNode`: with `v3`, it reads the backend
by the caller's triple and returns `nil` exactly when the change validates (`ccValidM`), else an
error; without, `nil`. -/
abbrev membership.RaftCluster.ValidateConfigurationChange.spec : Prop :=
  ∀ (c cc : Loc) (dq dqb : DFrac) (m : ConfChangeM) (v3 : Bool) (bi : GoInterfaceOk) (Pr : IProp GF)
    (mems : GMap w64 (List GoString)) (rmv : GMap w64 Bool),
  (m.type = W32 0 ∨ m.type = W32 1) →
  (m.type = W32 0 → ∃ i, membership.ccContextOf m.context = some (i, false)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗
      membership.rcBeAddr c ↦{dqb} GoInterface.ok bi ∗ ownConfChange cc dq m ∗
      (if v3 then iprop(membership.beReadOk bi Pr mems rmv ∗ Pr) else iprop(True)) }}
    (App (App (Val (c @!! go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!!
      go!"ValidateConfigurationChange")) (Val #cc)) (Val #v3))
  {{ (err : GoInterface), RET #err; membership.rcBeAddr c ↦{dqb} GoInterface.ok bi ∗ ownConfChange cc dq m ∗
      (if v3 then iprop(Pr ∗ ⌜err = GoInterface.nil ↔ membership.ccValidM mems rmv m⌝)
       else iprop(⌜err = GoInterface.nil⌝)) }}

end spec

end EtcdGrove
end Perennial
