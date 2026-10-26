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
variable [FfiSyntax]

/-- A peer URL some member of `mems` (each member's peer URLs) has. -/
def membership.urlTaken (mems : GMap w64 (List GoString)) (u : GoString) : Prop :=
  ∃ k pus, mems !! k = some pus ∧ u ∈ pus

/-- **The verdict of `ValidateConfigurationChange` with `shouldApplyV3`**, on the members' peer URLs
`mems` and the removed members `rmv` the backend holds: not a removed id; an `AddNode` (not a
promotion: the scope's) of an id not a member, whose peer URLs (the context's member's) no member
has; a `RemoveNode` of a member. -/
def membership.ccValidM (mems : GMap w64 (List GoString)) (rmv : GMap w64 Bool) (m : CCV1M) : Prop :=
  (rmv !! m.nodeId).getD false = false ∧
  (if m.type = W32 0 then mems !! m.nodeId = none ∧
      ∀ u, u ∈ (membership.ccMemberOf m.context).peerURLs → ¬ membership.urlTaken mems u
    else (mems !! m.nodeId).isSome = true)

end pure

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- A member record `l` the backend's read made, with its peer URLs `pus`. -/
def membership.memberURLsAt (l : Loc) (pus : List GoString) : IProp GF :=
  iprop(∃ pu : GoSlice, ⌜l ≠ null⌝ ∗ membership.mPeerURLsAddr l ↦ pu ∗ pu ↦* pus)

/-- The members map `mp` the backend's read returns, of the members' peer URLs `mems`. -/
def membership.membersRead (mp : Loc) (mems : GMap w64 (List GoString)) : IProp GF :=
  iprop(∃ ml : GMap w64 Loc, mp ↦$ ml ∗ ⌜∀ k, (ml !! k).isSome = (mems !! k).isSome⌝ ∗
    [∗map] k ↦ l ∈ ml, ∃ pus : List GoString, ⌜mems !! k = some pus⌝ ∗ membership.memberURLsAt l pus)

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
  ∀ (c cc : Loc) (dq : DFrac) (m : CCV1M) (v3 : Bool) (bi : GoInterfaceOk) (Pr : IProp GF)
    (mems : GMap w64 (List GoString)) (rmv : GMap w64 Bool),
  (m.type = W32 0 ∨ m.type = W32 1) →
  (m.type = W32 0 → ∃ i, membership.ccContextOf m.context = some (i, false)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗
      membership.rcBeAddr c ↦□ GoInterface.ok bi ∗ ownCCV1 cc dq m ∗
      (if v3 then iprop(membership.beReadOk bi Pr mems rmv ∗ Pr) else iprop(True)) }}
    (App (App (Val (c @!! go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!!
      go!"ValidateConfigurationChange")) (Val #cc)) (Val #v3))
  {{ (err : GoInterface), RET #err; ownCCV1 cc dq m ∗
      (if v3 then iprop(Pr ∗ ⌜err = GoInterface.nil ↔ membership.ccValidM mems rmv m⌝)
       else iprop(⌜err = GoInterface.nil⌝)) }}

end spec

end EtcdGrove
end Perennial
