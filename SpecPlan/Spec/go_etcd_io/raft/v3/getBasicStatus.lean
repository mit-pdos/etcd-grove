/-
## `getBasicStatus(r)`

**Users.** `RawNode.BasicStatus` (`rawnode.go:500-502`), `getStatus`. R1's `RawNode.BasicStatus.spec`
(the id; a hard state). Snippet: `status.go`.

**Proof sketch.** Reads `id`, `leadTransferee`, `raftLog.applied`; `hardState()`, `softState()`.
**Changes.** New (R1 left it to R2; no old spec). **Margin.** `Applied` and `LeadTransferee` are not
related to anything.
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

/-- The id, the view's hard state (fresh) and soft state. -/
def getBasicStatus.spec : Prop :=
  ∀ (r : Loc) (id : w64) (ρ : CoreView),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftRO r id ρ }}
    (App (Val (@! go_etcd_io.raft.v3.getBasicStatus)) (Val #r))
  {{ (bs : go_etcd_io.raft.v3.BasicStatus), RET #bs; raftRO r id ρ ∗
      ⌜bs.ID' = id ∧ bs.SoftState' = go_etcd_io.raft.v3.SoftState.mk ρ.lead ρ.role⌝ ∗
      hardStatePts bs.HardState' (DFrac.own 1) ρ.hs }}

end spec
end Raft
end EtcdGrove
end Perennial
