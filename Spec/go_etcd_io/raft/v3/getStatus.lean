/-
## `getStatus(r)`

**Users.** `RawNode.Status` (`rawnode.go:460`), `node.run`'s `status` arm (`node.go:425`: sent back to
`node.Status`, etcd's `isLearnerReady` and the examples' status dumps). R1's `RawNode.Status.spec`,
`node.Status.spec` (`statusOwn`, the id). Snippet: `status.go`.

**Proof sketch.** `getBasicStatus`; at a leader `getProgressCopy` (fresh `Progress` copies with
cloned `Inflights`: `progressCopyOwn`); `r.trk.Config.Clone()` (R4: fresh maps). `statusOwn s` is
their memory.

**Changes.** New (R1 left it to R2; no old spec). **Margin.** The configuration and progress are not
related to the view.
-/
module

public import Spec.go_etcd_io.raft.v3.ApiCore

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

/-- A fresh status: the id, the view's hard and soft state, the caller's maps. -/
def getStatus.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (ρ : CoreView),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftCore r γ id ρ }}
    (App (Val (@! go_etcd_io.raft.v3.getStatus)) (Val #r))
  {{ (s : go_etcd_io.raft.v3.Status), RET #s; raftCore r γ id ρ ∗ statusOwn s ∗
      ⌜s.BasicStatus'.ID' = id ∧
        s.BasicStatus'.SoftState' = go_etcd_io.raft.v3.SoftState.mk ρ.lead ρ.role⌝ ∗
      hardStatePts s.BasicStatus'.HardState' (DFrac.own 1) ρ.hs }}

end spec
end Raft
end EtcdGrove
end Perennial
