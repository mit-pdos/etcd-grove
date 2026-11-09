/-
## `getProgressCopy(r)` (internal)

**Users.** `getStatus` (at a leader). **Proof sketch.** R4's `Visit` over the progress map; each
value copied with `Inflights.Clone()`. **Changes.** New (no old spec). **Margin.** The copies'
contents are not stated.
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

/-- (internal) A fresh copy of the progress map. -/
def getProgressCopy.spec : Prop :=
  ∀ (r : Loc) (id : w64) (ρ : CoreView),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftRO r id ρ }}
    (App (Val (@! go_etcd_io.raft.v3.getProgressCopy)) (Val #r))
  {{ (mp : Loc), RET #mp; raftRO r id ρ ∗ progressCopyOwn mp }}

end spec
end Raft
end EtcdGrove
end Perennial
