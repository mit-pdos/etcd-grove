/-
## `(*raftLog).acceptApplying(i, size, allowUnstable)` (internal)

**Users**: `acceptReady` (`rawnode.go:434`: the last committed entry handed out, at least
`applying`). **Proof sketch**: the `Panicf` excluded by `i ≤ committed`; `applied ≤ i` keeps `Wf`.
**Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/raftLog__acceptApplying.lean`.
-/
module

public import Spec.go_etcd_io.raft.v3.ApiLog

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

/-- (internal) Record the entries through `i` as being applied, taking `size` of the budget. -/
def raftLog.acceptApplying.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (i size : w64) (allow : Bool),
  ls.applied ≤ uint.nat i → uint.nat i ≤ ls.committed →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftLog l ls }}
    (App (App (App (Val (l @!! go.GoType.PointerType go_etcd_io.raft.v3.raftLog.ty @!! go!"acceptApplying")) (Val #i)) (Val #size)) (Val #allow))
  {{ RET #(); raftLog l (ls.acceptApplying (uint.nat i) size allow) }}

end spec
end Raft
end EtcdGrove
end Perennial
