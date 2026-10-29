/- Lean-first (no Rocq counterpart).

# A `Status` value's memory (2026-10-29, stage U7)

What `node.Status()` hands out (`statusOwnRaw`, the API's sealed `statusOwn`): heap ownership only,
of what a `Status` value points to -- its `*pb.HardState` (read-only, `hsRO`), its configuration's
maps (`ownCfgCC`, at some configuration: `Config.Clone` drops `AutoLeave`,
`issues/raft-config-clone-autoleave.md`), and a leader's progress copy (`progCopyOwn`: the map, each
entry's cloned `Inflights`; `nil` at a non-leader); or the zero `Status{}` of a stopped node.
No fact ties the values to the cluster.
-/
module

public import Proof.go_etcd_io.raft.v3.InvPb
public import Proof.go_etcd_io.raft.v3.InvConfchange

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `getProgressCopy`'s map: owned, each entry's `Inflights` its own (a clone). -/
def progCopyOwn (m : GoMap) : IProp GF :=
  iprop(∃ pm : GMap w64 tracker.Progress, m ↦$ pm ∗
    [∗map] _k ↦ p ∈ pm, ∃ i : Inflights, ownInflights p.Inflights' i)

/-- See the file header. -/
def statusOwnRaw (st : Status) : IProp GF :=
  iprop(⌜st = zero_val Status⌝ ∨
    ((∃ hs, hsRO st.BasicStatus'.HardState' hs) ∗
     (∃ c : CfgM, ownCfgCC st.Config' (DFrac.own 1) c) ∗
     (⌜st.Progress' = null⌝ ∨ progCopyOwn st.Progress')))

end defs

end EtcdGrove
end Perennial
