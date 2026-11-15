/-
## `DescribeConfChange(cc)`

**Users**: `stepLeader`'s log line for a refused conf change (`raft.go:1358`). Formatting only.
**Assumed** (trust boundary; verify-round, A5 F1): the body formats with `fmt.Fprintf` into a
`strings.Builder` (`util.go:247-259`), of which neither Perennial (only `fmt.{Errorf,Printf,Sprintf}`;
`strings.Builder` without methods) nor this repository (raftpb's `fmtErrorf` covers `Errorf` only)
has a spec. True of the code: `cc.AsV2()` (3h's) reads the change, the builder is local, `Fprintf`
into a `*strings.Builder` never fails, and the change is given back unmodified.
**Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/DescribeConfChange.lean`: over R1's `confChangePts`.
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.ApiLog

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

/-- A description of the change (unspecified). -/
def DescribeConfChange.spec : Prop :=
  ∀ (v : GoInterface) (dq : DFrac) (c : ConfChangeI),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ confChangePts v dq c }}
    (App (Val (@! go_etcd_io.raft.v3.DescribeConfChange)) (Val #v))
  {{ (s : GoString), RET #s; confChangePts v dq c }}

end spec
end Raft
end EtcdGrove
end Perennial
