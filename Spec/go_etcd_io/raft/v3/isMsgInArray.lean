/-
## `isMsgInArray(msgt, arr)` (internal)

**Users**: `IsLocalMsg`, `IsResponseMsg` (R1's specs). Mirrors the code.
**Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/isMsgInArray.lean`.
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

/-- (internal) `arr[msgt]`, false past its end. -/
def isMsgInArray.spec : Prop :=
  ∀ (t : w32) (arr : GoSlice) (dq : DFrac) (bs : List Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ arr ↦*{dq} bs }}
    (App (App (Val (@! go_etcd_io.raft.v3.isMsgInArray)) (Val #t)) (Val #arr))
  {{ RET #((bs[uint.nat t]?).getD false); arr ↦*{dq} bs }}

end spec
end Raft
end EtcdGrove
end Perennial
