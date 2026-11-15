/-
## `payloadsSize(ents)` (internal)

**Users**: `maybeSendAppend` (`raft.go:659`), `MsgStorageApplyResp` (`raft.go:1227`),
`increaseUncommittedSize` (`raft.go:2100`). Mirrors the code (the sum wraps).
**Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/payloadsSize.lean`.
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

/-- (internal) The total length of the entries' data, modulo `2^64`. -/
def payloadsSize.spec : Prop :=
  ∀ (sl : GoSlice) (k : Nat) (es : List LogEntry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ entriesRO sl k es }}
    (App (Val (@! go_etcd_io.raft.v3.payloadsSize)) (Val #sl))
  {{ RET #(W64 (es.map (fun e => e.data.length)).sum); True }}

end spec
end Raft
end EtcdGrove
end Perennial
