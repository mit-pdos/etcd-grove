/-
## `logSliceFromMsgApp(m)` (internal)

`handleAppendEntries`. Mirrors the code: the message's term, previous entry id and entries (the
message's slice). **Changes.** Unchanged in substance. **Margin.** The entries' slice is not named
(`msgPts` is 3h's).
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

/-- (internal) The appended slice an `MsgApp` describes. -/
def logSliceFromMsgApp.spec : Prop :=
  ∀ (ml : Loc) (dq : DFrac) (m : Msg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ msgPts ml dq m }}
    (App (Val (@! go_etcd_io.raft.v3.logSliceFromMsgApp)) (Val #ml))
  {{ (ls : go_etcd_io.raft.v3.logSlice), RET #ls; msgPts ml dq m ∗
      ⌜ls.term' = m.term ∧ ls.prev'.term' = m.logTerm ∧ ls.prev'.index' = m.index⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
