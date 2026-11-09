/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `ln.msgType()`, `RaftMsgType[logline.event.msg.type]`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.TraceRead

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

/-- `ln.msgType()`: the line's message's type by `RaftMsgType` and whether it has one there (`(0,
false)` without a message, or a type outside the table). -/
abbrev line.msgType.spec : Prop :=
  ∀ (q : Loc) (x : Line),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      linePtrRO q x }}
    (App (Val (q @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.line.ty
      @!! go!"msgType")) (Val #()))
  {{ RET (PairV #(((x.ev.msg.bind (fun e => raftMsgType e.type)).map msgTypeW).getD (W8 0))
      #((x.ev.msg.bind (fun e => raftMsgType e.type)).isSome)); True }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
