/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `isMessageEvent(name)`.
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

/-- `isMessageEvent(name)`: `isMessageEvent s`. -/
abbrev isMessageEvent.spec : Prop :=
  ∀ (name : GoString) (s : String),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      ⌜strRel name s⌝ }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.isMessageEvent)) (Val #name))
  {{ RET #(isMessageEvent s); True }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
