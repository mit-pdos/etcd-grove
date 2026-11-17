/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `parseID(s)`, an id of the trace.
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

/-- `parseID(s)`, of an ASCII string: `parseID s` (`ok` false where it is `none`). -/
abbrev parseID.spec : Prop :=
  ∀ (gs : GoString) (s : String),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      ⌜strRel gs s⌝ }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.parseID)) (Val #gs))
  {{ (id : w64) (ok : Bool), RET (PairV #id #ok);
      ⌜match parseID s with
       | none => ok = false
       | some n => ok = true ∧ uint.nat id = n⌝ }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
