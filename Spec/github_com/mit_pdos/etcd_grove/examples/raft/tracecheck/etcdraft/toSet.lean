/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `toSet(ids)`, a list of the trace's ids as a set.
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

/-- `toSet(ids)`, of ASCII strings: `toSet ids` (`ok` false where it is `none`), a fresh read-only
set. -/
abbrev toSet.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (gss : List GoString) (ids : List String),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      sl ↦*{dq} gss ∗ ⌜List.Forall₂ strRel gss ids⌝ }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.toSet)) (Val #sl))
  {{ (set : GoSlice) (ok : Bool), RET (PairV #set #ok); sl ↦*{dq} gss ∗
      match toSet ids with
      | none => ⌜ok = false⌝
      | some st => ⌜ok = true⌝ ∗ setRO set st }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
