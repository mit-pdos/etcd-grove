/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `ln.confChange()`, the line's only configuration change.
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

/-- `ln.confChange()`: `x.confChange` (`ok` false where it is `none`). -/
abbrev line.confChange.spec : Prop :=
  ∀ (q : Loc) (x : Line),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      linePtrRO q x }}
    (App (Val (q @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.line.ty
      @!! go!"confChange")) (Val #()))
  {{ (a : GoString) (j : w64) (ok : Bool), RET (PairV (PairV #a #j) #ok);
      ⌜match x.confChange with
       | none => ok = false
       | some (act, n) => ok = true ∧ strRel a act ∧ uint.nat j = n⌝ }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
