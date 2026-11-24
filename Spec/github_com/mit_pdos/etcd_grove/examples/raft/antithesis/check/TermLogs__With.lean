/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): `f.With(t, v)`: `TermFn.with`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Rep

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- `[u \in DOMAIN f \cup {t} |-> IF u = t THEN v ELSE f[u]]`: `TermFn.with`, a new slice. -/
abbrev TermLogs.With.spec : Prop :=
  ∀ (sl : GoSlice) (f : TermFn (List Entry)) (t : w64) (vl : GoSlice) (v : List Entry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      termLogsRO sl f ∗ logRO vl v ∗ ⌜(f.length : Int) + 1 < 2 ^ 63⌝ }}
    (App (App (Val (sl @!! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermLogs.ty @!! go!"With")) (Val #t)) (Val #vl))
  {{ (u : GoSlice), RET #u; termLogsRO u (f.with (sint.Z t) v) }}

end spec

end AntCheck
end EtcdGrove
end Perennial
