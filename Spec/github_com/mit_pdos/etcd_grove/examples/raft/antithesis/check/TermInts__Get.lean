/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): `f.Get(t)`: `TermFn.get`.
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

/-- `f[t]`, where defined (outside the domain: an `EvalError`). -/
abbrev TermInts.Get.spec : Prop :=
  ∀ (sl : GoSlice) (f : TermFn (Int)) (t : w64) (x : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      termIntsRO sl f ∗ ⌜f.get (sint.Z t) = .ok x⌝ }}
    (App (Val (sl @!! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermInts.ty @!! go!"Get")) (Val #t))
  {{ (u : w64), RET #u; ⌜sint.Z u = x⌝ }}

end spec

end AntCheck
end EtcdGrove
end Perennial
