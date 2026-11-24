/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): `SetAdd(s, x)`: `setAdd`.
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

/-- `s \cup {x}`: `setAdd` (a new slice, or `s` itself when `x` is in it). -/
abbrev SetAdd.spec : Prop :=
  ∀ (sl : GoSlice) (xs : SSet) (x : Str),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      strsRO sl xs ∗ ⌜(xs.length : Int) + 1 < 2 ^ 63⌝ }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SetAdd)) (Val #sl)) (Val #x))
  {{ (u : GoSlice), RET #u; strsRO u (setAdd xs x) }}

end spec

end AntCheck
end EtcdGrove
end Perennial
