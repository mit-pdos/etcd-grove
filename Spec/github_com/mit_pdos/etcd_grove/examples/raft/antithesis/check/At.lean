/-
Lean-first (no Rocq counterpart). #33 S3b (2026-11-23): `At(l, k)`: `atE` where it is defined.
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

/-- `At(l, k)`: the entry `atE l k`, where it is defined (elsewhere the Go panics with an
`EvalError`, which a triple does not describe). -/
abbrev At.spec : Prop :=
  ∀ (sl : GoSlice) (l : List Entry) (k : w64) (x : Entry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      logRO sl l ∗ ⌜atE l (sint.Z k) = .ok x⌝ }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.At)) (Val #sl)) (Val #k))
  {{ (e : G.Entry), RET #e; entryRO e x }}

end spec

end AntCheck
end EtcdGrove
end Perennial
