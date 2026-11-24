/-
Lean-first (no Rocq counterpart). #33 S3b (2026-11-23): `SubSeq(s, m, n)`: `subSeq` where it is defined.
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

/-- `SubSeq(s, m, n)`: `s`'s elements `m..n` (1-indexed), sharing `s`'s array, where `subSeq` is
defined (elsewhere the Go panics with an `EvalError`, which a triple does not describe). -/
abbrev SubSeq.spec : Prop :=
  ∀ (sl : GoSlice) (s : List Entry) (m n : w64) (r : List Entry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      logRO sl s ∗ ⌜subSeq s (sint.Z m) (sint.Z n) = .ok r⌝ }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SubSeq)) (Val #sl)) (Val #m)) (Val #n))
  {{ (u : GoSlice), RET #u; logRO u r }}

end spec

end AntCheck
end EtcdGrove
end Perennial
