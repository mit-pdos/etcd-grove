/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): `LastConf(l, a)`.
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

/-- R 161 `LastConf(l, a)`: `lastConf`, where defined. -/
abbrev LastConf.spec : Prop :=
  ∀ (sl : GoSlice) (l : List Entry) (a : w64) (k : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      logRO sl l ∗ ⌜lastConf l (sint.Z a) = .ok k ∧ sint.Z a < 2 ^ 63 - 1⌝ }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.LastConf)) (Val #sl)) (Val #a))
  {{ (w : w64), RET #w; ⌜sint.Z w = k⌝ }}

end spec

end AntCheck
end EtcdGrove
end Perennial
