/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): `ConfOf(l, a, initConf)`.
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

/-- R 163-168 `ConfOf(l, a)`: `confOf`, where defined (its changes far from overflow). -/
abbrev ConfOf.spec : Prop :=
  ∀ (sl : GoSlice) (l : List Entry) (a : w64) (g : G.Conf) (c0 c : Conf),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      logRO sl l ∗ confRO g c0 ∗ ⌜confOf l (sint.Z a) c0 = .ok c ∧ sint.Z a < 2 ^ 63 - 1 ∧ ConfOf.Bounded l c0⌝ }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.ConfOf)) (Val #sl)) (Val #a)) (Val #g))
  {{ (u : G.Conf), RET #u; confRO u c }}

end spec

end AntCheck
end EtcdGrove
end Perennial
