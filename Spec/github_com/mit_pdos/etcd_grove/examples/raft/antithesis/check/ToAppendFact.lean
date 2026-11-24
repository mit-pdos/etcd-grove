/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `ToAppendFact(m)`: B 68-71, `toAppendFact`.
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

/-- B 68-71 `AppendFact(m)`: `toAppendFact m`, where defined. -/
abbrev ToAppendFact.spec : Prop :=
  ∀ (g : G.Msg) (m : Msg) (f : AppendFact),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      msgRO g m ∗
      ⌜toAppendFact m = .ok f⌝ }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.ToAppendFact)) (Val #g))
  {{ (u : G.AppendFact), RET #u; appendFactRO u f }}

end spec

end AntCheck
end EtcdGrove
end Perennial
