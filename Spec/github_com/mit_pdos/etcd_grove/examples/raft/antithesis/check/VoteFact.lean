/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `VoteFact(m)`: B 63-65, `voteFact`.
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

/-- B 63-65 `VoteFact(m)`: `voteFact m`, where defined (every field it reads present). -/
abbrev VoteFact.spec : Prop :=
  ∀ (g : G.Msg) (m : Msg) (f : Fact),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      msgRO g m ∗
      ⌜voteFact m = .ok f⌝ }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.VoteFact)) (Val #g))
  {{ (u : G.Fact), RET #u; ⌜factRel u f⌝ }}

end spec

end AntCheck
end EtcdGrove
end Perennial
