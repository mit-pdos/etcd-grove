/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `ReqFactIn(ll, m)`: B 85-91, `reqFactIn`.
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

/-- B 85-91 `ReqFactIn(ll, m)`: `reqFactIn ll m`, where defined. -/
abbrev ReqFactIn.spec : Prop :=
  ∀ (sl : GoSlice) (ll : TermFn (List Entry)) (g : G.Msg) (m : Msg) (f : AppendFact),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      termLogsRO sl ll ∗
      msgRO g m ∗
      ⌜reqFactIn ll m = .ok f⌝ }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.ReqFactIn)) (Val #sl)) (Val #g))
  {{ (u : G.AppendFact), RET #u; appendFactRO u f }}

end spec

end AntCheck
end EtcdGrove
end Perennial
