/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `SnapOk(ll, m)`: B 80-83, `snapOk`.
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

/-- B 80-83 `SnapOk(ll, m)`: `snapOk ll m`, where defined. -/
abbrev SnapOk.spec : Prop :=
  ∀ (sl : GoSlice) (ll : TermFn (List Entry)) (g : G.Msg) (m : Msg) (b : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      termLogsRO sl ll ∗
      msgRO g m ∗
      ⌜snapOk ll m = .ok b⌝ }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SnapOk)) (Val #sl)) (Val #g))
  {{ RET #b; True }}

end spec

end AntCheck
end EtcdGrove
end Perennial
