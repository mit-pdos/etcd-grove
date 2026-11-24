/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `SendableIn(ld, ll, ch, tl, f)`: B 117-126, `sendableIn`.
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

/-- B 117-126 `SendableIn(ld, ll, ch, tl, f)`: `sendableIn`, where defined (`f.prevLogIndex + Len(f.entries)` within the Go `int`). -/
abbrev SendableIn.spec : Prop :=
  ∀ (ldl : GoSlice) (ld : List LeaderRec) (lll : GoSlice) (ll : TermFn (List Entry)) (chl : GoSlice) (ch : List Entry) (tll : GoSlice) (tl : TermFn Int) (g : G.AppendFact) (f : AppendFact) (b : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      leadersRO ldl ld ∗
      termLogsRO lll ll ∗
      logRO chl ch ∗
      termIntsRO tll tl ∗
      appendFactRO g f ∗
      ⌜sendableIn ld ll ch tl f = .ok b ∧ bigOk f.prevLogIndex ∧ (f.entries.length : Int) < 2 ^ 62⌝ }}
    (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SendableIn)) (Val #ldl)) (Val #lll)) (Val #chl)) (Val #tll)) (Val #g))
  {{ RET #b; True }}

end spec

end AntCheck
end EtcdGrove
end Perennial
