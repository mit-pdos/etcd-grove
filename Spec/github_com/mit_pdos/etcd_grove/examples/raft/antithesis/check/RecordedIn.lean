/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `RecordedIn(ch, tl, l, c, t)`: B 109-112, `recordedIn`.
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

/-- B 109-112 `RecordedIn(ch, tl, l, c, t)`: `recordedIn`, where defined. -/
abbrev RecordedIn.spec : Prop :=
  ∀ (chl : GoSlice) (ch : List Entry) (tll : GoSlice) (tl : TermFn Int) (ll : GoSlice) (l : List Entry) (c t : w64) (b : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      logRO chl ch ∗
      termIntsRO tll tl ∗
      logRO ll l ∗
      ⌜recordedIn ch tl l (sint.Z c) (sint.Z t) = .ok b⌝ }}
    (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.RecordedIn)) (Val #chl)) (Val #tll)) (Val #ll)) (Val #c)) (Val #t))
  {{ RET #b; True }}

end spec

end AntCheck
end EtcdGrove
end Perennial
