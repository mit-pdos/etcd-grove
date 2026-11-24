/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): `s.OneWaiting(i, l)`.
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

/-- R 174-175 `OneWaiting(i, l)`: `State.oneWaiting`, where defined (`confAt[i] + 1` and `len(l) + 1` within the Go `int`). -/
abbrev State.OneWaiting.spec : Prop :=
  ∀ (p : Loc) (s : State) (i : w64) (sl : GoSlice) (l : List Entry) (b : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      stateRO p s ∗ logRO sl l ∗ ⌜0 ≤ sint.Z i ∧ sint.Z i < s.cfg.server.length ∧ s.oneWaiting (sint.nat i) l = .ok b ∧
        s.confAt[sint.nat i]! < 2 ^ 63 - 1 ∧ (l.length : Int) < 2 ^ 63 - 1⌝ }}
    (App (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.ty @!! go!"OneWaiting")) (Val #i)) (Val #sl))
  {{ RET #b; True }}

end spec

end AntCheck
end EtcdGrove
end Perennial
