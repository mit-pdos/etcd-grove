/-
(hraft_robust R3) The spec of `disk.decodeConfiguration` (`snap.go`).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.Defs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]

open github_com.hashicorp.raft github_com.hashicorp.raft.examples.hraftnet.disk in
/-- `decodeConfiguration(r)`, on input that starts with `encCfg ss` (every ID and address shorter than `2 ^ 63`),
returns a configuration holding `ss` in a fresh, owned slice, and leaves the rest. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.disk.decodeConfiguration.spec : Prop :=
  ∀ (r : Loc) (ss : List SServer) (rest : List w8), ss.length < 2 ^ 63 →
    (∀ s ∈ ss, s.id.length < 2 ^ 63 ∧ s.addr.length < 2 ^ 63) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.disk ∗
      readerSt r (encCfg ss ++ rest) }}
    (App (Val (@! github_com.hashicorp.raft.examples.hraftnet.disk.decodeConfiguration)) (Val #r))
  {{ (c : Configuration), RET #c; readerSt r rest ∗
      ∃ svs : List Server, c.Servers' ↦* svs ∗ ownSliceCap Server c.Servers' (DFrac.own 1) ∗
        ⌜svs.map srvOf = ss⌝ }}

end spec

end Perennial
