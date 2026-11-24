/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `x.K()`: B 291-359, `OnDisk.K`.
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

/-- `OnDisk`'s `K` (B 291-359): `OnDisk.K`, where defined. -/
abbrev onDisk.K.spec : Prop :=
  ∀ (g : G.onDisk) (x : OnDisk) (v : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      onDiskRO g x ∗
      ⌜x.K = .ok v⌝ }}
    (App (Val (g @!! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.ty @!! go!"K")) (Val #()))
  {{ (u : w64), RET #u; ⌜sint.Z u = v⌝ }}

end spec

end AntCheck
end EtcdGrove
end Perennial
