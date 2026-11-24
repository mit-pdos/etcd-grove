/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `x.V1()`: B 291-359, `OnDisk.V1`.
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

/-- `OnDisk`'s `V1` (B 291-359): `OnDisk.V1`, where defined. -/
abbrev onDisk.V1.spec : Prop :=
  ∀ (g : G.onDisk) (x : OnDisk) (v : Str),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      onDiskRO g x ∗
      ⌜x.V1 = .ok v⌝ }}
    (App (Val (g @!! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.ty @!! go!"V1")) (Val #()))
  {{ RET #v; True }}

end spec

end AntCheck
end EtcdGrove
end Perennial
