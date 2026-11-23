/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `x.newC()`: B 291-359, `OnDisk.newC`.
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

/-- `OnDisk`'s `newC` (B 291-359): `OnDisk.newC`, where defined. -/
abbrev onDisk.newC.spec : Prop :=
  ∀ (g : G.onDisk) (x : OnDisk) (v : List Entry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      onDiskRO g x ∗
      ⌜x.newC = .ok v⌝ }}
    (App (Val (g @!! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.ty @!! go!"newC")) (Val #()))
  {{ (u : GoSlice), RET #u; logRO u v }}

end spec

end AntCheck
end EtcdGrove
end Perennial
