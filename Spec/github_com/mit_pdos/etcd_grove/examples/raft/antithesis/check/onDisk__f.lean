/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `x.f()`: B 291-359, `OnDisk.f`.
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

/-- `OnDisk`'s `f` (B 291-359): `OnDisk.f`, where defined. -/
abbrev onDisk.f.spec : Prop :=
  ∀ (g : G.onDisk) (x : OnDisk) (v : AppendFact),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      onDiskRO g x ∗
      ⌜x.f = .ok v⌝ }}
    (App (Val (g @!! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.ty @!! go!"f")) (Val #()))
  {{ (u : G.AppendFact), RET #u; appendFactRO u v }}

end spec

end AntCheck
end EtcdGrove
end Perennial
