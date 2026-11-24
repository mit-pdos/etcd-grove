/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `x.lc1()`: B 214-253, `InMem.lc1`.
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

/-- `InMem`'s `lc1` (B 214-253): `InMem.lc1`, where defined. -/
abbrev inMem.lc1.spec : Prop :=
  ∀ (g : G.inMem) (x : InMem) (v : TermFn Conf),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      inMemRO g x ∗
      ⌜x.lc1 = .ok v⌝ }}
    (App (Val (g @!! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.ty @!! go!"lc1")) (Val #()))
  {{ (u : GoSlice), RET #u; termConfsRO u v }}

end spec

end AntCheck
end EtcdGrove
end Perennial
