/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `x.cmt()`: B 214-253, `InMem.cmt`.
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

/-- `InMem`'s `cmt` (B 214-253): `InMem.cmt`, where defined. -/
abbrev inMem.cmt.spec : Prop :=
  ∀ (g : G.inMem) (x : InMem) (v : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      inMemRO g x ∗
      ⌜x.cmt = .ok v⌝ }}
    (App (Val (g @!! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.ty @!! go!"cmt")) (Val #()))
  {{ RET #v; True }}

end spec

end AntCheck
end EtcdGrove
end Perennial
