/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): `f.Without(s)`: `TermFn.without`.
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

/-- `[t \in DOMAIN f \ S |-> f[t]]`: `TermFn.without`. -/
abbrev TermInts.Without.spec : Prop :=
  ∀ (sl : GoSlice) (f : TermFn (Int)) (tl : GoSlice) (ts : List Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      termIntsRO sl f ∗ intsRO tl ts }}
    (App (Val (sl @!! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermInts.ty @!! go!"Without")) (Val #tl))
  {{ (u : GoSlice), RET #u; termIntsRO u (f.without ts) }}

end spec

end AntCheck
end EtcdGrove
end Perennial
