/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): `setConfirmed(a, k, v)`: a copy of `a` with element `k` set.
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

/-- `setConfirmed(a, k, v)`: a new slice, `a` with element `k` replaced (`List.set`). -/
abbrev setConfirmed.spec : Prop :=
  ∀ (a : GoSlice) (xs : List Confirmed) (k : w64) (v : G.Confirmed) (x : Confirmed),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      confirmedsRO a xs ∗ ⌜confirmedRel v x⌝ ∗ ⌜0 ≤ sint.Z k ∧ sint.Z k < xs.length⌝ }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.setConfirmed)) (Val #a)) (Val #k)) (Val #v))
  {{ (out : GoSlice), RET #out; confirmedsRO out (xs.set (sint.nat k) x) }}

end spec

end AntCheck
end EtcdGrove
end Perennial
