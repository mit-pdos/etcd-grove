/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): `setStr(a, k, v)`: a copy of `a` with element `k` set.
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

/-- `setStr(a, k, v)`: a new slice, `a` with element `k` replaced (`List.set`). -/
abbrev setStr.spec : Prop :=
  ∀ (a : GoSlice) (xs : List Str) (k : w64) (v : Str),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      strsRO a xs ∗ ⌜0 ≤ sint.Z k ∧ sint.Z k < xs.length⌝ }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.setStr)) (Val #a)) (Val #k)) (Val #v))
  {{ (out : GoSlice), RET #out; strsRO out (xs.set (sint.nat k) v) }}

end spec

end AntCheck
end EtcdGrove
end Perennial
