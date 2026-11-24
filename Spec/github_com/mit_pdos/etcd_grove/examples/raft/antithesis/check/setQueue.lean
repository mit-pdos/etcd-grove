/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): `setQueue(a, k, v)`: a copy of `a` with element `k` set.
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

/-- `setQueue(a, k, v)`: a new slice, `a` with element `k` replaced (`List.set`). -/
abbrev setQueue.spec : Prop :=
  ∀ (a : GoSlice) (xs : List (List QItem)) (k : w64) (v : GoSlice) (x : List QItem),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      queueRO a xs ∗ qitemsRO v x ∗ ⌜0 ≤ sint.Z k ∧ sint.Z k < xs.length⌝ }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.setQueue)) (Val #a)) (Val #k)) (Val #v))
  {{ (out : GoSlice), RET #out; queueRO out (xs.set (sint.nat k) x) }}

end spec

end AntCheck
end EtcdGrove
end Perennial
