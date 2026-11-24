/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): `setPre(a, k, v)`: a copy of `a` with element `k` set.
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

/-- `setPre(a, k, v)`: a new slice, `a` with element `k` replaced by `v` (`List.set`; Lean: a
successor's `undo := s.undo.set n u`). -/
abbrev setPre.spec : Prop :=
  ∀ (a : GoSlice) (us : List (Option Pre)) (k : w64) (v : Loc) (u : Option Pre),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      undoRO a us ∗ preRO v u ∗ ⌜0 ≤ sint.Z k ∧ sint.Z k < us.length⌝ }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.setPre)) (Val #a)) (Val #k)) (Val #v))
  {{ (out : GoSlice), RET #out; undoRO out (us.set (sint.nat k) u) }}

end spec

end AntCheck
end EtcdGrove
end Perennial
