/-
`confchange.symdiff(l, r)` counts the symmetric difference of two id sets. Lean-first
(no Rocq counterpart); see `InvConfchange.lean`.
-/
import EtcdGrove.Raft.InvConfchange

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `symdiff` reads both maps and returns a count. The postcondition states the one
fact `Simple` needs of it: when `l ⊆ r` and `r` adds at most one id `x` to `l`, the
count is at most `1`. (The exact count would need a bound on the maps' sizes to rule
out `n++` wrapping; nothing on this path has one.) -/
abbrev confchange.symdiff.spec : Prop :=
  ∀ (l r : Loc) (ml mr : GMap w64 Unit) (dql dqr : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ l ↦${dql} ml ∗ r ↦${dqr} mr }}
    (App (App (Val #(functions confchange.symdiff [])) (Val #l)) (Val #r))
  {{ (n : w64), RET #n; l ↦${dql} ml ∗ r ↦${dqr} mr ∗
      ⌜(∀ k, (ml !! k).isSome → (mr !! k).isSome) →
        ∀ x, (∀ k, (mr !! k).isSome → (ml !! k).isSome ∨ k = x) →
        0 ≤ sint.Z n ∧ sint.Z n ≤ 1⌝ }}

end spec

end EtcdGrove
end Perennial
