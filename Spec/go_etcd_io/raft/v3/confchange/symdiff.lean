/-
`confchange.symdiff(l, r)` counts the symmetric difference of two id sets. Lean-first
(no Rocq counterpart); see `InvConfchange.lean`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvConfchange

@[expose] public section

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

/-- `symdiff(l, r)` returns the size of the symmetric difference, as a Go `int`: the count
is incremented once per id of `l` not in `r` and once per id of `r` not in `l`, so the
result is `symdiffN ml mr` modulo `2^64` (no bound is needed). (Until 2026-10-12 this
said only "at most 1 under `Simple`'s two inclusions".) -/
abbrev confchange.symdiff.spec : Prop :=
  ∀ (l r : Loc) (ml mr : GSet w64) (dql dqr : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ l ↦${dql} ml ∗ r ↦${dqr} mr }}
    (App (App (Val #(functions confchange.symdiff [])) (Val #l)) (Val #r))
  {{ RET #(W64 (symdiffN ml mr : Int)); l ↦${dql} ml ∗ r ↦${dqr} mr }}

end spec

end EtcdGrove
end Perennial
