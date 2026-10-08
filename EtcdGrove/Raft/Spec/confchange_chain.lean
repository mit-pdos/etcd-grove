/-
`confchange.chain(chg, ops...)` runs the ops in order, each on the config and progress
map the previous one returned. Lean-first (no Rocq counterpart); see
`InvConfchange.lean`.
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

/-- `chain` threads a (`Config`, progress map) pair through the ops: op `i` is called
on `chg` with the pair in its tracker and must return a pair without error (`opSpec`,
`InvConfchange.lean`); the result is the last pair, with `nil`. `I i` is the caller's
invariant on the pair before op `i`; nothing is said of the pair after an op fails,
because on this path no op does. -/
abbrev confchange.chain.spec : Prop :=
  ∀ (chg : confchange.Changer) (ops : GoSlice) (fs : List GoFunc) (dq : DFrac)
    (I : Nat → tracker.Config → Loc → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ ops ↦*{dq} fs ∗ I 0 chg.Tracker'.Config' chg.Tracker'.Progress' ∗
      □ (∀ (i : Nat) (f : GoFunc), ⌜fs[i]? = some f⌝ -∗ opSpec f chg (I i) (I (i + 1))) }}
    (App (App (Val #(functions confchange.chain [])) (Val #chg)) (Val #ops))
  {{ (cfg : tracker.Config) (prs : Loc), RET (PairV (PairV #cfg #prs) #interface.nil);
      ops ↦*{dq} fs ∗ I fs.length cfg prs }}

end spec

end EtcdGrove
end Perennial
