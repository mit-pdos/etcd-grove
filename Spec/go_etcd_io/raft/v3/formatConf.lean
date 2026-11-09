/-
Lean-first (no Rocq counterpart): `formatConf` (`state_trace.go`), a configuration half's ids as
decimal strings, as a traced event's `conf` (Q8 stage 1, slice 2, 2026-11-09).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedCap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `formatConf(s)`: a fresh slice of the ids of `s`, each in decimal (`decStr`, `strconv.FormatUint(v,
10)`), in order; for a nil `s` the empty `[]string{}`. -/
abbrev formatConf.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (xs : List w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ sl ↦*{dq} xs }}
    (App (Val #(functions formatConf [])) (Val #sl))
  {{ (out : GoSlice), RET #out; sl ↦*{dq} xs ∗ out ↦* xs.map decStr }}

end spec

end EtcdGrove
end Perennial
