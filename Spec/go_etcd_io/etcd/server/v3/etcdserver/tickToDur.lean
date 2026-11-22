/-
`tickToDur(ticks, tickMs)` (`server.go`: `fmt.Sprintf("%v", time.Duration(ticks)*time.Duration(tickMs)*time.Millisecond)`,
the formatted duration of `adjustTicks`'s logs). Lean-first (no Rocq counterpart); prove-ps2-srv (2026-11-22).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `tickToDur(ticks, tickMs)`: some string (the duration `ticks * tickMs` milliseconds, as
`time.Duration.String` formats it under `%v`). -/
abbrev tickToDur.spec : Prop :=
  ∀ (ticks tickMs : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.tickToDur)) (Val #ticks)) (Val #tickMs))
  {{ (s : GoString), RET #s; True }}

end spec

end EtcdGrove
end Perennial
