/-
`clockwork.NewRealClock`: the trust boundary (`github.com/jonboulle/clockwork` is names-only).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.jonboulle.clockwork.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `clockwork.NewRealClock()` returns a clock (`clockwork.isClock`: over `time.Now` and
`time.After`). -/
abbrev clockwork.NewRealClock.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.jonboulle.clockwork }}
    (App (Val (@! _root_.Perennial.github_com.jonboulle.clockwork.NewRealClock)) (Val #()))
  {{ (clk : GoInterface), RET #clk; clockwork.isClock clk }}

end spec

end EtcdGrove
end Perennial
