/-
`clockwork.NewRealClock()` (names only): the trust boundary of the spec-first pilot's clock
(`Proof/github_com/jonboulle/clockwork/Defs.lean`, which says why it is true). Lean-first.
-/
module

public import Proof.github_com.jonboulle.clockwork.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `clockwork.NewRealClock()`: a clock over the real clock (`clockwork.clockOk clockwork.realClock`). -/
abbrev clockwork.NewRealClock.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.jonboulle.clockwork }}
    (App (Val (@! _root_.Perennial.github_com.jonboulle.clockwork.NewRealClock)) (Val #()))
  {{ (clk : GoInterface), RET #clk; clockwork.clockOk clockwork.realClock clk }}

end spec

end EtcdGrove
end Perennial
