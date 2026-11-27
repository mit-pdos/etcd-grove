/- Lean-first (no Rocq counterpart).

`dirFits(r)` (`examples/mvccfull/start.go`, P3 of the pure-premise plan, 2026-11-24): whether the
directory `r` leaves room below it, `Fs.DirFits r` (under 3800 bytes, every 256-byte window holding a
`/`): it answers exactly that.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Base
public import GooseLang.Ext.Fs.PathFitsLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]

/-- See the file header. -/
abbrev dirFits.spec : Prop :=
  ∀ (r : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.mvccfull.dirFits)) (Val #r))
  {{ (b : Bool), RET #b; ⌜b = true ↔ Fs.DirFits r⌝ }}

end spec

end mvccfull
end EtcdGrove
end Perennial
