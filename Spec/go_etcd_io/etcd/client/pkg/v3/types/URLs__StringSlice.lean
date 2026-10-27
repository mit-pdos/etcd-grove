/-
`types.URLs.StringSlice()`: names-only. Lean-first (no Rocq counterpart); the server-construction unit, stage N0 (2026-10-16, D13:
`notes/decisions.md`), for `NewServer`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvServer

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

/-- `us.StringSlice()` through a non-nil pointer to the `URLs` value (as `NewServer` calls it on its
configuration's field): some slice of strings. (Not stated over the value's points-to: `URLs` is
an axiomatized type, whose generated points-to instance is `sorry`.) -/
abbrev types.URLs.StringSlice.spec : Prop :=
  ∀ (p : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types ∗ ⌜p ≠ null⌝ }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.types.URLs.ty @!!
      go!"StringSlice")) (Val #()))
  {{ (sl : GoSlice), RET #sl; True }}

end spec

end EtcdGrove
end Perennial
