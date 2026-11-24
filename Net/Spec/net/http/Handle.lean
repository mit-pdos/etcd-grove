/-
`http.Handle(pattern, handler)`: register `handler` for `pattern` on `DefaultServeMux`. On the right
to register there (`muxOwn dmux Ps`, `MuxDefs.lean`), for a literal path pattern not yet registered
(`litPattern p`, `p ∉ Ps`: Go 1.22's conflict rule is then equality, so `register` does not panic) and
a non-nil handler (`Handle` panics on a nil one), it registers it: the right now covers `p :: Ps`,
and the mux routes `p` to `h` (`muxRoute`, persistent). Over both of the model's muxes (`use121`,
fixed at net/http's initialization by `GODEBUG`: the same routes for literal paths). The shared
rpc-over-HTTP design (L2), phase 7's S5 item 4. Lean-first.
-/
module

public import Net.Proof.net.http.MuxDefs
public import Net.Proof.net.http.PkgInit

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net.http

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

/-- See the file header. -/
abbrev Handle.spec : Prop :=
  ∀ (Ps : List GoString) (p : GoString) (h : GoInterface),
    litPattern p → p ∉ Ps → h ≠ interface.nil →
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ muxOwn (GF := GF) dmux Ps }}
    (App (App (Val (@! net.http.Handle)) (Val #p)) (Val #h))
  {{ RET #(); muxOwn (GF := GF) dmux (p :: Ps) ∗ muxRoute (GF := GF) dmux p h }}

end spec
end net.http
end Perennial
