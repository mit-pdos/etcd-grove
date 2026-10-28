/-
`(*wait.Group).Start(f)` (`k8s.io/apimachinery/pkg/util/wait/wait.go`, names-only:
`g.wg.Add(1); go func() { defer g.wg.Done(); f() }()`). **A named hypothesis** (outside client-go,
no axiom this round; the reflector's `watchWithResync` starts its resync goroutine with it; phase 4
of `notes/k8s-daemonset-plan.md`, fifth round): `?` in `etc/link-lean-first-k8scache.txt`.

Stated for a fresh group (its zero value) and one `Start`: `f` runs in a new goroutine (its
precondition given up to it, as `go`'s: it must not panic), and the caller gets what one later
`g.Wait()` needs (a one-shot triple: `Wait` returns, here learning nothing about `f`), which the
group's `WaitGroup` protocol would give.
-/
module

public import Proof.k8s_io.apimachinery.pkg.util.wait.Init

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.util.wait.Assumptions]

/-- `g.Start(f)` on a fresh group: `f` runs in a goroutine; one `g.Wait()` returns. -/
abbrev wait.Group.Start.spec : Prop :=
  ∀ (g : Loc) (f : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.wait ∗
      g ↦ (zero_val k8s_io.apimachinery.pkg.util.wait.Group) ∗
      ▷ WP (App (Val #f) (Val #())) {{ v, ⌜v.isPanic = false⌝ }} }}
    (App (Val (g @!! go.GoType.PointerType k8s_io.apimachinery.pkg.util.wait.Group.ty @!! go!"Start"))
      (Val #f))
  {{ RET #(); ∀ Φ : val → IProp GF, ▷ Φ #() -∗
      WP (App (Val (g @!! go.GoType.PointerType k8s_io.apimachinery.pkg.util.wait.Group.ty @!! go!"Wait"))
        (Val #())) {{ Φ }} }}

end spec

end EtcdGrove
end Perennial
