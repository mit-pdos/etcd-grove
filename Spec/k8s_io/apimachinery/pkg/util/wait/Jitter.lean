/-
`wait.Jitter(d, f)` (names-only; k8s 7f-5, T5-d, `notes/k8s-7f5-freeze.md`): returns some
duration, for any `d` and any float `f` (its bits), with no premise. Go: `wait.go:92-98`,
`duration + time.Duration(jitterRand()*maxFactor*float64(duration))`; the float-to-int conversion is
arbitrary in Perennial's model (`Float64Semantics`) and in Go (implementation-defined out of range),
and it never panics. Evidence: `TestJitter`. Reached only on the etcd3 watcher's too-large-RV error
path (`watcher.go:463`). The trust boundary: an axiom, `Proof/k8s_io/apimachinery/pkg/util/wait/Jitter.lean`.
Lean-first.
-/
module

public import Proof.k8s_io.apimachinery.pkg.util.wait.Init

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

/-- See the file header. -/
abbrev wait.Jitter.spec : Prop :=
  ∀ (d f : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.wait }}
    (App (App (Val (@! k8s_io.apimachinery.pkg.util.wait.Jitter)) (Val #d)) (Val #f))
  {{ (j : w64), RET #j; True }}

end spec

end EtcdGrove
end Perennial
