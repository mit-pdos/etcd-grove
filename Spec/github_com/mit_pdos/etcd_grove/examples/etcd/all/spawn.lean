/-
`spawn(wg, f)` (`examples/etcd/all/all.go`): `go holdToken()`, then `go func() { f(); wg.Done() }()`.
Lean-first (no Rocq counterpart).

**The triple:** from a `Done` right of the wait group in Perennial's join idiom (`sync.join.ownDone`,
as `wg.Add` gives it; its proposition `True`) and `f`'s triple given a thread token (`f` runs on its
own goroutine with the token of its `go`, returns `#()` and need not give a token back), `spawn`
returns. The `holdToken` goroutine's token is the one `f`'s goroutine exits with, after `wg.Done()`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.all.holdToken
public import Perennial.Proof.sync.WaitGroupJoin

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_all

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.all.Assumptions]

/-- See the file header. -/
abbrev spawn.spec : Prop :=
  ∀ (wg : Loc) (f : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.all ∗
      sync.join.ownDone wg iprop(True) ∗
      ▷ (threadTok -∗ WP (App (Val #f) (Val #())) {{ v, ⌜v = #()⌝ }}) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.all.spawn)) (Val #wg)) (Val #f))
  {{ RET #(); True }}

end spec

end etcd_all
end EtcdGrove
end Perennial
