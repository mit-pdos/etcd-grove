/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/all/spawn.lean`: `go holdToken()` keeps its
fresh token here (`wp_fork_tok_self`; the goroutine never returns), the second goroutine gets the token
of its `go` (`wp_fork_tok_body`), hands it to `f`, calls `wg.Done()` (`sync.join`) and exits with the
`holdToken` token. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.all.spawn
public import Perennial.Proof.sync.Results

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_all

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.all.Assumptions]

theorem spawn.wp_proof (wp_holdToken : holdToken.spec (GF := GF) (hG := hG)) :
    spawn.spec (GF := GF) (hG := hG) := by
  intro wg f
  wp_start as ⟨Hdone, Hf⟩
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  (try wp_auto)
  -- `go holdToken()`: the goroutine never returns, its thread token stays here
  wp_apply wp_fork_tok_self as Htok
  · wp_apply wp_holdToken as Hfalse
    iexfalso; iexact Hfalse
  (try wp_auto)
  -- `go func() { f(); wg.Done() }()`, with the token of its `go`
  wp_apply wp_fork_tok_body $$ [Hdone Hf Htok f wg]
  · iintro Htok'
    (try wp_auto)
    ispecialize Hf $$ Htok'
    wp_bind (App (Val #f) (Val #()))
    iapply wp_wand $$ Hf
    iintro %v %Hv
    subst Hv
    (try wp_auto)
    wp_apply sync.join.WaitGroup.wp_Done iprop(True) _ $$ [Hdone]
    · iframe #; iframe
    (try wp_auto)
    iframe
  (try wp_auto)
  iapply HΦ; itrivial

end proof

end etcd_all
end EtcdGrove
end Perennial
