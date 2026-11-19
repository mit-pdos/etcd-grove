/- Lean-first (no Rocq counterpart).

`Main()` (`examples/goose/prophkv`): `Test`'s answer is `"a"` or `"b"` (`Test.spec`), so the
check passes and the panic is unreachable.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.goose.prophkv.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.goose.prophkv.Test

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace goose_prophkv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.goose.prophkv

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.goose.prophkv.Assumptions]

theorem Main.wp_proof (wp_Test : Test.spec (GF := GF)) : Main.spec (GF := GF) := by
  wp_start as #Hpkg
  wp_apply wp_Test as %r %Hg
  rcases Hg with rfl | rfl
  · wp_auto
    iapply HΦ
    itrivial
  · wp_auto
    iapply HΦ
    itrivial

end proof

end goose_prophkv
end EtcdGrove
end Perennial
