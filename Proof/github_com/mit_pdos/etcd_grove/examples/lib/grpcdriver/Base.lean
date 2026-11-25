/-
gRPC's robustness driver (`examples/lib/grpcdriver`, notes/library-drivers.md): its package fact,
`drvFacts` (its variable `reached` holds a function that returns).
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.Base
public import Perennial.Proof.github_com.goose_lang.primitive.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

open Iris Iris.BI

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The package's fact** (`drvFacts`, persistent): its variable `reached` holds a function whose
calls return (its body is empty); its initializer stores it and never writes it again. -/
def drvFacts : IProp GF :=
  iprop(∃ f : GoFunc, globalAddr reached ↦□ f ∗
    □ ∀ s : GoString, WP (App (Val #f) (Val #s)) {{ v, ⌜v = #()⌝ }})

instance drvFacts_persistent : Persistent (drvFacts (GF := GF)) := by
  unfold drvFacts; infer_instance

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver :=
  define_is_pkg_init drvFacts
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver :=
  build_get_is_pkg_init_wf

/-- The package's fact, from its `isPkgInit`. -/
theorem drvFacts_of_init :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver ⊢
      drvFacts := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

end init

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
