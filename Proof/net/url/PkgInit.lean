/-
The package-initialization instance of `net/url` (the element type of `types.URLs`, unit
N4, 2026-10-17; zap's sink registry's factories' parameter): fact `urlInit` (phase 7 S5, 2026-11-24,
`True` until then): the character-class table `table` holds `encTableList`
(`Proof/net/url/Escape.lean`), read-only for good. Moved out of the apply
package's `Base.lean` (prove-zap3, 2026-11-21) so that zap's instances, which import it since zap's
`_sinkRegistry` is translated, do not import the server.
-/
module

public import GeneratedProof.net.url
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.strings.Base
public import Proof.net.url.Escape

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

namespace net.url

/-- net/url's fact: `table` (`encoding_table.go`) holds the entries Go's generator computes
(`encTableList`), and nothing writes it. -/
def urlInit : IProp GF :=
  iprop(∃ t : GoArray w8 256, globalAddr table ↦□ t ∗ ⌜t.arr = encTableList⌝)

instance urlInit_persistent : Persistent (urlInit (GF := GF)) := by
  unfold urlInit; infer_instance

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.net.url :=
  define_is_pkg_init urlInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.net.url :=
  build_get_is_pkg_init_wf

end net.url

end init

end Perennial
