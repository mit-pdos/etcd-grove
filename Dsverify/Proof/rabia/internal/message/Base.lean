/-
The package fact of `rabia.internal.message` (the lab's `msgState`, the part the framing needs):
the globals `errFrameTooLarge` and `errFrameTooLong` hold non-`nil` errors, read-only for good
(`errors.New` errors, which Go never writes after initialization). `BufRead` returns the first, a
frame longer than the caller's buffer (N6); `BufWrite` the second, a payload longer than a `uint32`
header (N8).
-/
module

public import Dsverify.GeneratedProof.rabia.internal.message
public import Net.Proof.net.Base
public import Dsverify.Proof.github_com.gogo.protobuf.gogoproto.Base
public import Dsverify.Proof.github_com.gogo.protobuf.proto.Base
public import Proof.bufio.PkgInit
public import Perennial.Proof.encoding.binary.Base
public import Perennial.Proof.errors.Base
public import Perennial.Proof.fmt.Base
public import Perennial.Proof.io.Base
public import Perennial.Proof.strconv.Base
public import Perennial.Proof.math.Base
public import Perennial.Proof.math.bits.Base
public import Perennial.Proof.reflect.Base
public import Perennial.Proof.strings.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace rabia.internal.message

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- See the file header. -/
def msgFact : IProp GF :=
  iprop(∃ e1 e2 : GoInterface, globalAddr errFrameTooLarge ↦□ e1 ∗ globalAddr errFrameTooLong ↦□ e2 ∗
    ⌜e1 ≠ interface.nil ∧ e2 ≠ interface.nil⌝)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.rabia.internal.message :=
  define_is_pkg_init (msgFact (GF := GF))
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.rabia.internal.message :=
  build_get_is_pkg_init_wf

end def_

end rabia.internal.message
end Perennial
