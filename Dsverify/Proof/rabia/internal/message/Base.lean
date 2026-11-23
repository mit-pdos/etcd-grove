/-
The package fact of `rabia.internal.message`: `True` (no package-level state yet (notes/dsv-rabia.md: the lab's facts are to be ported)).
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

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.rabia.internal.message :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.rabia.internal.message :=
  build_get_is_pkg_init_wf

end def_

end rabia.internal.message
end Perennial
