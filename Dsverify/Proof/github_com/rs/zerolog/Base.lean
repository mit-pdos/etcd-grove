/-
The package fact of `github_com.rs.zerolog`: `True` (names only here (no model: notes/dsv-rabia.md), no variables).
-/
module

public import Dsverify.GeneratedProof.github_com.rs.zerolog
public import Net.Proof.net.Base
public import Perennial.Proof.bytes.Base
public import Perennial.Proof.context.Base
public import Perennial.Proof.fmt.Base
public import Perennial.Proof.io.Base
public import Perennial.Proof.math.Base
public import Perennial.Proof.math.rand.Base
public import Perennial.Proof.sort.Base
public import Perennial.Proof.strconv.Base
public import Perennial.Proof.strings.Base
public import Perennial.Proof.sync.Base
public import Perennial.Proof.sync.atomic.Base
public import Perennial.Proof.time.Base
public import Perennial.Proof.unsafe.Base
public import Perennial.Proof.runtime.Base
public import Proof.encoding.json.Base
public import Proof.os.Base
public import Proof.path.filepath.Base
public import Dsverify.Proof.io.ioutil.Base
public import Dsverify.Proof.github_com.rs.zerolog.internal.json.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.rs.zerolog

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.rs.zerolog :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.rs.zerolog :=
  build_get_is_pkg_init_wf

end def_

end github_com.rs.zerolog
end Perennial
