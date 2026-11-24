/-
The package fact of `net/http` (the part `Net/`'s model of it, `models/net/http`): `True`, no
proof reads a variable of the package. Its well-formedness instance (`build_get_is_pkg_init_wf`)
names the facts of every package its initializer reaches (its `PkgInfo` imports, recursively): the
part's names-only translations (`net/textproto`, `mime/multipart`, `net/http/internal/ascii`,
`httpguts`: their `Base.lean`), the main tree's (`bufio`, `net/url`, `path`, `crypto/tls`: their
`PkgInit.lean`) and Perennial's. Shared by `Net/` (its interim `wp_initialize'`, `Init.lean`) and
`Dsverify/` (its hypothesis `InitHyp`, `Dsverify/Proof/net/http/Init.lean`) (rpc-driver,
2026-11-24: until then declared in `Dsverify/Proof/net/http/Init.lean`).
-/
module

public import Net.GeneratedProof.net.http
public import Net.Proof.net.Base
public import Proof.bufio.PkgInit
public import Proof.net.url.PkgInit
public import Proof.path.PkgInit
public import Proof.crypto.tls.PkgInit
public import Net.Proof.net.textproto.Base
public import Net.Proof.mime.multipart.Base
public import Net.Proof.net.http.internal.ascii.Base
public import Net.Proof.vendor.golang_org.x.net.http.httpguts.Base
public import Perennial.Proof.fmt.Base
public import Perennial.Proof.strings.Base
public import Perennial.Proof.strconv.Base
public import Perennial.Proof.sync.Base
public import Perennial.Proof.sync.atomic.Base
public import Perennial.Proof.runtime.Base
public import Perennial.Proof.slices.Base
public import Perennial.Proof.log.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace net.http

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The package's fact: `True`, with its imports' facts (`define_is_pkg_init`). -/
instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.net.http :=
  define_is_pkg_init iprop(True)
/-- Its well-formedness: `get_is_pkg_init` gives its fact and, recursively, the facts of every
package its initializer reaches (its `PkgInfo` imports, which are the packages whose initializers
`initialize'` runs: `build_get_is_pkg_init_wf`). -/
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.net.http :=
  build_get_is_pkg_init_wf

end def_

end net.http
end Perennial
