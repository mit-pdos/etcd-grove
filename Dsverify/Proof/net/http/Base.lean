/-
The package fact of `net.http` (the net/http model, `models/net/http`), for the craq kit (notes/dsv-craq.md,
hypothesis H1): `True` for now (the fact a proof needs is added with that proof). `Net/` has no package fact for the model yet (plan phase 5.2, item 5); its
initialization is the hypothesis `Init.lean`'s `InitHyp`.
-/
module

public import Net.GeneratedProof.net.http
public import Net.Proof.net.Base
public import Proof.bufio.PkgInit
public import Perennial.Proof.context.Base
public import Perennial.Proof.errors.Base
public import Perennial.Proof.fmt.Base
public import Perennial.Proof.io.Base
public import Perennial.Proof.runtime.Base
public import Perennial.Proof.strconv.Base
public import Perennial.Proof.strings.Base
public import Perennial.Proof.sync.Base
public import Perennial.Proof.sync.atomic.Base
public import Perennial.Proof.time.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace net.http

/-! The facts of net/http's imports that have none in this part's closure (names-only
translations; each `True`, as their owners' elsewhere in the tree). -/
section deps
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance dep_bytealg_inst : IsPkgInit (IProp GF) pkg_id.internal.bytealg := define_is_pkg_init iprop(True)
instance dep_bytealg_wf : GetIsPkgInitWf (IProp GF) pkg_id.internal.bytealg := build_get_is_pkg_init_wf
instance dep_path_inst : IsPkgInit (IProp GF) pkg_id.path := define_is_pkg_init iprop(True)
instance dep_path_wf : GetIsPkgInitWf (IProp GF) pkg_id.path := build_get_is_pkg_init_wf
instance dep_tls_inst : IsPkgInit (IProp GF) pkg_id.crypto.tls := define_is_pkg_init iprop(True)
instance dep_tls_wf : GetIsPkgInitWf (IProp GF) pkg_id.crypto.tls := build_get_is_pkg_init_wf
instance dep_url_inst : IsPkgInit (IProp GF) pkg_id.net.url := define_is_pkg_init iprop(True)
instance dep_url_wf : GetIsPkgInitWf (IProp GF) pkg_id.net.url := build_get_is_pkg_init_wf
instance dep_textproto_inst : IsPkgInit (IProp GF) pkg_id.net.textproto := define_is_pkg_init iprop(True)
instance dep_textproto_wf : GetIsPkgInitWf (IProp GF) pkg_id.net.textproto := build_get_is_pkg_init_wf
instance dep_httpguts_inst : IsPkgInit (IProp GF) pkg_id.vendor.golang_org.x.net.http.httpguts :=
  define_is_pkg_init iprop(True)
instance dep_httpguts_wf : GetIsPkgInitWf (IProp GF) pkg_id.vendor.golang_org.x.net.http.httpguts :=
  build_get_is_pkg_init_wf

end deps

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : net.http.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.net.http :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.net.http :=
  build_get_is_pkg_init_wf

end def_

end net.http
end Perennial
