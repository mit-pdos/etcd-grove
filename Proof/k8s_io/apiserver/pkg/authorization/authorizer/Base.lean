/-
Lean-first (no Rocq counterpart).

Package initialization instances for Kubernetes' conditional authorization (KEP-5681;
`k8s.io/apiserver/pkg/authorization/{authorizer,union}`, with bodies, project `k8s-authz` of
`etc/goose.py`) and the packages they import that have none yet: apimachinery's `util/validation`
(names only) and the apiserver's `authentication/user` (names only). Every fact is `True` but the
authorizer package's (`authorizerInit`: `ErrorConditionEvaluationNotSupported` holds some error,
read-only for good: the driver's and `AuthorizerFunc`'s `EvaluateConditions` return it). The
other imports' instances are in `storage/cacher/Base.lean` (and the modules it imports).
These are assumptions about package initialization only once an `Init.lean` proves a package's
`wp_initialize'` from them (`etc/gen-init.py`).
-/
module

public import GeneratedProof.k8s_io.apiserver.pkg.authorization.union
public import Proof.k8s_io.apiserver.pkg.storage.cacher.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace k8s_io.apiserver.pkg.authorization.authorizer

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance k8s_io_apimachinery_pkg_util_validation_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.validation :=
  define_is_pkg_init iprop(True)
instance k8s_io_apimachinery_pkg_util_validation_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.validation :=
  build_get_is_pkg_init_wf

-- (prove-k8s2, 2026-11-20) `authentication/user`'s instances moved to `storage/etcd3/Base.lean`:
-- `util/flowcontrol` imports it since its `var _ fmt.GoStringer = RequestDigest{}` is translated

/-- The authorizer package's fact: `ErrorConditionEvaluationNotSupported` (`errors.New(...)`,
`interfaces.go`) holds some error, and nothing writes it. -/
def authorizerInit : IProp GF :=
  iprop(∃ e : GoInterface, globalAddr ErrorConditionEvaluationNotSupported ↦□ e)

instance authorizerInit_persistent : Persistent (authorizerInit (GF := GF)) := by
  unfold authorizerInit; infer_instance

instance k8s_io_apiserver_pkg_authorization_authorizer_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apiserver.pkg.authorization.authorizer :=
  define_is_pkg_init authorizerInit
instance k8s_io_apiserver_pkg_authorization_authorizer_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apiserver.pkg.authorization.authorizer :=
  build_get_is_pkg_init_wf

instance k8s_io_apiserver_pkg_authorization_union_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apiserver.pkg.authorization.union :=
  define_is_pkg_init iprop(True)
instance k8s_io_apiserver_pkg_authorization_union_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apiserver.pkg.authorization.union :=
  build_get_is_pkg_init_wf

end init

end k8s_io.apiserver.pkg.authorization.authorizer
end Perennial
