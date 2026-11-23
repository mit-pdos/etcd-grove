/-
Trusted code for `k8s.io/apiserver/pkg/audit`, in namespace `k8s_io.apiserver.pkg.audit` like the generated package (`Code/k8s_io/apiserver/pkg/audit.toml`): its `init`
functions, which the models skip: each docstring says why that is unobservable to the
translated code (etcd-grove#32).
-/
module

public import Perennial.Golang.Defn

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace k8s_io.apiserver.pkg.audit

noncomputable section
section code
variable [GooseExts] [GoGlobalContext]

/-- `k8s.io/apiserver/pkg/audit`'s `init` (apiserver `9c4ec15b8038`) at `metrics.go:80`: `legacyregistry.MustRegister` of the four `apiserver_audit_*` counters. It panics only on a duplicate or invalid metric name, and these are constant and unique (every program importing the package starts). No translated code reads what it writes: the package translates no reader of the counters, and the only translated registration into `legacyregistry` (the daemon set controller's metrics) uses other names. The model does nothing (etcd-grove#32; until 2026-11-22 the
trust-boundary axiom `initFuncsOk` said it returns). -/
def init.«0».impl : val :=
  λ: <>, #()

/-- `k8s.io/apiserver/pkg/audit`'s `init` (apiserver `9c4ec15b8038`) at `scheme.go:33`: registers the audit types into `audit.Scheme` (`utilruntime.Must` of `AddToScheme`s of fixed types), which panics only on a registration error that fixed types do not have. No translated code reads what it writes (the package's translated function, `GetAuditIDTruncated`, reads no scheme). The model does nothing (etcd-grove#32; until 2026-11-22 the
trust-boundary axiom `initFuncsOk` said it returns). -/
def init.«1».impl : val :=
  λ: <>, #()

end code
end

end k8s_io.apiserver.pkg.audit

end Perennial
