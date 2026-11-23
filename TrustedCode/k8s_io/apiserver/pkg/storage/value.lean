/-
Trusted code for `k8s.io/apiserver/pkg/storage/value`, in namespace `k8s_io.apiserver.pkg.storage.value` like the generated package (`Code/k8s_io/apiserver/pkg/storage/value.toml`): its `init`
function, which the model skip: each docstring says why that is unobservable to the
translated code (etcd-grove#32).
-/
module

public import Perennial.Golang.Defn

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace k8s_io.apiserver.pkg.storage.value

noncomputable section
section code
variable [GooseExts] [GoGlobalContext]

/-- `k8s.io/apiserver/pkg/storage/value`'s `init` (apiserver `9c4ec15b8038`) at `transformer.go:32`: `RegisterMetrics()`, a `sync.Once` around five `legacyregistry.MustRegister` calls of constant, unique metric names. It cannot panic. No translated code reads what it writes (the package translates no function body, and nothing translated calls into it). The model does nothing (etcd-grove#32; until 2026-11-22 the
trust-boundary axiom `initFuncsOk` said it returns). -/
def init.«0».impl : val :=
  λ: <>, #()

end code
end

end k8s_io.apiserver.pkg.storage.value

end Perennial
