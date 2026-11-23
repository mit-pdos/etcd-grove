/-
Trusted code for `k8s.io/apimachinery/pkg/apis/meta/internalversion`, in namespace `k8s_io.apimachinery.pkg.apis.meta.internalversion` like the generated package (`Code/k8s_io/apimachinery/pkg/apis/meta/internalversion.toml`): its `init`
functions, which the models skip: each docstring says why that is unobservable to the
translated code (etcd-grove#32).
-/
module

public import Perennial.Golang.Defn

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace k8s_io.apimachinery.pkg.apis.meta.internalversion

noncomputable section
section code
variable [GooseExts] [GoGlobalContext]

/-- `k8s.io/apimachinery/pkg/apis/meta/internalversion`'s `init` (apimachinery `0b7d352f711c`) at `register.go:86`: `localSchemeBuilder.Register(addToGroupVersion)`, appending to the skipped scheme builder. It cannot panic. No translated code reads what it writes: only untranslated code (`AddToScheme`, from `util/watchlist`'s own `init`) uses the builder. The model does nothing (etcd-grove#32; until 2026-11-22 the
trust-boundary axiom `initFuncsOk` said it returns). -/
def init.«0».impl : val :=
  λ: <>, #()

/-- `k8s.io/apimachinery/pkg/apis/meta/internalversion`'s `init` (apimachinery `0b7d352f711c`) at `zz_generated.conversion.go:32`: `localSchemeBuilder.Register(RegisterConversions)`, the same. It cannot panic; No translated code reads what it writes. The model does nothing (etcd-grove#32; until 2026-11-22 the
trust-boundary axiom `initFuncsOk` said it returns). -/
def init.«1».impl : val :=
  λ: <>, #()

end code
end

end k8s_io.apimachinery.pkg.apis.meta.internalversion

end Perennial
