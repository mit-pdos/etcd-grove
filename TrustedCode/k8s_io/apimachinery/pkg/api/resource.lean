/-
Trusted code for `k8s.io/apimachinery/pkg/api/resource`, in namespace `k8s_io.apimachinery.pkg.api.resource` like the generated package (`Code/k8s_io/apimachinery/pkg/api/resource.toml`): its `init`
function, which the model skip: each docstring says why that is unobservable to the
translated code (etcd-grove#32).
-/
module

public import Perennial.Golang.Defn

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace k8s_io.apimachinery.pkg.api.resource

noncomputable section
section code
variable [GooseExts] [GoGlobalContext]

/-- `k8s.io/apimachinery/pkg/api/resource`'s `init` (apimachinery `0b7d352f711c`) at `scale_int.go:32`: sets `intPool.New` (the constructor of the package's `sync.Pool` of `big.Int`s). It cannot panic. No translated code reads what it writes (the package translates no function body). The model does nothing (etcd-grove#32; until 2026-11-22 the
trust-boundary axiom `initFuncsOk` said it returns). -/
def init.«0».impl : val :=
  λ: <>, #()

end code
end

end k8s_io.apimachinery.pkg.api.resource

end Perennial
