/-
Trusted code for `k8s.io/client-go/util/watchlist`, in namespace `k8s_io.client_go.util.watchlist` like the generated package (`Code/k8s_io/client_go/util/watchlist.toml`): its `init`
function, which the model skip: each docstring says why that is unobservable to the
translated code (etcd-grove#32).
-/
module

public import Perennial.Golang.Defn

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace k8s_io.client_go.util.watchlist

noncomputable section
section code
variable [GooseExts] [GoGlobalContext]

/-- `k8s.io/client-go/util/watchlist`'s `init` (client-go `569675c57fa3`) at the package's only `init`: `utilruntime.Must(metainternalversion.AddToScheme(scheme))`, fixed registrations into the package's skipped `scheme`, which cannot fail. No translated code reads what it writes: its one translated caller's function, `DoesClientNotSupportWatchListSemantics`, does not use `scheme`. The model does nothing (etcd-grove#32; until 2026-11-22 the
trust-boundary axiom `initFuncsOk` said it returns). -/
def init.«0».impl : val :=
  λ: <>, #()

end code
end

end k8s_io.client_go.util.watchlist

end Perennial
