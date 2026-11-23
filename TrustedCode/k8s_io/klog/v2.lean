/-
Trusted code for `k8s.io/klog/v2`, in namespace `k8s_io.klog.v2` like the generated package (`Code/k8s_io/klog/v2.toml`): its `init`
functions, which the models skip: each docstring says why that is unobservable to the
translated code (etcd-grove#32).
-/
module

public import Perennial.Golang.Defn

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace k8s_io.klog.v2

noncomputable section
section code
variable [GooseExts] [GoGlobalContext]

/-- `k8s.io/klog/v2`'s `init` (klog v2.140.0) at `klog_file.go:52`: `host = shortHostname(os.Hostname())` (an error leaves `"unknownhost"`). It cannot panic. No translated code reads what it writes (`host`). The model does nothing (etcd-grove#32; until 2026-11-22 the
trust-boundary axiom `initFuncsOk` said it returns). -/
def init.«0».impl : val :=
  λ: <>, #()

/-- `k8s.io/klog/v2`'s `init` (klog v2.140.0) at `klog.go:426`: the default `logging` thresholds, the `commandLine` flag set's flags (constant, distinct names: a duplicate would panic), and `newFlushDaemon` (built, not started). It cannot panic. Of what it writes, translated code reads only
`logging.verbosity` and `logging.filterLength` (`V`, translated since klog-leaves, 2026-11-23), to which
it writes 0 (`setVState(0, nil, false)`, `klog.go:434`): the zero value `logging` is allocated with
already has them. The model does nothing (etcd-grove#32; until 2026-11-22 the
trust-boundary axiom `initFuncsOk` said it returns). -/
def init.«1».impl : val :=
  λ: <>, #()

end code
end

end k8s_io.klog.v2

end Perennial
