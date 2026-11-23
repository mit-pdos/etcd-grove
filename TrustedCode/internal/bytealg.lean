/-
Trusted code for `internal/bytealg`, in namespace `internal.bytealg` like the generated package (`Code/internal/bytealg.toml`): its `init`
function, which the model skip: each docstring says why that is unobservable to the
translated code (etcd-grove#32).
-/
module

public import Perennial.Golang.Defn

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace internal.bytealg

noncomputable section
section code
variable [GooseExts] [GoGlobalContext]

/-- `internal/bytealg`'s `init` (go1.27.3) at `index_amd64.go:11`: `MaxLen = 63` with AVX2, else `31` (`cpu.X86.HasAVX2`). It cannot panic. No translated code reads what it writes: the package translates only `LastIndexByteString`, which does not read `MaxLen`, and nothing translated names it. The model does nothing (etcd-grove#32; until 2026-11-22 the
trust-boundary axiom `initFuncsOk` said it returns). -/
def init.«0».impl : val :=
  λ: <>, #()

end code
end

end internal.bytealg

end Perennial
