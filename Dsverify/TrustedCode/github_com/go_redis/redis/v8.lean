/-
Trusted definitions of `github.com/go-redis/redis/v8`, in namespace `github_com.go_redis.redis.v8` like the generated package: its
initialization only (notes/dsv-quepaxa.md; the lab's quepaxa-bump-1 made the same kind of no-op
models of its names-only packages' initializers, `lean.trusted_init`). `ErrClosed`, `errClusterNoNodes`, `errRingShardsDown`, `_` do nothing
(the package's goose config lists them as trusted and leaves them out of the translation). The
claim: the package is translated names only, no call of the verified program reaches it except
through calls whose specs are hypotheses of the port, so its initialization's tables and settings
are not observed by anything proved.
-/
module

public import Perennial.Golang.Defn.Pre

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace github_com.go_redis.redis.v8
section code
variable [GooseExts] [GoGlobalContext]

def ErrClosed.init : val :=
  λ: <>, #()
def errClusterNoNodes.init : val :=
  λ: <>, #()
def errRingShardsDown.init : val :=
  λ: <>, #()
def «_».init : val :=
  λ: <>, #()

end code
end github_com.go_redis.redis.v8

end Perennial
