/-
# `golang.org/x/crypto/bcrypt`: the trust boundary (batch 3d)

bcrypt (`golang.org/x/crypto` v0.57.0 at the pin) is translated names only (`Code/golang_org/x/
crypto/bcrypt.toml`): its two functions etcd calls are **assumed**, each file says why they are
true of the library's code at the pin.

* `hashOf h pw` (pure, opaque): **`h` is a bcrypt hash of the password `pw`** (`$2a$<cost>$`, a
  salt and the hash of `pw` under it): what `GenerateFromPassword(pw, cost)` returns.

The one fact etcd relies on is bcrypt's **correctness**: `CompareHashAndPassword(h, pw)` is `nil`
for a hash `h` of `pw`. Nothing is assumed about a password that is not `pw`: bcrypt reads at most
the first 72 bytes of a password (a longer password whose first 72 bytes are a 72-byte `pw` passes,
`nonissues/etcd-auth-password-72-byte-prefix.md`), and a hash function has collisions; "a wrong
password fails" would be a false universal (PRINCIPLES, "An assumption states the physical fact the
code relies on").
-/
module

public import GeneratedProof.golang_org.x.crypto.bcrypt
public import Spec.PkgInit.golang_org.x.crypto.bcrypt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Bcrypt

open Iris Iris.BI

/-- **`h` is a bcrypt hash of the password `pw`** (see the header). -/
opaque hashOf (h pw : List w8) : Prop

end Bcrypt
end EtcdGrove
end Perennial
