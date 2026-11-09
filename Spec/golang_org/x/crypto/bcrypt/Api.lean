/-
# `golang.org/x/crypto/bcrypt`: the trust boundary (batch 3d)

bcrypt (`golang.org/x/crypto` v0.57.0 at the pin) is translated names only (`Code/golang_org/x/
crypto/bcrypt.toml`): its two functions etcd calls are **assumed**, each file says why they are
true of the library's code at the pin.

Stated over W0's two opaque relations (`Spec/go_etcd_io/etcd/api/v3/Model.lean`, which calls them
3d's boundary): `EtcdModel.pwHash pw h` (**`h` is a bcrypt hash of `pw`**: `$2a$<cost>$`, a salt and
the hash of `pw` under it; what `GenerateFromPassword` returns) and `EtcdModel.pwMatch h pw` (**`pw`
passes the check against `h`**: exactly when `CompareHashAndPassword(h, pw)` is `nil`).

The one fact etcd relies on is bcrypt's **correctness**, W0's law `pwHash_match` (a hash matches
its own password). Nothing is assumed about a password that is not `pw`: bcrypt reads at most
the first 72 bytes of a password (a longer password passes when bcrypt's key, `pw` with a NUL appended, cut at 72 bytes, is the same:
`nonissues/etcd-auth-password-72-byte-prefix.md`), and a hash function has collisions; "a wrong
password fails" would be a false universal (PRINCIPLES, "An assumption states the physical fact the
code relies on").
-/
module

public import GeneratedProof.golang_org.x.crypto.bcrypt
public import Spec.PkgInit.golang_org.x.crypto.bcrypt
public import Spec.go_etcd_io.etcd.api.v3.State

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Bcrypt

open Iris Iris.BI

end Bcrypt
end EtcdGrove
end Perennial
