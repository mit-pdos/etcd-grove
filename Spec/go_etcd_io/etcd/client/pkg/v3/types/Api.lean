/-
# `client/pkg/v3/types` (batch 1c): member ids and URL lists

* `urlsValid urls` (an opaque pure property of the strings): `NewURLs` accepts them (each parses as a
  URL with scheme `http`, `https`, `unix` or `unixs`, a `host:port` for `http(s)`, no path, query or
  fragment). Opaque because Go's `url.Parse` has no model here; its meaning is `NewURLs.spec`.
* `idStr x`: `ID(x).String()`, lowercase hexadecimal without leading zeros (`strconv.FormatUint(x,
  16)`).
-/
module

public import GeneratedProof.go_etcd_io.etcd.client.pkg.v3.types
public import Spec.PkgInit.go_etcd_io.etcd.client.pkg.v3.types

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Types

open Iris Iris.BI

/-- `types.NewURLs(urls)` accepts the list (see the header). -/
opaque urlsValid (urls : List GoString) : Prop

/-- `ID(x).String()`. -/
def idStr (x : w64) : GoString := (Nat.toDigits 16 (uint.nat x)).map (fun c => W8 c.toNat)

end Types
end EtcdGrove
end Perennial
