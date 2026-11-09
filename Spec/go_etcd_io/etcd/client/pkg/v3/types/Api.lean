/-
# `client/pkg/v3/types` (batch 1c): member ids and URL lists

* `urlsValid urls` (an opaque pure property of the strings): `NewURLs` accepts them (each parses as a
  URL with scheme `http`, `https`, `unix` or `unixs`, a `host:port` for `http(s)`, no path, query or
  fragment). Opaque because Go's `url.Parse` has no model here; its meaning is `NewURLs.spec`.
* `idStr x`: `ID(x).String()`, lowercase hexadecimal without leading zeros (`strconv.FormatUint(x,
  16)`).* `urlsHosts ss` (opaque pure function; integration I1, for 2e and 2f): `NewURLs(ss)` succeeds exactly
  when it is `some hs`, `hs` the hosts (`host:port`) of the parsed URLs in the result's (sorted)
  order; `urlsNorm ss` the parsed URLs' `String()` forms in that order (`url.Parse(s).String()`,
  sorted). Opaque because Go's `url.Parse` has no model here. `urlsValid ss` is `(urlsHosts
  ss).isSome`. Law `urlsHosts_len`: one host per URL, never for an empty list.
* `urlsStrs sl us`, `urlsAt sl hs` (persistent): the `types.URLs` slice `sl` holds, read-only for
  good, URLs whose `String()` forms are `us`, resp. whose hosts are `hs` (`NewURLs`' result).
  Intended realization: `sl ↦*□ uvs` with `uvs` the parsed `url.URL` values, each one's `String()`
  and `Host` as given (net/url's trusted model). They replace 2e's provisional `Config.urlsStrs` and
  2f's provisional `Rafthttp.urlsAt`/`urlsHosts` (`urlsMapStrs` and 2f's `urlsNoComma` stay theirs:
  a `URLsMap` is built by `NewURLsMap`, which has no spec here, and `NewURLs` accepts a comma).
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

/-- The hosts of the URLs `NewURLs(ss)` parses, in its result's order, or `none` if it fails. -/
opaque urlsHosts (ss : List GoString) : Option (List GoString)

/-- The `String()` forms of the URLs `NewURLs(ss)` parses, in its result's order. -/
opaque urlsNorm (ss : List GoString) : List GoString

/-- `types.NewURLs(urls)` accepts the list (see the header). -/
def urlsValid (urls : List GoString) : Prop := (urlsHosts urls).isSome

/-- One host per URL; an empty list is refused (`"no valid URLs given"`). -/
def urlsHosts_len.spec : Prop := ∀ ss hs, urlsHosts ss = some hs →
  hs.length = ss.length ∧ (urlsNorm ss).length = ss.length ∧ ss ≠ []

/-- `ID(x).String()`. -/
def idStr (x : w64) : GoString := (Nat.toDigits 16 (uint.nat x)).map (fun c => W8 c.toNat)

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- **The `types.URLs` slice `sl` holds, read-only for good, URLs whose `String()` forms are `us`**
(persistent). -/
opaque urlsStrs (sl : GoSlice) (us : List GoString) : IProp GF := iprop(True)

/-- **The `types.URLs` slice `sl` holds, read-only for good, URLs whose hosts are `hs`**
(persistent). -/
opaque urlsAt (sl : GoSlice) (hs : List GoString) : IProp GF := iprop(True)

def urls_persistent.spec : Prop :=
  (∀ sl us, Persistent (urlsStrs (GF := GF) sl us)) ∧ (∀ sl hs, Persistent (urlsAt (GF := GF) sl hs))

end res

end Types
end EtcdGrove
end Perennial
