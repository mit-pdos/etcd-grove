# `membership.NewMember.wp_proof` (interim, etcd-dist D2)

**Retired by the proof** (2026-11-24): `computeMemberID` is translated with its body again (over Perennial's
`hash`), and `NewMember.wp_proof` is a theorem (`computeMemberID`, `newMember`); `TopLevelDefs`'s `memberId` is
the definition `membership.memberIdOf` (`MemberId.lean`). The review below is of the axiom as it was.

Reviewed 2026-11-24 (branch `etcd-safe-wf/2026-11-24`), by the axiom's author with the `axiom` skill, as a
short review: no counterexample project was built.

**Axiom**: `membership.NewMember.wp_proof` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/membership/NewMember.lean`,
triple in `Spec/.../membership/NewMember.lean`). It is interim: `computeMemberID` is translated names only until the
local `hash`/`internal/byteorder` translations are unified onto Perennial's. Under `GodebugFips140Off`, from
`sl ↦*{dq} [urlHttp p]` (exactly one URL, `url.URL{Scheme: "http", Host: p}`), `NewMember(name, sl, token, nil)`
does not panic, keeps `sl`, and returns `m` with `m ↦ mv` (owned) and `mv.ID' = memberId ("http://" ++ p) token`,
where `memberId` is `TopLevelDefs`'s opaque function.

**Go** (fork `upamanyus/etcd`, `server/v3/etcdserver/api/membership/member.go:51-88`; `client/pkg/v3/types/urls.go:79`):
`computeMemberID` runs `StringSlice` (`URL.String` of each URL), `sort.Strings`, `strings.Join(_, "")`, appends the token,
appends `now.Unix()` only if `now != nil`, then `sha1.Sum` and `BigEndian.Uint64(hash[:8])`. `newMember` allocates a
`&Member{...}` with a fresh `PeerURLs` slice (`StringSlice`'s `make`) and nil `ClientURLs`.

**Verdict: survives.** These attacks were tried:

- *Missing premise (panic).* `sha1.Sum` panics in `GODEBUG=fips140=only` mode (measured, go1.27.3: "use of SHA-1 is
  not allowed in FIPS 140-only mode"). The premise `GodebugFips140Off` excludes that mode. No other panic path exists:
  `now` is nil, so there is no `Sprintf` or `Unix`; the slice is read in bounds; `URL.String` never panics.
- *False pure fact.* The ID is a deterministic function of the URL's string and the token. The string is a function of
  `p` (measured: `""` gives `"http:"`, `"a b/%"` gives `"http://a%20b%2F%25"`, `"\xff"` gives `"http://%FF"`). Since
  `"http://" ++ p` determines `p`, the function `memberId u t := BE64(sha1(render(strip u) ++ t)[:8])` satisfies the
  axiom for every `p` and `token`. For plain hosts this is `memberIdSha1 ("http://" ++ p ++ t)`. So the axiom is
  consistent: nothing in it contradicts a real definition of `memberId`. Its docstring says "the SHA-1 of the URL's
  string", not "of `http://p`". No other axiom or spec constrains `memberId`, and `BootFacts` (a premise) only uses it.
- *Too much ownership.* `m ↦ mv` is the fresh `&Member` of `newMember`. No ownership of `mv`'s slices is claimed. `sl`
  is only read and is given back at the fraction it came with. The library keeps nothing: there is no package state.
- *Cross-world.* The post's pure fact is about `mv.ID'` and `memberId` of pure arguments. No opaque function of a
  pointer is involved.
- *Name.* `name` is only stored in `Attributes.Name`. The ID does not depend on it (tested: the same ID for `"x"` and
  `"y"`).

**Not tried**: a Lean counterexample (there was no gap to build one from); concurrency (`NewMember` touches no shared
state).

**Consequence for the statement**: callers (`deployment.memberIDs`, and through it `WellFormed`) inherit
`GodebugFips140Off` as a premise. Under rule 15 a new premise on a top-level theorem needs sign-off, unless the
statement already carries it.
