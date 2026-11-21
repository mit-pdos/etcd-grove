# `encoding.json.MarshalMember`, `MarshalConfigChangeContext` (auth-mediation M2, 2026-11-20)

**Axioms**: `encoding.json.MarshalMember.wp_proof`, `encoding.json.MarshalConfigChangeContext.wp_proof`
(`Spec/encoding/json/{MarshalMember,MarshalConfigChangeContext}.lean`, the axioms under
`Proof/encoding/json/`), in the user's smallest form (2026-11-20): `json.Marshal` of a
`membership.Member` / `ConfigChangeContext` passed by value returns `nil` and some fresh bytes
(`sl ↦* b`, `b` existential), the value's two string slices borrowed at any fraction and given back.
etcd `d3feef9bcd` (the fork's pin), go1.27.3.

**Verdict: survives** (two rounds on the earlier drafts with a content claim: the first refuted the
draft without `PeerURLs`' nil-ness, nil and empty encoding as `null` and `[]`; the smallest form drops
the content claim; this round by an independent read-only reviewer).

Attacks (Go tests now in `examples/authmedjson/`, each panics or fails on a false claim; all pass,
the aliasing ones under `-race` too):

- never an error: invalid UTF-8 (lone `\xff`, truncated sequences, encoded surrogates), NUL and control
  bytes, HTML-escaped and line-separator characters, quotes and backslashes in every string; IDs 0, 1,
  2^63, MaxUint64; nil, empty and filled slices; both flags (`TestNoError`); 200k random values
  (`TestFunctionOfFields`); 2^20 peer URLs, a 32 MiB invalid name, 1.8 GB of output (`TestNoErrorLarge`,
  `TestHuge`). Blocked: none of the types has a `MarshalJSON`/`MarshalText` method, a `,string` tag, a
  map, a pointer, an interface or a colliding field name; the v1 options replace invalid UTF-8 by U+FFFD.
- another encoder: `GOEXPERIMENT=nojsonv2` does not build etcd's server at go1.27.3 (prometheus imports
  `encoding/json/jsontext`); v1's encoder would also be error-free and fresh.
- aliasing: 2000 results compared by address range, spare capacity included: none overlaps another or an
  input string; overwriting one result, appending past it and filling another's spare capacity leave the
  inputs and the others unchanged (`TestFresh`; `v2/arshal.go`'s `bytes.Clone`). `sl ↦* b` carries no
  capacity ownership in any case.
- retention and writes: writes to the slices after a call are seen by the next call and nothing else
  (`TestNoRetain`); 16 goroutines marshalling one member, sharing its slices read-only, race-free
  (`TestConcurrentReaders`).
- the triple's shape: Goose's three call sites (`server.go:1423`, `:1558`, `:1688`) load the value at
  `Member.ty`/`ConfigChangeContext.ty`, convert it to `go.any` and call `encoding.json.Marshal`: the
  spec's `interface.mkOk T.ty #v`; the nil error is the nil interface; `isPkgInit` is persistent.

Not tried: allocation failure (a fatal runtime error, outside the model), other toolchains (the claim is
for go1.27.3).
