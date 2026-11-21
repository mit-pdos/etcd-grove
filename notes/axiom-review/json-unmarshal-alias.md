# `encoding.json.Unmarshal`: "fresh" URL slices that alias the caller's (prove-reflectfmt, 2026-11-20)

Found by reading the pinned code (go1.27.3 `encoding/json/decode.go`), while triaging the
`encoding/json` trust boundary; confirmed by a Go test, `examples/axiomcx/jsonunmarshalalias`.

## The axiom, as it stood

`Spec/encoding/json/Unmarshal.lean`: `json.Unmarshal(data, p)` into a `*membership.ConfigChangeContext`
with `p ↦ v`, for **any** `v`, returns `nil` and gives `p ↦ v'` with
`v'.Member'.RaftAttributes'.PeerURLs' ↦* pus` and `v'.Member'.Attributes'.ClientURLs' ↦* ...`, both
owned in full ("its URL slices fresh").

## Why it is false

`encoding/json` decodes a JSON array into the struct field's existing slice: `array` grows and
re-lengths the field's own `reflect.Value` (`decode.go:553-556`, `v.Grow(1)` only when `i >= v.Cap()`,
then `v.SetLen(i + 1)`), so while the old slice's capacity lasts the decoded elements are written into
its backing array and the field keeps pointing there. If `v.PeerURLs` is a non-nil slice the caller
still owns (`v.PeerURLs ↦* xs` beside `p ↦ v`), the post adds a second full points-to of the same
cells: the two give `False`, and every program after the call is provable, including one that panics.
The test sets `cc.PeerURLs` to a one-element slice, decodes one URL into it, and shows the decoded
slice's element is the caller's (and its value overwritten).

## Reachability

Latent: both callers (`EtcdServer.applyConfChange`, `server.go:2063-2064`;
`RaftCluster.ValidateConfigurationChange`, `cluster.go:319-320`) decode into
`new(membership.ConfigChangeContext)`, whose slices are `nil`.

## Fix

The precondition requires both URL slices of `v` to be `nil`
(`v.Member'.RaftAttributes'.PeerURLs' = slice.nil ∧ v.Member'.Attributes'.ClientURLs' = slice.nil`);
the callers discharge it by `rfl` on the zero value. With nil slices `array` allocates (`v.Grow`), so
the post's full ownership is right. Ledger: `notes/specs-only/ledger.md`, 2026-11-20.
