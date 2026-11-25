# `MustSaveMemberToBackend.spec`: one `memberEnc mm` for two encodings (2026-11-24, prove-ps2-jsonj6)

**Axiom:** `schema.membershipBackend.MustSaveMemberToBackend.wp_proof`. Its post puts `apply.memberEnc mm` under
`members/<id>` for any member record with `membership.memberAt m 1 mm`.

**Finding: false of Go at `mm.peerURLs = []`.** `memberAt` hides whether `RaftAttributes.PeerURLs` is nil. Go's
`json.Marshal(m)` writes `"peerURLs":null` for a nil slice and `"peerURLs":[]` for an empty non-nil one. Both kinds
reach the call: `applyConfChange` decodes its context with `json.Unmarshal` into a fresh `ConfigChangeContext`, and
`{"id":5}` leaves the slice nil while `{"id":5,"peerURLs":[]}` makes it empty non-nil. Both decode to
`ccMemberOf … .peerURLs = []` and both pass `ccApplyOk`. One `mm`, two byte strings: the axiom names one of them.

**Exploitability:** none known. `memberEnc` is opaque and is used only through `memberEnc_id_learner` (ids and
learner flags, which both encodings agree on), so no contradiction follows. It does block a proof: no definition of
`memberEnc` makes the axiom a theorem.

**Fix:** pending, see the ledger (2026-11-24, "`MustSaveMemberToBackend.spec`'s post does not see the peer-URL
slice's nil-ness") for the two candidates.
