# The auth messages' nested unknown fields (spec-side flaw, found 2026-11-13; open)

Found by etcd-grove-81's independent review of auth-schema-fix (journal
`/root/.claude-csail/projects/-shared-etcd-grove/c04a65b0-a272-4ae4-94c7-91aa4a20ea30/subagents/workflows/wf_c53ac11b-636/journal.jsonl`;
Go tests at the pin: `/shared/tmp/coord-81/authfix-review/r3/server/storage/schema/zz_review_{garbage,optsuf}_test.go`,
run `cd /shared/tmp/coord-81/authfix-review/r3/server && GOWORK=off GOTOOLCHAIN=go1.27.3 go test ./storage/schema/ -run TestReview -v`).
A bug in this repository's trusted text, not in Go.

- **MAJ-1.** The re-review's M1 fix (9317630050) fixed `unknownFields` to nil in `ownUser`/`ownRole`/
  `ownUserX`/`ownRoleX`, but not one level down: `userOptsAt` (the `Options` message) and
  `ownPermW`/`ownPermX` (the permissions) leave theirs free. `UnsafePutUser`/`UnsafePutRole` (the
  write contract, `auth/InvAuth.lean`) accept garbage there; protobuf-go's `Marshal` stores it and
  the next `GetUser`/`GetRole` panics. So `authSchemaSrv` (premise `hD22` of `authkv_startServer`
  etc.) is false of Go.
- **MAJ-2.** A client's valid unknown fields in `UserAddOptions` round-trip through `UserAdd`
  (`Options: r.Options`, store.go:442-462), so one `UserRec` (name, password, roles, noPassword) has
  two byte encodings; the opaque `userEncode : UserRec → bytes` cannot satisfy both `authBkLend`'s
  `authBucketsAt` and `UnmarshalUser.spec`.
- MINOR: `notes/auth-validspec-false.md` calls `server_new_auth_on` and the authkv results "strictly
  stronger"; R-M1 makes D22 harder to meet on reads (the read contract now promises nil unknown
  fields), so they are not strictly stronger in that respect.

Decided by etcd-grove-81 (2026-11-13): (1) permissions: `unknownFields' := slice.nil` for the stored
permissions (etcd builds them fresh, store.go:839-842); (2) Options: the raw unknown bytes become part
of the record (`UserRec` gains e.g. `optsUF : GoString` with a valid-wire-format premise), `userEncode`
takes them, `userOptsAt` ties `uf` to them, `userAddReqIs` carries them from the request, every later
put of the user carries the stored value; a Go control: valid unknown fields in Options round-trip and
the read does not panic. Status: not done; `notes/auth-schema-fix-handoff.md` has the plan.
