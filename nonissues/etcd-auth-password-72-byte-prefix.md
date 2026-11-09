---
upstream: none
checked: 2026-11-09
links: []
blocks-proof: no
---

# auth: a user whose password is 72 bytes long also authenticates with any longer password starting with it

bcrypt reads at most the first 72 bytes of a password. etcd hashes a new password with
`bcrypt.GenerateFromPassword`, which refuses passwords over 72 bytes, so a stored password is at most
72 bytes; but `CheckPassword` compares with `bcrypt.CompareHashAndPassword`, which does not refuse a
long password: for a user whose password is exactly 72 bytes, any password that extends it passes.

**Why not an issue:** no test; bcrypt's documented behavior ("the longest password bcrypt will
operate on"), not stated by etcd's documentation; found by code reading (the bcrypt boundary,
2026-11-09).

## Proof

no: the bcrypt boundary assumes only that a hash accepts its own password
(`Spec/golang_org/x/crypto/bcrypt/CompareHashAndPassword.lean`), and `CheckPassword`'s spec claims
nothing of another password; the client's model must allow a successful `Authenticate` with a
password that is not the user's (requested of W0, `notes/specs-only/req/go_etcd_io_etcd_api_v3.md`,
"from 3d"), which hash collisions need anyway.

## Notes

A fix, if wanted: refuse a password over 72 bytes in `CheckPassword` (as `GenerateFromPassword`
does).
