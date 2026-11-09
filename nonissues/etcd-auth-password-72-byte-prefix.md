---
upstream: none
checked: 2026-11-09
links: []
blocks-proof: no
---

# auth: a user whose password is 71 or 72 bytes long also authenticates with longer passwords that extend it

bcrypt's key is the password with a NUL byte appended, cut at 72 bytes (`expensiveBlowfishSetup`).
etcd hashes a new password with `bcrypt.GenerateFromPassword`, which refuses passwords over 72
bytes, so a stored password is at most 72 bytes; but `CheckPassword` compares with
`bcrypt.CompareHashAndPassword`, which does not refuse a long password. So for a user whose
password `pw` is exactly 72 bytes, any password that extends it passes, and for a 71-byte `pw`,
any password `pw + "\x00" + s` passes (NUL is valid UTF-8 in a proto3 string).

**Why not an issue:** no test; bcrypt's documented behavior ("the longest password bcrypt will
operate on"), not stated by etcd's documentation; found by code reading (the bcrypt boundary,
2026-11-09).

## Proof

no: the bcrypt boundary assumes only that a hash accepts its own password
(W0's `pwHash_match`), and checks a password with W0's opaque `pwMatch` (bcrypt's verdict,
`Spec/golang_org/x/crypto/bcrypt/CompareHashAndPassword.lean`), which claims nothing of a password
that is not the user's (hash collisions need that anyway).

## Notes

A fix, if wanted: refuse a password over 72 bytes in `CheckPassword` (as `GenerateFromPassword`
does).
