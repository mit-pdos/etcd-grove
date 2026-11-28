# Witness: `UserChangePassword`'s password choice, exactly (nomode D3 follow-up (a), 2026-11-28)

One Go test file, `zz_pw_test.go.txt`, for `notes/nomode-n1.md`, "D3 follow-up (a)": the exact error
conditions the model of `authStore.selectPassword` (`auth.selectPwOk`) rests on, and the real store's
outcomes against the model.

- `TestBcryptExactError`: `bcrypt.GenerateFromPassword` (x/crypto v0.57.0, the version the fork's
  `server/go.mod` requires) over password lengths 0, 1, 71, 72, 73, 80, 200 and costs `-2^62`, -1, 0, 3, 4,
  5, 32, 33, 1000, `2^40` (and 31 for the over-long passwords: a 72-byte password at cost 31 would run
  `2^31` rounds; its "no error" is read off `checkCost`, bcrypt.go:299-304): an error iff the length is over
  72 or the cost over `MaxCost`; with an error the hash is nil; the error is `ErrPasswordTooLong` for an
  over-long password (checked first), else `InvalidCostError(cost)`.
- `TestStdDecodeExact`: `base64.StdEncoding.DecodeString`'s error is nil iff `stdDecOk` (Lean's
  `encoding.base64.stdDecOk`, reimplemented: the text without `'\n'`/`'\r'` is padded base64 over the
  standard alphabet, `b64Ok`), on every text of length at most 7 over `A Q / = \n \r !` (960,800) and 400k random
  texts (half of them real encodings with newlines inserted).
- `TestChangePasswordModel`: the real `authStore` over a bbolt backend (`NewAuthStore` at cost
  `bcrypt.MinCost` and at the invalid 32, which it replaces by `DefaultCost`): for a user with a password
  and one without (`NoPassword`), 15 password pairs (empty/empty, 72- and 73-byte plaintexts, valid and
  invalid hashes, hashes with newlines, bad padding, trailing data): `UserChangePassword` succeeds (and
  bumps the revision) iff `NoPassword || selectPwOk(pw, hpw)`, else returns `ErrNoPasswordUser`; a missing
  user gives `ErrUserNotFound`.
- `TestUserAddModel`: `UserAdd` of the same pairs, with and without `NoPassword`: success iff
  `NoPassword || selectPwOk(pw, hpw)`.

Run: copy to `server/zzpw/zz_pw_test.go` in a checkout of the fork pin (upamanyus/etcd `18ab647b02`),
then in `server/`: `GOTOOLCHAIN=go1.27.3 GOPROXY=off go test ./zzpw -v -count=1`.

Results (2026-11-28, go1.27.3): all four pass (`TestStdDecodeExact`: "1360800 texts agree").
