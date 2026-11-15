# Requirements on `strings` (Perennial's; names-only)

## from 4d

`strings.ToLower(s)` returns some string without panicking (`internal/common/verify.go:20,25`,
`getEnvVerify`, `IsVerificationEnabled`). The old trust-boundary spec
(`specs-ref/Spec/strings/ToLower.lean`; `notes/perennial-changes.md`, "`strings.ToLower` has no
spec") is enough. Used by: `Verify.spec`.
