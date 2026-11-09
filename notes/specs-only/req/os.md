# Requirements on `os` (project bboltfs's translation, the OsFs extension; trust boundary)

## from 4d

1. `os.Getenv(key)` returns some string, without panicking (`internal/common/verify.go:20`,
   `getEnvVerify`: `strings.ToLower(os.Getenv("BBOLT_VERIFY"))`). Any string: `Verify.spec` proves
   both of its branches. Used by: `Verify.spec`.
2. `os.Getpagesize()` returns the OS page size, at least 4096 and at most 65536 (Linux: 4 KiB on
   amd64, 4/16/64 KiB on arm64, ppc64, loong64). `internal/common/types.go:31`:
   `var DefaultPageSize = os.Getpagesize()`. Used by: `BboltCommon.init.spec` (bbolt's `Open`
   takes it as a new file's page size, db.go:268).
