---
upstream: none
checked: 2026-11-25
links: []
blocks-proof: no
---

# rabia: `GetLogLevel` panics on a level its documentation says selects debug

`internal/logger/logger.go:63-73` (the dsverify kit's rabia, `examples/dsverify/rabia`):
the comment says a `Conf.LogLevel` other than "debug", "info" and "warn" selects the debug level, but
the code panics on any string zerolog's `ParseLevel` rejects ("foo", "Warn"), and the empty string
(an unset `RC_LLevel`) becomes `NoLevel`, which turns all logging off.

**Why not an issue:** documentation only, and a precondition the verified deployment meets: the kit
sets the level to "warn" (`examples/rabianet/kit.go:216`). Found by code reading (the dsv-fix6 axiom
review of zerolog, `notes/axiom-review/dsv-fix6/zerolog.md`); no test.

## Proof

no: `InitLogger.wp_proof` (`Dsverify/Proof/rabia/internal/logger/InitLogger.lean`) runs under
`confRO`, whose `LogLevel` is `"warn"`, and uses `ParseLevel("warn")`'s spec only.
