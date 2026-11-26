# rt: resume notes (2026-11-24, after the takeover)

## Done on `goose-model-overlay-rest-rt`
runtime (Gosched, buildVersion, Frames.Next models; callers trusted over the added translated
`callersModel`), os/syscall runtime_args/runtime_envs over gomodel.ChooseStrings, syscall init.0
real over the prlimit1 model, log Printf/Println/init.0 models; proofs built; model-tests extended.
ChooseString(s) alone: branch `goose-model-overlay-rest-gomodel-choosestring` (1ba3cdff2).

## D3 (crypto/rand.Int real) — NOT done, parked on `goose-model-overlay-rest-rt-rand`
That branch = rt + the D3 files (translation, models, no proofs): crypto/rand.Int and Reader
translated, crypto/internal/rand (reader.Read model), drbg DefaultReader, math/big nat subset
over the arith_decl_pure model. Missing:
1. drbg's initialize' calls `init.0` (fips140.CAST self-test; fatal with GODEBUG failfipscast)
   and `drbgPool.init` (opaque): need a [[skip]] for drbgPool and a model of init.0 (no-op or
   `if Choose() { exit }`) — a decision for the lead (GODEBUG environment assumption).
2. Specs+proofs: crypto/internal/rand reader.Read as io.readerOk; its initialize'
   (Reader ↦□ reader{}); crypto/rand isInitialized (Reader's value + readerOk) and initialize';
   math/big Int.Sign/SetUint64/Sub/BitLen/SetBytes/Cmp and nat make/norm/set/setWord/setUint64/
   add/sub/cmp/bitLen/setBytes, addVW/subVW/addVV_g/subVV_g (aliasing: n.Sub(max, n.SetUint64(1))
   has z == y); then crypto/rand.Int over io.ReadFull's spec. ownInt has no capacity: track the
   fresh n's cap internally. Estimate ~1-1.5k lines.
Snapshot of the D3 files: gmr-rt/d3-snapshot.tgz.
