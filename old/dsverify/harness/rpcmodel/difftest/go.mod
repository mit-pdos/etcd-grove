module dsverify.lab/rpcdifftest

go 1.26

// the json tests' codec uses the harness's jsoncodec (the harness's own replaces repeated: a
// dependency's replaces do not apply)
require dsverify.lab/harness v0.0.0

replace dsverify.lab/harness => ../..

replace github.com/mit-pdos/perennial/goose/testdata/examples => /shared/perennial-4c8617a9e/goose/testdata/examples

replace github.com/tchajed/marshal => github.com/upamanyus/marshal v0.0.0-20260212025754-cf86d74f6773

replace github.com/anishathalye/porcupine => /shared/dsverify-lab/cache/src/porcupine
