// The concurrent-map model's difftest (run.sh): this go.mod builds the tests against the real
// github.com/orcaman/concurrent-map v1.0.0, which is not in the lab's offline module cache; run.sh
// reads it from a module cache of its own (cache/cmap-difftest-modcache). go.model.mod builds the
// same tests against the model.
module dsverify.lab/cmapdifftest

go 1.22

require github.com/orcaman/concurrent-map v1.0.0
