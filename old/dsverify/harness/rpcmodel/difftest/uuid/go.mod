// The uuid model's difftest (run.sh): this go.mod builds the tests against the real
// github.com/google/uuid v1.3.1, which is not in the lab's offline module cache; run.sh reads it
// from a module cache of its own (cache/uuid-difftest-modcache, downloaded once from the public Go
// proxy, never a kit's or a run's). go.model.mod builds the same tests against the model.
module dsverify.lab/uuiddifftest

go 1.22

require github.com/google/uuid v1.3.1
