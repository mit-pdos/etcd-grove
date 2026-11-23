// The differential tests of the third-party library models (models/gods, models/uuid,
// models/concurrent-map; models/README.md): this go.mod builds them against the real modules
// (gods v1.18.1, uuid v1.3.1, concurrent-map v1.0.0, the versions SwiftPaxos's go.mod pins);
// run.sh builds the same tests against the models (a -modfile with the three replaced, tag tpmodel).
module models.lab/internal/tpdifftest

go 1.27

require (
	github.com/emirpasic/gods v1.18.1
	github.com/google/uuid v1.3.1
	github.com/orcaman/concurrent-map v1.0.0
)
