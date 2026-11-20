// The grpc and protobuf models' difftest (run.sh): this go.mod builds the tests against the real
// google.golang.org/grpc v1.84.0 and google.golang.org/protobuf v1.36.12 (in the lab's offline
// module cache); go.model.mod builds the same tests against the models (../grpc, ../protobuf),
// substituted as a kit's model-mode modfile substitutes them, with the tag rpcmodel.
module dsverify.lab/grpcdifftest

go 1.26.0

require (
	dsverify.lab/harness v0.0.0
	golang.org/x/net v0.59.0
	golang.org/x/sys v0.48.0
	golang.org/x/text v0.42.0
	google.golang.org/genproto/googleapis/rpc v0.0.0-20260928230214-8a89bd6388cc
	google.golang.org/grpc v1.84.0
	google.golang.org/protobuf v1.36.12
)

replace dsverify.lab/harness => ../..

replace github.com/mit-pdos/perennial/goose/testdata/examples => /shared/perennial-4c8617a9e/goose/testdata/examples

replace github.com/tchajed/marshal => github.com/upamanyus/marshal v0.0.0-20260212025754-cf86d74f6773

replace github.com/anishathalye/porcupine => /shared/dsverify-lab/cache/src/porcupine
