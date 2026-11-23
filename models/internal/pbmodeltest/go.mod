// The protobuf model's differential test (models/protobuf-go; models/README.md, "The protobuf
// model"): this go.mod builds it against the real google.golang.org/protobuf v1.36.12; run.sh builds
// the same tests against the model (models/protobuf-go/gomodel.py: the module with the model's
// proto and protoadapt, tag protomodel). Both builds set tag pbmodel (the methods pbgen's pbmodel
// mode wrote into models.lab/internal/pbdifftest/{pb,xpb}; the real build does not call them).
module models.lab/internal/pbmodeltest

go 1.27

replace models.lab => ../..

require (
	google.golang.org/protobuf v1.36.12
	models.lab v0.0.0-00010101000000-000000000000
)
