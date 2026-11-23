// The protobuf model's packages (models/protobuf-go: gomodel.py assembles the module from
// google.golang.org/protobuf v1.36.12 with these packages in place of its own). This go.mod only
// keeps them out of the models.lab module (they are protobuf-go's packages, which use its
// internal packages); nothing builds this directory as it is.
module google.golang.org/protobuf

go 1.23
