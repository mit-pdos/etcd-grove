// The dsverify lab's model of google.golang.org/protobuf (v1.36.12), for a kit's model build and
// for Goose (notes/grpc-model.md): proto.Marshal and proto.Unmarshal over a codec that kitgen
// generates per kit (kit.toml's [protobuf]), and the names that protoc-gen-go's generated code
// (*.pb.go) refers to, so that it compiles and translates unmodified. The real module is used
// outside the model build; a kit substitutes this directory by a replace in its model-mode
// modfile (go.model.mod) only.
module google.golang.org/protobuf

go 1.22
