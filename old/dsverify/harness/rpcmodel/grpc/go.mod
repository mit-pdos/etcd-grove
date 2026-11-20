// The dsverify lab's model of google.golang.org/grpc (v1.84.0), the unary subset
// (notes/grpc-model.md): Go over the lab's net model, translated by Goose in place of the real
// module and proved once in the harness (harness/lean/Harness/Proof/grpc). The real module is used
// outside the model build; a kit substitutes this directory (and the protobuf model,
// ../protobuf) by replaces in its model-mode modfile (go.model.mod) only.
module google.golang.org/grpc

go 1.22

require google.golang.org/protobuf v1.36.12

// for translating this module on its own (goose, harness/lean/build.sh): a dependency's replaces
// do not apply to a kit, whose model-mode modfile replaces both modules
replace google.golang.org/protobuf => ../protobuf

require github.com/goose-lang/primitive v0.2.2-0.20260212023729-cb7f52217e65
