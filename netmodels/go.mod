// netmodels.lab: the Go code of the network library models that verified programs share (the
// protobuf and JSON codecs' helpers first), under a module path that names no project using it.
// protobuf-go is a test dependency only: the differential tests of pbcodec and of the generated
// codecs.
module netmodels.lab

go 1.27

// (the toolchain the translation is made with; the go line stays 1.27 so that a module on go 1.27
// can import this one: a dependency's go line above the main module's makes Go rewrite its graph)
toolchain go1.27.3

require google.golang.org/protobuf v1.36.12
