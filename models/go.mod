// models.lab: our trusted models of real libraries (executable stand-ins: verified where they are
// code, trusted only in their claim to behave like the library; README.md), under a module path
// that names no project using it: the protobuf and JSON codecs' helpers, the codec generators
// (protobuf/, json/) and the schema dump pbgen derives its inputs from (pbdesc). protobuf-go is
// needed by pbdesc and by the differential tests only.
module models.lab

go 1.27

// (the toolchain the translation is made with; the go line stays 1.27 so that a module on go 1.27
// can import this one: a dependency's go line above the main module's makes Go rewrite its graph)
toolchain go1.27.3

require google.golang.org/protobuf v1.36.12
