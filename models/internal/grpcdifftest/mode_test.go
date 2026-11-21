//go:build !grpcmodel

package grpcdifftest_test

// model: whether the tests run against the model (run.sh: models/grpc/gomodel.py, tag
// grpcmodel) or against the real grpc-go v1.84.0 (go.mod).
const model = false
