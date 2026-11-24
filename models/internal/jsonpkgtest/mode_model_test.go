//go:build netmodel

package jsonpkgtest

// modelBuild: the encoding/json model with the generated methods (internal/jsonstreamtest/run.sh,
// which runs TestDispatch* here only with the model's overlay; a netmodel build over the real
// encoding/json runs only the generated TestJSON*, etc/gates.sh).
const modelBuild = true
