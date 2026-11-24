//go:build !protomodel

package pbmodeltest

import "testing"

const modelBuild = false

// TestNotModelled, real build: what the model does not model works in protobuf-go, or panics (the
// model blocks there instead: mode_model_test.go).
func TestNotModelled(t *testing.T) {
	for name, c := range notModelledCases() {
		if o := outcome(c.f); o != c.real {
			t.Errorf("%s: protobuf-go: %s (want %s)", name, o, c.real)
		}
	}
}
