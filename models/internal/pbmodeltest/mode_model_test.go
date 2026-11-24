//go:build protomodel

package pbmodeltest

import "testing"

const modelBuild = true

// TestNotModelled, model build: outside the model, the model blocks forever (stuck; never a panic,
// models/README.md, "Not modelled: stuck").
func TestNotModelled(t *testing.T) {
	for name, c := range notModelledCases() {
		if o := outcome(c.f); o != "stuck" {
			t.Errorf("%s: the model: %s", name, o)
		}
	}
}
