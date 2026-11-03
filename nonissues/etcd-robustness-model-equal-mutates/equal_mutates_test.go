// Test of nonissues/etcd-robustness-model-equal-mutates.md: copy into tests/robustness/model/ and
// run `go test ./robustness/model -run '^TestNonDeterministicEqualMutatesArguments$'` from tests/.
package model

import "testing"

// Equal sorts both of its arguments in place, against porcupine's contract that a model does
// not modify the states it is given.
func TestNonDeterministicEqualMutatesArguments(t *testing.T) {
	a := nonDeterministicState{{Revision: 2}, {Revision: 1}}
	b := nonDeterministicState{{Revision: 2}, {Revision: 1}}
	if !a.Equal(b) {
		t.Fatalf("expected equal states")
	}
	if a[0].Revision != 2 || b[0].Revision != 2 {
		t.Errorf("Equal reordered its arguments: a = %v, b = %v", a, b)
	}
}
