package rpcdifftest_test

import (
	"go/token"
	"testing"
)

// TestIsExportedASCII checks the trusted model of go/token.IsExported
// (Net/TrustedCode/go/token.lean): on the empty name false, on a name whose first byte is ASCII
// exactly `'A' <= b && b <= 'Z'` (the rest of the name does not matter); a non-ASCII first byte
// is the model's choice point, so nothing is checked there.
func TestIsExportedASCII(t *testing.T) {
	if token.IsExported("") {
		t.Errorf("IsExported(\"\") = true")
	}
	for b := 0; b < 0x80; b++ {
		want := 'A' <= b && b <= 'Z'
		for _, rest := range []string{"", "x", "X", "_", "1", "é", "\xff"} {
			name := string([]byte{byte(b)}) + rest
			if got := token.IsExported(name); got != want {
				t.Errorf("IsExported(%q) = %v, the model says %v", name, got, want)
			}
		}
	}
}
