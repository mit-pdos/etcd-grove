// Check the byte limit used by semverSimple against the pinned parser.
package semverlen_test

import (
	"errors"
	"strings"
	"testing"

	"github.com/Masterminds/semver/v3"
)

func TestMaxVersionLen(t *testing.T) {
	v := "1.2.3-" + strings.Repeat("a", 250)
	if _, err := semver.NewVersion(v); err != nil {
		t.Fatalf("256 bytes: %v", err)
	}
	if _, err := semver.NewVersion(v + "a"); !errors.Is(err, semver.ErrVersionTooLong) {
		t.Fatalf("257 bytes: got %v, want ErrVersionTooLong", err)
	}
}
