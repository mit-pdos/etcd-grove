// Package early replaces crypto/rand.Reader by a failing reader at its initialization.
package early

import (
	"crypto/rand"
	"errors"
)

type failReader struct{}

func (failReader) Read([]byte) (int, error) { return 0, errors.New("no randomness") }

func init() { rand.Reader = failReader{} }
