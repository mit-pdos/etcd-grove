package mvccrand

import (
	"path/filepath"
	"testing"
)

func TestRun(t *testing.T) {
	for seed := uint64(1); seed <= 100; seed++ {
		Run(Config{Path: filepath.Join(t.TempDir(), "mvccrand.db"), Seed: seed, Ops: 3000})
	}
}

func TestMain_(t *testing.T) {
	t.Chdir(t.TempDir())
	Main()
}
