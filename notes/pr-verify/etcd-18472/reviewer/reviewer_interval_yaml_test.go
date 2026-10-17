package embed

import (
	"os"
	"path/filepath"
	"testing"
)

// Reviewer probe (etcd#18472): the config file carries auto-compaction-interval, and a
// negative or unit-less value is (not) rejected where.
func TestReviewerIntervalYAML(t *testing.T) {
	for _, v := range []string{`"5m"`, `"-1s"`, `"1ns"`, `5`} {
		p := filepath.Join(t.TempDir(), "c.yml")
		if err := os.WriteFile(p, []byte("auto-compaction-mode: revision\nauto-compaction-retention: \"10\"\nauto-compaction-interval: "+v+"\n"), 0o600); err != nil {
			t.Fatal(err)
		}
		cfg, err := ConfigFromFile(p)
		if err != nil {
			t.Logf("yaml %s: ConfigFromFile error: %v", v, err)
			continue
		}
		verr := cfg.Validate()
		d, perr := parseCompactionInterval(cfg.AutoCompactionInterval)
		t.Logf("yaml %s: field=%q Validate=%v parse=%v,%v", v, cfg.AutoCompactionInterval, verr, d, perr)
	}
}
