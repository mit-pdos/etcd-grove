package embed

import (
	"reflect"
	"testing"
	"time"
)

// With the quota disabled (QuotaBackendBytes < 0: storage.NewBackendQuota
// returns a passthrough quota), NewServer still hands the auto-periodic
// compactor the 2 GiB default, so it compacts once Size() nears 1.4 GiB.
func TestReviewerAutoPeriodicQuotaDisabled(t *testing.T) {
	cfg := NewConfig()
	applyTestURLConfig(cfg, newConfigTestURLs())
	cfg.Dir = t.TempDir()
	cfg.QuotaBackendBytes = -1
	cfg.AutoCompactionMode = CompactorModeAutoPeriodic
	cfg.AutoCompactionRetention = "5"
	cfg.LogLevel = "error"
	e, err := StartEtcd(cfg)
	if err != nil {
		t.Fatal(err)
	}
	defer e.Close()
	select {
	case <-e.Server.ReadyNotify():
	case <-time.After(30 * time.Second):
		t.Fatal("not ready")
	}
	c := reflect.ValueOf(e.Server).Elem().FieldByName("compactor").Elem().Elem()
	t.Logf("QuotaBackendBytes=-1 (quota disabled): compactor type %v, maxBytes=%d, retention=%d",
		c.Type(), c.FieldByName("maxBytes").Int(), c.FieldByName("retention").Int())
}

// parseCompactionRetention accepts "5ns" in the periodic mode; v3compactor.New
// then panics (getRetentions divides by period/10 == 0).
func TestReviewerParseTinyPeriodic(t *testing.T) {
	d, err := parseCompactionRetention(CompactorModePeriodic, "5ns")
	t.Logf("periodic, \"5ns\": %v, err %v", d, err)
}
