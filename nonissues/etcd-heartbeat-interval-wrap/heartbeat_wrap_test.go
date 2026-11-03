package embed

import (
	"testing"
)

// TestHeartbeatIntervalWrap: `Config.Validate` checks `5*cfg.TickMs > cfg.ElectionMs` in `uint`
// arithmetic, which wraps: a `--heartbeat-interval` of 3689348814741910324 ms passes with
// `--election-timeout=1000` (5 × 3689348814741910324 = 2^64 + 4), and the election timeout in ticks is
// then 0, which raft's `StartNode` rejects with a panic at startup.
func TestHeartbeatIntervalWrap(t *testing.T) {
	cfg := NewConfig()
	cfg.TickMs = 3689348814741910324
	cfg.ElectionMs = 1000
	if err := cfg.Validate(); err == nil {
		t.Fatalf("Validate accepted --heartbeat-interval=%d --election-timeout=%d (ElectionTicks %d)",
			cfg.TickMs, cfg.ElectionMs, cfg.ElectionTicks())
	}
}
