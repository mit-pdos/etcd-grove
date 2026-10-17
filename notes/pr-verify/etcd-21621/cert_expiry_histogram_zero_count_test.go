package v3rpc

import (
	"net/http/httptest"
	"io"
	"strings"
	"testing"

	"github.com/prometheus/client_golang/prometheus/promhttp"
)

// Before any observation, the registered histogram already exports _count 0, so
// TestV3MetricsClientCertHistogramModified's substring check passes vacuously.
func TestProbeHistogramCountExportedWithoutObservation(t *testing.T) {
	srv := httptest.NewServer(promhttp.Handler())
	defer srv.Close()
	resp, err := srv.Client().Get(srv.URL)
	if err != nil { t.Fatal(err) }
	b, _ := io.ReadAll(resp.Body)
	for _, l := range strings.Split(string(b), "\n") {
		if strings.Contains(l, "client_cert_expiration_seconds_count") || strings.Contains(l, `client_cert_expiration_seconds_bucket{le="0"}`) {
			t.Log(l)
		}
	}
}
