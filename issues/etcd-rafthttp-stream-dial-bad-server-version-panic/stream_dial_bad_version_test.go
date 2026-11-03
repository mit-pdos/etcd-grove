// Reproduction of issues/etcd-rafthttp-stream-dial-bad-server-version-panic.md: copy into
// server/etcdserver/api/rafthttp/ and run
// `go test ./etcdserver/api/rafthttp -run '^TestStreamReaderDialBadServerVersion$'` from server/.
// It uses the package's test helpers respRoundTripper (pipeline_test.go) and mustNewURLPicker
// (urlpick_test.go), as TestStreamReaderDialHttpError does.
package rafthttp

import (
	"net/http"
	"testing"

	"go.etcd.io/etcd/client/pkg/v3/types"
)

// TestStreamReaderDialBadServerVersion: a peer's response whose X-Server-Version does not parse
// is a failed dial, not a panic of the dialing member (dial runs on the stream reader's goroutine,
// where nothing recovers a panic).
func TestStreamReaderDialBadServerVersion(t *testing.T) {
	h := http.Header{}
	h.Add("X-Server-Version", "not-a-version")
	sr := &streamReader{
		peerID: types.ID(2),
		tr:     &Transport{streamRt: &respRoundTripper{code: http.StatusOK, header: h}, ClusterID: types.ID(1)},
		picker: mustNewURLPicker(t, []string{"http://localhost:2380"}),
		errorc: make(chan error, 1),
		ctx:    t.Context(),
	}
	defer func() {
		if r := recover(); r != nil {
			t.Fatalf("dial panicked: %v", r)
		}
	}()
	if _, err := sr.dial(streamTypeMessage); err == nil {
		t.Errorf("dial succeeded with a malformed X-Server-Version")
	}
}
