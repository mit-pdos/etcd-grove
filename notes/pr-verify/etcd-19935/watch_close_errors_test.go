// Copyright 2026 The etcd Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package clientv3

import (
	"context"
	"errors"
	"fmt"
	"testing"
)

// closedStream returns a watch stream that has already shut down and whose
// close() reports err (nil for none).
func closedStream(key string, err error) *watchGRPCStream {
	donec := make(chan struct{})
	close(donec)
	errc := make(chan error, 1)
	if err != nil {
		errc <- err
	}
	return &watchGRPCStream{ctx: context.Background(), ctxKey: key, cancel: func() {}, donec: donec, errc: errc}
}

func watcherWith(streams ...*watchGRPCStream) *watcher {
	w := &watcher{streams: make(map[string]*watchGRPCStream)}
	for _, s := range streams {
		w.streams[s.ctxKey] = s
	}
	return w
}

// TestWatcherCloseCanceledIsSuccess: a stream whose close reports
// context.Canceled closed successfully, so Close returns nil.
func TestWatcherCloseCanceledIsSuccess(t *testing.T) {
	w := watcherWith(closedStream("a", context.Canceled))
	if err := w.Close(); err != nil {
		t.Fatalf("Close() = %v, want nil", err)
	}
}

// TestWatcherCloseKeepsRealError: if one stream's close fails with a real
// error and another's reports context.Canceled, Close returns the real error,
// whatever order it closes the streams in (map order, so the test repeats).
func TestWatcherCloseKeepsRealError(t *testing.T) {
	errBoom := fmt.Errorf("boom")
	for i := 0; i < 200; i++ {
		w := watcherWith(closedStream("a", errBoom), closedStream("b", context.Canceled))
		err := w.Close()
		if !errors.Is(err, errBoom) {
			t.Fatalf("iteration %d: Close() = %v, want an error wrapping %v", i, err, errBoom)
		}
	}
}
