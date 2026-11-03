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

package leasehttp

import (
	"context"
	"net/http"
	"net/http/httptest"
	"testing"
)

// TestTimeToLiveHTTPEmptyOKReply: a follower forwarding a TimeToLive request
// to a peer URL that answers 200 with an empty body (no
// LeaseTimeToLiveResponse) should get an error, as for any other malformed
// reply, not a panic.
func TestTimeToLiveHTTPEmptyOKReply(t *testing.T) {
	ts := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		w.WriteHeader(http.StatusOK)
	}))
	defer ts.Close()

	var err error
	func() {
		defer func() {
			if r := recover(); r != nil {
				t.Fatalf("TimeToLiveHTTP panicked: %v", r)
			}
		}()
		_, err = TimeToLiveHTTP(context.Background(), 1, false, ts.URL+LeaseInternalPrefix, http.DefaultTransport)
	}()
	if err == nil {
		t.Fatal("TimeToLiveHTTP accepted a reply without a LeaseTimeToLiveResponse")
	}
}
