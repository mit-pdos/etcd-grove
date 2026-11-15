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

package transport

import (
	"net"
	"net/http"
	"testing"
	"time"
)

// TestNewTimeoutTransportReadTimeout: a peer that accepts the connection and never answers must
// make a request over NewTimeoutTransport fail once the read timeout passes, as its doc says ("If
// read/write on the created connection blocks longer than its time limit, it will return timeout
// error"); rafthttp's stream round tripper relies on it (ConnReadTimeout).
func TestNewTimeoutTransportReadTimeout(t *testing.T) {
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer ln.Close()
	stop := make(chan struct{})
	defer close(stop)
	go func() {
		for {
			c, err := ln.Accept()
			if err != nil {
				return
			}
			go func() { <-stop; c.Close() }() // read nothing, answer nothing
		}
	}()

	tr, err := NewTimeoutTransport(TLSInfo{}, time.Second, 100*time.Millisecond, 100*time.Millisecond)
	if err != nil {
		t.Fatal(err)
	}
	req, err := http.NewRequest(http.MethodGet, "http://"+ln.Addr().String()+"/", nil)
	if err != nil {
		t.Fatal(err)
	}
	done := make(chan error, 1)
	go func() {
		_, err := tr.RoundTrip(req)
		done <- err
	}()
	select {
	case err := <-done:
		if err == nil {
			t.Fatal("expected a timeout error")
		}
		t.Logf("RoundTrip failed as expected: %v", err)
	case <-time.After(3 * time.Second):
		t.Fatal("RoundTrip still blocked 3s after the 100ms read timeout")
	}
}
