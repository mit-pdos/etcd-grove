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

package v3rpc

import (
	"context"
	"errors"
	"testing"
	"time"
)

// TestCancellableContextErrBeforeDone checks that Err returns nil while Done is
// not yet closed, as context.Context requires, when Err is called while Cancel
// is cancelling the context.
func TestCancellableContextErrBeforeDone(t *testing.T) {
	c := newCancellableContext(context.Background())
	reason := errors.New("test reason")
	cancel := c.cancel
	c.cancel = func() {
		errc := make(chan error, 1)
		go func() { errc <- c.Err() }()
		select {
		case err := <-errc:
			if err != nil {
				t.Errorf("Err() = %v before Done is closed", err)
			}
		case <-time.After(100 * time.Millisecond):
		}
		cancel()
	}
	c.Cancel(reason)

	<-c.Done()
	if err := c.Err(); !errors.Is(err, reason) {
		t.Errorf("Err() = %v after Cancel, want %v", err, reason)
	}
}
