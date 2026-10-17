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

// Probes for etcd#21330 (client/v3: validate key is non-empty before sending
// KV requests). Needs the PR's kv_test.go (recordingKVClient) beside it.

import (
	"context"
	"errors"
	"testing"

	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
)

// The error the client returns now is the same value the caller got before,
// when the server rejected the empty key with ErrGRPCEmptyKey and kv.Do passed
// it through ContextError.
func TestProbeEmptyKeySameErrorAsServer(t *testing.T) {
	before := ContextError(context.Background(), rpctypes.ErrGRPCEmptyKey)
	if before != rpctypes.ErrEmptyKey {
		t.Fatalf("server path error %#v != ErrEmptyKey %#v", before, rpctypes.ErrEmptyKey)
	}
	kv := &kv{remote: &recordingKVClient{}}
	for name, f := range map[string]func() error{
		"Get":    func() error { _, err := kv.Get(context.Background(), ""); return err },
		"Put":    func() error { _, err := kv.Put(context.Background(), "", "v"); return err },
		"Delete": func() error { _, err := kv.Delete(context.Background(), ""); return err },
		"GetStream": func() error {
			_, err := kv.GetStream(context.Background(), "")
			return err
		},
	} {
		if err := f(); err != before {
			t.Errorf("%s(\"\") = %v, want the server path's %v", name, err, before)
		}
	}
}

// An empty key with an invalid sort option: the client reports the empty key,
// as the server's checkRangeRequest does (key checked before sort).
func TestProbeEmptyKeyBeforeSortCheck(t *testing.T) {
	kv := &kv{remote: &recordingKVClient{}}
	_, err := kv.Get(context.Background(), "", WithSort(SortByKey, SortOrder(99)))
	if !errors.Is(err, rpctypes.ErrEmptyKey) {
		t.Fatalf("Get(\"\", invalid sort) = %v, want ErrEmptyKey", err)
	}
	_, err = kv.Get(context.Background(), "a", WithSort(SortByKey, SortOrder(99)))
	if !errors.Is(err, rpctypes.ErrInvalidSortOption) {
		t.Fatalf("Get(\"a\", invalid sort) = %v, want ErrInvalidSortOption", err)
	}
}

// WithRange with an empty start key is still rejected (the server rejects it
// too); WithPrefix/WithFromKey are not (they replace the key by "\x00").
func TestProbeEmptyKeyWithRange(t *testing.T) {
	r := &recordingKVClient{}
	kv := &kv{remote: r}
	if _, err := kv.Get(context.Background(), "", WithRange("z")); !errors.Is(err, rpctypes.ErrEmptyKey) {
		t.Fatalf("Get(\"\", WithRange) = %v, want ErrEmptyKey", err)
	}
	if _, err := kv.Delete(context.Background(), "", WithPrefix()); errors.Is(err, rpctypes.ErrEmptyKey) || !r.deleteRangeCalled {
		t.Fatalf("Delete(\"\", WithPrefix) = %v (remote called %v), want the RPC", err, r.deleteRangeCalled)
	}
}
