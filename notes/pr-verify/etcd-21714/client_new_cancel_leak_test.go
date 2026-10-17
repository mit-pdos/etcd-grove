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
	"reflect"
	"testing"

	"github.com/stretchr/testify/require"

	"go.etcd.io/etcd/client/pkg/v3/logutil"
)

// children returns how many child contexts are registered with the *context.cancelCtx `ctx`
// (the unexported field `children` of Go's cancelCtx, read by reflection).
func children(t *testing.T, ctx context.Context) int {
	v := reflect.ValueOf(ctx).Elem().FieldByName("children")
	require.True(t, v.IsValid(), "not a *context.cancelCtx")
	return v.Len()
}

// newClient makes its context (`context.WithCancel(cfg.Context)`) before the message size check;
// when the check fails it returns without calling the context's cancel function, so the parent
// context keeps the child registered until the parent itself is canceled.
func TestNewSizeErrorCancelsContext(t *testing.T) {
	parent, cancel := context.WithCancel(context.Background())
	defer cancel()
	for i := 0; i < 100; i++ {
		_, err := New(Config{
			Context:            parent,
			Endpoints:          []string{"127.0.0.1:2379"},
			MaxCallSendMsgSize: 10,
			MaxCallRecvMsgSize: 5,
		})
		require.ErrorContains(t, err, "must be greater than send limit")
	}
	require.Equal(t, 0, children(t, parent), "failed New calls left child contexts registered with the parent")
}

// The same with an invalid logger configuration (cfg.LogConfig.Build() fails).
func TestNewLoggerErrorCancelsContext(t *testing.T) {
	parent, cancel := context.WithCancel(context.Background())
	defer cancel()
	lc := logutil.DefaultZapLoggerConfig
	lc.OutputPaths = []string{"/nonexistent-dir-pr21714/out.log"}
	for i := 0; i < 100; i++ {
		_, err := New(Config{Context: parent, Endpoints: []string{"127.0.0.1:2379"}, LogConfig: &lc})
		require.Error(t, err)
	}
	require.Equal(t, 0, children(t, parent), "failed New calls left child contexts registered with the parent")
}
