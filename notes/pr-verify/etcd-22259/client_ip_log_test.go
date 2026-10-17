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

package embed

import (
	"context"
	"fmt"
	"net"
	"net/url"
	"testing"
	"time"

	"go.uber.org/zap"
	"go.uber.org/zap/zapcore"
	"go.uber.org/zap/zaptest/observer"
	"google.golang.org/grpc/metadata"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/etcdserver/api/v3client"
)

func freeTCPURL(t *testing.T) url.URL {
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer l.Close()
	return url.URL{Scheme: "http", Host: l.Addr().String()}
}

func remotes(logs *observer.ObservedLogs, msg string) []string {
	var out []string
	for _, e := range logs.FilterMessage(msg).All() {
		r, ok := e.ContextMap()["remote"]
		if !ok {
			out = append(out, "<no remote field>")
			continue
		}
		out = append(out, fmt.Sprint(r))
	}
	return out
}

// TestClientIPInAuthLogs runs a single-member server over TCP with a debug-level observed
// logger and reports the "remote" field of the auth log lines PR #22259 extends.
func TestClientIPInAuthLogs(t *testing.T) {
	core, logs := observer.New(zapcore.DebugLevel)
	lg := zap.New(core)

	cu, pu := freeTCPURL(t), freeTCPURL(t)
	cfg := NewConfig()
	cfg.Dir = t.TempDir()
	cfg.ListenClientUrls, cfg.AdvertiseClientUrls = []url.URL{cu}, []url.URL{cu}
	cfg.ListenPeerUrls, cfg.AdvertisePeerUrls = []url.URL{pu}, []url.URL{pu}
	cfg.InitialCluster = "default=" + pu.String()
	cfg.ZapLoggerBuilder = NewZapLoggerBuilder(lg)
	cfg.Logger = "zap"
	e, err := StartEtcd(cfg)
	if err != nil {
		t.Fatal(err)
	}
	defer e.Close()
	<-e.Server.ReadyNotify()

	// set up auth in-process (no gRPC peer)
	ic := v3client.New(e.Server)
	defer ic.Close()
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()
	for _, f := range []func() error{
		func() error { _, err := ic.RoleAdd(ctx, "root"); return err },
		func() error { _, err := ic.UserAdd(ctx, "root", "root"); return err },
		func() error { _, err := ic.UserGrantRole(ctx, "root", "root"); return err },
		func() error { _, err := ic.AuthEnable(ctx); return err },
	} {
		if err := f(); err != nil {
			t.Fatal(err)
		}
	}

	// 1. Authenticate over gRPC: success, then a wrong password.
	c, err := clientv3.New(clientv3.Config{Endpoints: []string{cu.Host}, Username: "root", Password: "root", Logger: zap.NewNop()})
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()
	if _, err := c.Get(ctx, "k"); err != nil {
		t.Fatal(err)
	}
	if _, err := c.Auth.Authenticate(ctx, "root", "wrong"); err == nil {
		t.Fatal("expected an authentication failure")
	}

	// 2. A unary call and a watch with an invalid token.
	nc, err := clientv3.New(clientv3.Config{Endpoints: []string{cu.Host}, Logger: zap.NewNop()})
	if err != nil {
		t.Fatal(err)
	}
	defer nc.Close()
	bad := metadata.AppendToOutgoingContext(ctx, "token", "bogus-token")
	if _, err := nc.Get(bad, "k"); err == nil {
		t.Fatal("expected an invalid-token error")
	}
	wctx, wcancel := context.WithTimeout(bad, 3*time.Second)
	for wr := range nc.Watch(wctx, "k") {
		if wr.Err() != nil || wr.Canceled {
			break
		}
	}
	wcancel()
	time.Sleep(200 * time.Millisecond)

	for _, msg := range []string{
		"authenticated a user",              // authStore.Authenticate (apply path)
		"invalid authentication was requested", // EtcdServer.Authenticate
		"invalid auth token",                // authStore.AuthInfoFromCtx (unary and watch)
		"request stats",                     // logUnaryRequestStats
	} {
		count := map[string]int{}
		for _, r := range remotes(logs, msg) {
			count[r]++
		}
		t.Logf("%-40q remote values (count): %v", msg, count)
	}
	for _, r := range remotes(logs, "authenticated a user") {
		if r == "" {
			t.Errorf(`"authenticated a user" logged with an empty "remote": the apply path's context does not carry the request's client IP`)
		}
	}
	for _, r := range remotes(logs, "invalid auth token") {
		if r == "" {
			t.Errorf(`"invalid auth token" logged with an empty "remote" (a stream RPC: only the unary interceptor stores the client IP)`)
		}
	}
}
