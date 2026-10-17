package v3rpc_test

import (
	"bytes"
	"context"
	"fmt"
	"net"
	"net/http"
	"net/url"
	"os"
	"path/filepath"
	"runtime"
	"strings"
	"sync"
	"testing"
	"time"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/embed"
)

func rvFreePort(t *testing.T) int {
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer l.Close()
	return l.Addr().(*net.TCPAddr).Port
}

func rvStart(t *testing.T, logPath, rotJSON string) (*embed.Etcd, string) {
	cfg := embed.NewConfig()
	cfg.Dir = filepath.Join(t.TempDir(), "data")
	cfg.LogLevel = "error"
	cu, _ := url.Parse(fmt.Sprintf("http://127.0.0.1:%d", rvFreePort(t)))
	pu, _ := url.Parse(fmt.Sprintf("http://127.0.0.1:%d", rvFreePort(t)))
	cfg.ListenClientUrls, cfg.AdvertiseClientUrls = []url.URL{*cu}, []url.URL{*cu}
	cfg.ListenPeerUrls, cfg.AdvertisePeerUrls = []url.URL{*pu}, []url.URL{*pu}
	cfg.InitialCluster = cfg.InitialClusterFromName(cfg.Name)
	cfg.ExperimentalLogRequestPath = logPath
	cfg.ExperimentalLogRequestRotationConfigJSON = rotJSON
	e, err := embed.StartEtcd(cfg)
	if err != nil {
		t.Fatal(err)
	}
	select {
	case <-e.Server.ReadyNotify():
	case <-time.After(10 * time.Second):
		t.Fatal("not ready")
	}
	return e, cu.String()
}

func rvPut(t *testing.T, ep, k string) {
	c, err := clientv3.New(clientv3.Config{Endpoints: []string{ep}, DialTimeout: 5 * time.Second})
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	if _, err := c.Put(ctx, k, "v"); err != nil {
		t.Fatal(err)
	}
}

func rvOpenFDsTo(path string) []string {
	var out []string
	ents, _ := os.ReadDir("/proc/self/fd")
	for _, e := range ents {
		l, err := os.Readlink(filepath.Join("/proc/self/fd", e.Name()))
		if err == nil && l == path {
			out = append(out, e.Name())
		}
	}
	return out
}

func rvGoroutines(substr string) int {
	buf := make([]byte, 1<<22)
	n := runtime.Stack(buf, true)
	return strings.Count(string(buf[:n]), substr)
}

// After the server is closed (Cleanup stops the BufferedWriteSyncer), the lumberjack
// logger is never closed: its file stays open and its mill goroutine keeps running, once
// per server started in the process (embedders, integration tests).
func TestReviewRequestLogFileLeakAfterClose(t *testing.T) {
	logPath := filepath.Join(t.TempDir(), "req.log")
	before := rvGoroutines(").millRun(")
	for i := 0; i < 2; i++ {
		e, ep := rvStart(t, logPath, "")
		rvPut(t, ep, fmt.Sprintf("k%d", i))
		e.Close()
	}
	time.Sleep(200 * time.Millisecond)
	data, _ := os.ReadFile(logPath)
	t.Logf("log file %d bytes, put entries: %d", len(data), strings.Count(string(data), "KV/Put"))
	fds := rvOpenFDsTo(logPath)
	mills := rvGoroutines(").millRun(") - before
	t.Logf("after 2 start/Close cycles: open fds to %s: %v; leaked millRun goroutines: %d", logPath, fds, mills)
	if len(fds) == 0 && mills == 0 {
		t.Fatalf("no leak; finding does not hold")
	}
}

// A rotation config with a negative maxsize is accepted, and every entry is then
// silently dropped (lumberjack rejects each write; BufferedWriteSyncer's flush loop
// discards the error).
func TestReviewRotationNegativeMaxSizeDropsAll(t *testing.T) {
	logPath := filepath.Join(t.TempDir(), "req.log")
	e, ep := rvStart(t, logPath, `{"maxsize": -1}`)
	for i := 0; i < 5; i++ {
		rvPut(t, ep, fmt.Sprintf("k%d", i))
	}
	e.Close()
	data, err := os.ReadFile(logPath)
	t.Logf("server started fine; after 5 Puts and Close: file err=%v, %d bytes", err, len(data))
	if len(data) > 0 {
		t.Fatalf("entries were written; finding does not hold")
	}
}

// An unknown or misspelled rotation key is silently ignored (json.Unmarshal into
// lumberjack.Logger), so {"max-size": 1} keeps the 100 MB default.
func TestReviewRotationUnknownKeyIgnored(t *testing.T) {
	logPath := filepath.Join(t.TempDir(), "req.log")
	e, _ := rvStart(t, logPath, `{"max-size": 1, "maxSizeMB": 1, "max_backups": 1}`)
	e.Close()
	t.Logf("server started with misspelled rotation keys, no error")
}

// Requests through the gRPC gateway (HTTP/JSON, enabled by default) are logged with the
// gateway's own gRPC connection as "remote", not the HTTP client's address.
func TestReviewGatewayRemoteIsServerItself(t *testing.T) {
	logPath := filepath.Join(t.TempDir(), "req.log")
	e, ep := rvStart(t, logPath, "")
	var mu sync.Mutex
	var clientLocal string
	tr := &http.Transport{DialContext: func(ctx context.Context, network, addr string) (net.Conn, error) {
		c, err := (&net.Dialer{}).DialContext(ctx, network, addr)
		if err == nil {
			mu.Lock()
			clientLocal = c.LocalAddr().String()
			mu.Unlock()
		}
		return c, err
	}}
	body := `{"key":"Z3drZXk=","value":"dg=="}` // "gwkey"
	resp, err := (&http.Client{Transport: tr}).Post(ep+"/v3/kv/put", "application/json", bytes.NewBufferString(body))
	if err != nil {
		t.Fatal(err)
	}
	resp.Body.Close()
	e.Close()
	data, _ := os.ReadFile(logPath)
	var line string
	for _, l := range strings.Split(string(data), "\n") {
		if strings.Contains(l, `"key":"gwkey"`) {
			line = l
		}
	}
	t.Logf("HTTP client address: %s", clientLocal)
	t.Logf("request log entry: %s", line)
	if line == "" {
		t.Fatalf("no entry")
	}
	if strings.Contains(line, `"remote":"`+clientLocal+`"`) {
		t.Fatalf("remote is the HTTP client; finding does not hold")
	}
}

// Concurrent unary requests while the server shuts down (Cleanup stops the syncer):
// run with -race; expected to find no race (requestLogger is written before serving,
// BufferedWriteSyncer and lumberjack lock internally).
func TestReviewRequestLogConcurrentCloseRace(t *testing.T) {
	logPath := filepath.Join(t.TempDir(), "req.log")
	e, ep := rvStart(t, logPath, "")
	c, err := clientv3.New(clientv3.Config{Endpoints: []string{ep}, DialTimeout: 5 * time.Second})
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()
	var wg sync.WaitGroup
	for g := 0; g < 8; g++ {
		wg.Add(1)
		go func(g int) {
			defer wg.Done()
			for i := 0; i < 200; i++ {
				ctx, cancel := context.WithTimeout(context.Background(), time.Second)
				c.Put(ctx, fmt.Sprintf("k%d-%d", g, i), "v")
				cancel()
			}
		}(g)
	}
	time.Sleep(300 * time.Millisecond)
	e.Close()
	wg.Wait()
}
