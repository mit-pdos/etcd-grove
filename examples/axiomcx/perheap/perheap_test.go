// Package perheaptest checks the Go facts behind the perheap redesign's incoming-metadata leaf
// (`metadata.transportMDRaw`, notes/perheap-scope.md §2, §8): the `MD` grpc's server transport puts in a
// stream's context is never written after `NewIncomingContext`, so a handler's
// `metadata.FromIncomingContext` reads the same contents every time.
package perheaptest

import (
	"context"
	"errors"
	"go/ast"
	"go/parser"
	"go/token"
	"io"
	"io/fs"
	"net"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/credentials/insecure"
	"google.golang.org/grpc/metadata"
	"google.golang.org/grpc/status"
	"google.golang.org/grpc/test/bufconn"
	"google.golang.org/protobuf/types/known/emptypb"
)

// The only code grpc hands the transport's map to after NewIncomingContext is a server's
// InTapHandle (grpc v1.84.0 internal/transport/http2_server.go:575). etcd installs none: no
// non-test file of etcd's server (at the fork's pin, ETCD_SRC) names grpc.InTapHandle.
func TestEtcdInstallsNoTapHandle(t *testing.T) {
	src := os.Getenv("ETCD_SRC")
	if src == "" {
		src = "/shared/etcd-grove/.lake/go-src/etcd"
	}
	root := filepath.Join(src, "server")
	if _, err := os.Stat(root); err != nil {
		t.Skipf("no etcd source at %s (set ETCD_SRC)", src)
	}
	files := 0
	err := filepath.WalkDir(root, func(p string, d fs.DirEntry, err error) error {
		if err != nil || d.IsDir() || !strings.HasSuffix(p, ".go") || strings.HasSuffix(p, "_test.go") {
			return err
		}
		f, err := parser.ParseFile(token.NewFileSet(), p, nil, parser.SkipObjectResolution)
		if err != nil {
			return err
		}
		files++
		ast.Inspect(f, func(n ast.Node) bool {
			if sel, ok := n.(*ast.SelectorExpr); ok && sel.Sel.Name == "InTapHandle" {
				t.Errorf("%s names InTapHandle", p)
			}
			return true
		})
		return nil
	})
	if err != nil {
		t.Fatal(err)
	}
	if files < 100 {
		t.Fatalf("only %d files under %s", files, root)
	}
	t.Logf("%d non-test files of etcd's server, none names InTapHandle", files)
}

// A handler's FromIncomingContext returns a copy: writing it changes nothing a later read sees;
// the transport's MD has lower-case keys, each with at least one value.
func TestIncomingCopyIndependent(t *testing.T) {
	lis := bufconn.Listen(1 << 20)
	check := func(_ any, stream grpc.ServerStream) error {
		ctx := stream.Context()
		md1, ok := metadata.FromIncomingContext(ctx)
		if !ok {
			return status.Error(codes.Internal, "no incoming metadata")
		}
		for k, vs := range md1 {
			if k != strings.ToLower(k) || len(vs) == 0 {
				return status.Errorf(codes.Internal, "key %q values %v", k, vs)
			}
		}
		if got := md1["token"]; len(got) != 1 || got[0] != "tok-1" {
			return status.Errorf(codes.Internal, "token %v", got)
		}
		md1["token"][0] = "overwritten"
		md1["added"] = []string{"x"}
		delete(md1, "user-agent")
		md2, _ := metadata.FromIncomingContext(ctx)
		if got := md2["token"]; len(got) != 1 || got[0] != "tok-1" {
			return status.Errorf(codes.Internal, "second read token %v", got)
		}
		if _, ok := md2["added"]; ok {
			return status.Error(codes.Internal, "second read sees the first copy's key")
		}
		if _, ok := md2["user-agent"]; !ok {
			return status.Error(codes.Internal, "second read lost a key the first copy deleted")
		}
		return nil
	}
	srv := grpc.NewServer(grpc.UnknownServiceHandler(check))
	go srv.Serve(lis)
	defer srv.Stop()
	conn, err := grpc.NewClient("passthrough:///bufnet",
		grpc.WithContextDialer(func(ctx context.Context, _ string) (net.Conn, error) { return lis.DialContext(ctx) }),
		grpc.WithTransportCredentials(insecure.NewCredentials()))
	if err != nil {
		t.Fatal(err)
	}
	defer conn.Close()
	ctx := metadata.AppendToOutgoingContext(context.Background(), "Token", "tok-1")
	st, err := conn.NewStream(ctx, &grpc.StreamDesc{ServerStreams: true, ClientStreams: true}, "/perheap.T/Check")
	if err != nil {
		t.Fatal(err)
	}
	if err := st.CloseSend(); err != nil {
		t.Fatal(err)
	}
	if err := st.RecvMsg(new(emptypb.Empty)); !errors.Is(err, io.EOF) {
		t.Fatalf("handler: %v", err)
	}
}
