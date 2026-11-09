// Package grpc holds the requirement snippets of the gRPC boundary (batch 2a,
// Spec/google_golang_org/grpc/Api.lean): what etcd's client and server rely on of grpc-go, each
// reliance an explicit panic.
//
// Common assumptions: cc is a connection made by grpc.NewClient whose resolver reports only
// addresses bound (Grpc.addrAt) to the contracts the snippet names; the program's messages fit
// (Grpc.msgsFit).
package grpc

import (
	"context"
	"errors"
	"io"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/metadata"
	"google.golang.org/grpc/status"
)

// REQ grpc/at-most-once: a unary call reaches at most one run of the method's handler, and a
// handler's status reaches the caller as it was sent (an etcd status is etcd's, never grpc's own).
// Users: the client's retry interceptor (1c's AttemptTriple: a write is applied at most once per
// attempt), W0's at-most-once for exclusive updates.
// Assumes: k owned; the member's contract for Put (etcdUnary).
// Specs: Grpc.ClientConn.Invoke.spec, attemptOk_call (S consumed by at most one run), ownErr_grpcMsg;
// rpctypes' desc_not_grpcMsg.
func ReqAtMostOnce(ctx context.Context, kc pb.KVClient, k string) {
	before, err := kc.Range(ctx, &pb.RangeRequest{Key: []byte(k)})
	if err != nil {
		return
	}
	_, err = kc.Put(ctx, &pb.PutRequest{Key: []byte(k), Value: []byte("x")})
	after, err2 := kc.Range(ctx, &pb.RangeRequest{Key: []byte(k)})
	if err != nil || err2 != nil {
		return
	}
	var v0 int64
	if len(before.Kvs) == 1 {
		v0 = before.Kvs[0].Version
	}
	if len(after.Kvs) == 1 && after.Kvs[0].Version > v0+1 {
		panic("at-most-once: one put applied twice")
	}
}

// REQ grpc/status-classify: status.FromError reads a status error's code and message; an etcd
// status maps to its client-side value through rpctypes.Error; a context's error is no etcd error.
// Users: the client's ContextError, isHaltErr, isUnavailableErr, isSafeRetry* (W0, 1b, 1c);
// leasing's acquire (1e: Unavailable).
// Assumes: none.
// Specs: Grpc.Error.spec, FromError.spec, Status.Code.spec, Status.Message.spec; rpctypes'
// Error.spec, ErrorDesc.spec, init.spec, ctxErr_errMsg.
func ReqStatusClassify() {
	err := status.Error(codes.OutOfRange, "etcdserver: mvcc: required revision has been compacted")
	s, ok := status.FromError(err)
	if !ok || s.Code() != codes.OutOfRange {
		panic("status: a status error's code")
	}
	if rpctypes.Error(err) != rpctypes.ErrCompacted {
		panic("status: etcd's status is not its error")
	}
	if rpctypes.Error(context.Canceled) != context.Canceled {
		panic("status: a context's error became an etcd error")
	}
	if errors.Is(context.Canceled, io.EOF) {
		panic("status: a context's error is io.EOF")
	}
}

// REQ grpc/metadata-out: a context's outgoing metadata is what NewOutgoingContext attached, with the
// key lowercased by Set; the caller's map is copied before it is written.
// Users: the client's WithRequireLeader, withVersion (W0, 1c), Kubernetes' client setup.
// Assumes: ctx carries no outgoing metadata (Context.ctxNoMeta ctx: Value(mdOutgoingKey{}) is nil),
// which FromOutgoingContext.spec's gated row turns into ok = false (recheck RR1).
// Specs: FromOutgoingContext.spec (the nil case, mdAtN true), MD.Copy.spec and MD.Get.spec of
// the nil map, MD.Set.spec, NewOutgoingContext.spec; laws: outMD_noMeta. (Re-review R-A6 N1: the
// nil case was contradictory, so this snippet was proved vacuously; it now checks ok and nil.)
func ReqMetadataOut(ctx context.Context) {
	md, ok := metadata.FromOutgoingContext(ctx)
	if ok || md != nil {
		panic("metadata: a context with no outgoing metadata has some")
	}
	cp := md.Copy() // of the nil map: a fresh empty one
	cp.Set("HasLeader", "true")
	ctx2 := metadata.NewOutgoingContext(ctx, cp)
	got, ok := metadata.FromOutgoingContext(ctx2)
	if !ok || len(got.Get("hasleader")) != 1 || got.Get("hasleader")[0] != "true" {
		panic("metadata: the attached key is not there")
	}
	if len(md.Get("hasleader")) != 0 {
		panic("metadata: the original map was written")
	}
}
