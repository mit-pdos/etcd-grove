// A bound of clientErrTys (k8s 7e-1): with a service-config retry policy, grpc-go v1.84's stream
// returns a *fmt.wrapError ("max retries exhausted"), not one of clientErrTys; etcd's resolver config
// has no retry policy (grpcResolverAt).
package main

import (
	"context"
	"errors"
	"fmt"
	"io"
	"net"

	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/credentials/insecure"
	hpb "google.golang.org/grpc/health/grpc_health_v1"
	"google.golang.org/grpc/status"
)

type srv struct{ hpb.UnimplementedHealthServer }

func (srv) Watch(*hpb.HealthCheckRequest, hpb.Health_WatchServer) error {
	return status.Error(codes.Unavailable, "go away")
}

func main() {
	lis, _ := net.Listen("tcp", "127.0.0.1:0")
	s := grpc.NewServer()
	hpb.RegisterHealthServer(s, srv{})
	go s.Serve(lis)
	sc := `{"methodConfig":[{"name":[{"service":"grpc.health.v1.Health"}],"retryPolicy":{"maxAttempts":2,"initialBackoff":"0.01s","maxBackoff":"0.01s","backoffMultiplier":1,"retryableStatusCodes":["UNAVAILABLE"]}}]}`
	cc, err := grpc.NewClient(lis.Addr().String(), grpc.WithTransportCredentials(insecure.NewCredentials()),
		grpc.WithDisableServiceConfig(), grpc.WithDefaultServiceConfig(sc))
	if err != nil {
		panic(err)
	}
	desc := &grpc.StreamDesc{StreamName: "Watch", ServerStreams: true}
	cs, err := cc.NewStream(context.Background(), desc, "/grpc.health.v1.Health/Watch")
	fmt.Printf("NewStream err %T %v\n", err, err)
	err = cs.SendMsg(&hpb.HealthCheckRequest{})
	fmt.Printf("SendMsg err %T %v\n", err, err)
	err = cs.CloseSend()
	fmt.Printf("CloseSend err %T %v\n", err, err)
	err = cs.RecvMsg(new(hpb.HealthCheckResponse))
	fmt.Printf("RecvMsg err %T %v unwrap=%T eof=%v\n", err, err, errors.Unwrap(err), err == io.EOF)
	st, ok := status.FromError(err)
	fmt.Println("status.FromError ok:", ok, st.Code())
}
