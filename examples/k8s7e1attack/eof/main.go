// io.EOF's and status.Error's dynamic types (k8s 7e-1, clientErrTys): *errors.errorString and
// *status.Error, for every code but OK.
package main

import (
	"fmt"
	"io"
	"math"

	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
)

func main() {
	fmt.Printf("io.EOF: %T %v\n", io.EOF, io.EOF)
	for _, c := range []codes.Code{codes.Canceled, codes.Unknown, codes.FailedPrecondition, codes.Unimplemented, codes.Unauthenticated, 17, 1 << 31, math.MaxUint32} {
		e := status.Error(c, "m")
		fmt.Printf("status.Error(%d): %T nil=%v\n", uint32(c), e, e == nil)
	}
	fmt.Printf("status.Error(OK): %T\n", status.Error(codes.OK, "m"))
}
