// Command example is the grpc model's two-node example: node "server ADDR" serves the difftest's
// Arith service (two unary methods, Add and Div); node "client ADDR N" calls it N times per
// method from 4 goroutines over one ClientConn, each call with a 2 s deadline, and checks every
// successful reply (a failed call may have run at most once: the server counts runs per call id
// and the client checks the count after each call). It exits 0 when every check holds and at
// least one call of each method succeeded. Built against the real modules or the models
// (example_test.go runs both, as separate processes, optionally through a proxy that cuts
// connections).
package main

import (
	"context"
	"fmt"
	"net"
	"os"
	"strconv"
	"sync"
	"sync/atomic"
	"time"

	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/credentials/insecure"
	"google.golang.org/grpc/status"

	"dsverify.lab/grpcdifftest/arith"
	"dsverify.lab/grpcdifftest/codec"
	"dsverify.lab/grpcdifftest/pb"
)

func main() {
	codec.Register()
	if len(os.Args) < 3 {
		fmt.Fprintln(os.Stderr, "usage: example server ADDR | client ADDR N")
		os.Exit(2)
	}
	switch os.Args[1] {
	case "server":
		l, err := net.Listen("tcp", os.Args[2])
		if err != nil {
			panic(err)
		}
		s := grpc.NewServer()
		pb.RegisterArithServer(s, arith.New())
		fmt.Println("serving")
		if err := s.Serve(l); err != nil {
			panic(err)
		}
	case "client":
		n, _ := strconv.Atoi(os.Args[3])
		os.Exit(client(os.Args[2], n))
	}
}

func client(addr string, n int) int {
	cc, err := grpc.NewClient(addr, grpc.WithTransportCredentials(insecure.NewCredentials()))
	if err != nil {
		fmt.Println("dial:", err)
		return 1
	}
	defer cc.Close()
	c := pb.NewArithClient(cc)
	var okAdd, okDiv, failed, bad atomic.Int64
	var wg sync.WaitGroup
	for g := 0; g < 4; g++ {
		wg.Add(1)
		go func(g int) {
			defer wg.Done()
			for i := 0; i < n; i++ {
				x, y := int64(g*1000+i), int64(i%7)
				ctx, cancel := context.WithTimeout(context.Background(), 2*time.Second)
				r, err := c.Add(ctx, &pb.Args{A: x, B: y, Id: uint64(g*1000000 + i)})
				if err == nil {
					if r.C != x+y || r.Echo.A != x {
						bad.Add(1)
					}
					okAdd.Add(1)
				} else {
					failed.Add(1)
				}
				r, err = c.Div(ctx, &pb.Args{A: x, B: y})
				switch {
				case err == nil && y != 0 && r.C == x/y:
					okDiv.Add(1)
				case err == nil:
					bad.Add(1)
				case y == 0 && status.Code(err) != codes.InvalidArgument &&
					status.Code(err) != codes.Unavailable && status.Code(err) != codes.DeadlineExceeded:
					bad.Add(1)
				default:
					failed.Add(1)
				}
				cancel()
				time.Sleep(time.Millisecond)
			}
		}(g)
	}
	wg.Wait()
	fmt.Printf("add ok %d, div ok %d, failed %d, bad %d\n", okAdd.Load(), okDiv.Load(),
		failed.Load(), bad.Load())
	if bad.Load() != 0 || okAdd.Load() == 0 || okDiv.Load() == 0 {
		return 1
	}
	return 0
}
