Title: encoding/proto: Marshal panics with "makeslice: len out of range" for a message whose encoding is over 2^48 bytes

### What version of gRPC are you using?

`master` (bc90736a).

### What version of Go are you using (`go version`)?

go1.27.1

### What operating system (Linux, Windows, …) and version?

Linux, amd64.

### What did you do?

Marshaled, with the proto codec, a message whose encoding is larger than 2^48 bytes, the largest allocation Go allows on linux/amd64. A repeated field that holds one submessage many times makes such a message cheap to build: here one 16 MiB value is held 2^24 times, about 150 MiB of memory.

```go
package main

import (
	"fmt"
	"strings"

	"google.golang.org/grpc/encoding"
	"google.golang.org/grpc/encoding/proto"
	"google.golang.org/protobuf/types/known/structpb"
)

func main() {
	v := structpb.NewStringValue(strings.Repeat("a", 1<<24)) // 16 MiB
	l := &structpb.ListValue{Values: make([]*structpb.Value, 1<<24)}
	for i := range l.Values {
		l.Values[i] = v // the same value 2^24 times: over 2^48 bytes encoded
	}
	_, err := encoding.GetCodecV2(proto.Name).Marshal(l)
	fmt.Println(err)
}
```

A client calling `Invoke` with this message as the request panics the same way, and a server sending a reply goes through the same codec.

### What did you expect to see?

`Marshal` should return an error, and an RPC sending such a message should fail with `ResourceExhausted`, the code gRPC uses for a message over its size limits.

### What did you see instead?

The program panics (output trimmed):

```
panic: runtime error: makeslice: len out of range

goroutine 1 [running]:
google.golang.org/grpc/internal/mem.(*SimpleBufferPool).Get(0x2350a8c6ebd0, 0x100000a000000)
	internal/mem/buffer_pool.go:356 +0xf4
google.golang.org/grpc/internal/mem.(*BinaryTieredBufferPool).Get(0x765750?, 0x7b6b80?)
	internal/mem/buffer_pool.go:157 +0x72
google.golang.org/grpc/encoding/proto.(*codecV2).Marshal(0x7d0490?, {0x765750?, 0x2350a8c50200?})
	encoding/proto/proto.go:74 +0x118
main.main()
```

Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and reviewed the report.
