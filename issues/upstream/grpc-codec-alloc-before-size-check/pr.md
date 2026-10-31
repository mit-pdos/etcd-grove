Title: encoding/proto: check the message size before allocating

Fixes #<issue>

[`codecV2.Marshal`](https://github.com/grpc/grpc-go/blob/bc90736a6fadc41582f9a23fb955bb66088f1bb8/encoding/proto/proto.go#L51-L80) allocates the message's encoded size before [`encode`'s 4 GiB check](https://github.com/grpc/grpc-go/blob/bc90736a6fadc41582f9a23fb955bb66088f1bb8/rpc_util.go#L820-L823) and the send limits run. Above Go's maximum allocation (2^48 bytes on 64-bit platforms) the allocation panics, in a client sending a request or a server sending a reply. This PR makes `Marshal` return `ResourceExhausted` for a message over 4 GiB before allocating, and `encode` return a codec's status error unchanged instead of as `Internal`.

The first commit adds tests of the issue's example, which panic on `master`; the second, the fix, makes them pass.

Written with the assistance of generative AI; I reviewed and tested every change.

RELEASE NOTES:
* encoding/proto: Sending a message whose encoding is too large to allocate now fails with `ResourceExhausted` instead of panicking.
