package rpc

import "sync"

// Codec is the model's stand-in for gob and reflection: a kit's generated encoders, decoders and
// dispatch table for exactly the types and methods kit.toml's [rpc] lists (harness/kitgen). It
// is not in Go's net/rpc; the kit's generated registerRPC (built only for the model, build tag
// rpcmodel) calls SetCodec, and the real build has a no-op in its place.
//
//   - Encode(v): v's type tag and encoding; v is a listed type or a non-nil pointer to one (as
//     gob, pointers are flattened). Panics otherwise.
//   - Decode(data, ptr): ptr is a non-nil pointer to a listed type whose value is zero; decodes
//     data into *ptr as gob would (an error if gob would refuse the encoded type). Panics
//     otherwise.
//   - Methods(rcvr): the number of methods net/rpc's reflection would register for rcvr, a
//     listed receiver type. Panics for any other receiver.
//   - Name(rcvr): the service name Register gives rcvr, a listed receiver type: its type's name
//     (reflection's reflect.Indirect(v).Type().Name()). Panics for any other receiver.
//   - Call(rcvr, method, args): runs rcvr's method on args decoded into a new value of its
//     argument type and a new reply value; (encoded reply, "", true), or (nil, the method's or
//     the decoder's error message, true), or (nil, "", false) if rcvr has no such method.
type Codec struct {
	Encode  func(v interface{}) []byte
	Decode  func(data []byte, ptr interface{}) error
	Methods func(rcvr interface{}) uint64
	Call    func(rcvr interface{}, method string, args []byte) ([]byte, string, bool)
	Name    func(rcvr interface{}) string
}

var codecMu sync.Mutex
var codec *Codec

// SetCodec registers the kit's codec; the first registration stays.
func SetCodec(c *Codec) {
	codecMu.Lock()
	if codec == nil {
		codec = c
	}
	codecMu.Unlock()
}

func getCodec() *Codec {
	codecMu.Lock()
	c := codec
	codecMu.Unlock()
	if c == nil {
		panic("net/rpc model: no codec registered (the kit's registerRPC)")
	}
	return c
}
