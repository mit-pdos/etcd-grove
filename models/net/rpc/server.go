// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

/*
Package rpc provides access to the exported methods of an object across a
network or other I/O connection.

The net/rpc package is frozen and is not accepting new features.

A server registers an object, making it visible
as a service with the name of the type of the object.  After registration, exported
methods of the object will be accessible remotely.  A server may register multiple
objects (services) of different types but it is an error to register multiple
objects of the same type.

Only methods that satisfy these criteria will be made available for remote access;
other methods will be ignored:

  - the method's type is exported.
  - the method is exported.
  - the method has two arguments, both exported (or builtin) types.
  - the method's second argument is a pointer.
  - the method has return type error.

In effect, the method must look schematically like

	func (t *T) MethodName(argType T1, replyType *T2) error

where T1 and T2 can be marshaled by encoding/gob.
These requirements apply even if a different codec is used.
(In the future, these requirements may soften for custom codecs.)

The method's first argument represents the arguments provided by the caller; the
second argument represents the result parameters to be returned to the caller.
The method's return value, if non-nil, is passed back as a string that the client
sees as if created by [errors.New].  If an error is returned, the reply parameter
will not be sent back to the client.

The server may handle requests on a single connection by calling [ServeConn].  More
typically it will create a network listener and call [Accept] or, for an HTTP
listener, [HandleHTTP] and [http.Serve].

A client wishing to use the service establishes a connection and then invokes
[NewClient] on the connection.  The convenience function [Dial] ([DialHTTP]) performs
both steps for a raw network connection (an HTTP connection).  The resulting
[Client] object has two methods, [Call] and Go, that specify the service and method to
call, a pointer containing the arguments, and a pointer to receive the result
parameters.

The Call method waits for the remote call to complete while the Go method
launches the call asynchronously and signals completion using the Call
structure's Done channel.

Unless an explicit codec is set up, package [encoding/gob] is used to
transport the data.

Here is a simple example.  A server wishes to export an object of type Arith:

	package server

	import "errors"

	type Args struct {
		A, B int
	}

	type Quotient struct {
		Quo, Rem int
	}

	type Arith int

	func (t *Arith) Multiply(args *Args, reply *int) error {
		*reply = args.A * args.B
		return nil
	}

	func (t *Arith) Divide(args *Args, quo *Quotient) error {
		if args.B == 0 {
			return errors.New("divide by zero")
		}
		quo.Quo = args.A / args.B
		quo.Rem = args.A % args.B
		return nil
	}

The server calls (for HTTP service):

	arith := new(Arith)
	rpc.Register(arith)
	rpc.HandleHTTP()
	l, err := net.Listen("tcp", ":1234")
	if err != nil {
		log.Fatal("listen error:", err)
	}
	go http.Serve(l, nil)

At this point, clients can see a service "Arith" with methods "Arith.Multiply" and
"Arith.Divide".  To invoke one, a client first dials the server:

	client, err := rpc.DialHTTP("tcp", serverAddress + ":1234")
	if err != nil {
		log.Fatal("dialing:", err)
	}

Then it can make a remote call:

	// Synchronous call
	args := &server.Args{7,8}
	var reply int
	err = client.Call("Arith.Multiply", args, &reply)
	if err != nil {
		log.Fatal("arith error:", err)
	}
	fmt.Printf("Arith: %d*%d=%d", args.A, args.B, reply)

or

	// Asynchronous call
	quotient := new(Quotient)
	divCall := client.Go("Arith.Divide", args, quotient, nil)
	replyCall := <-divCall.Done	// will be equal to divCall
	// check errors, print, etc.

A server implementation will often provide a simple, type-safe wrapper for the
client.
*/
package rpc

import (
	"errors"
	"go/token"
	"io"
	"log"
	"net"
	"net/http"
	"sync"
)

const (
	// Defaults used by HandleHTTP
	DefaultRPCPath   = "/_goRPC_"
	DefaultDebugPath = "/debug/rpc"
)

// MODEL: a method is the program's generated Method (codec.go) in place of reflection's
// reflect.Method and argument types; a service's receiver is kept as it was passed to
// Register.
type methodType struct {
	sync.Mutex // protects counters
	m          *Method
	numCalls   uint
}

type service struct {
	name   string                 // name of service
	rcvr   any                    // receiver of methods for the service
	method map[string]*methodType // registered methods
}

// Request is a header written before every RPC call. It is used internally
// but documented here as an aid to debugging, such as when analyzing
// network traffic.
type Request struct {
	ServiceMethod string   // format: "Service.Method"
	Seq           uint64   // sequence number chosen by client
	next          *Request // for free list in Server
}

// Response is a header written before every RPC return. It is used internally
// but documented here as an aid to debugging, such as when analyzing
// network traffic.
type Response struct {
	ServiceMethod string    // echoes that of the Request
	Seq           uint64    // echoes that of the request
	Error         string    // error, if any.
	next          *Response // for free list in Server
}

// Server represents an RPC Server.
//
// MODEL: the services are a map under a mutex in place of a sync.Map (the same
// LoadOrStore and Load).
type Server struct {
	mapLock    sync.Mutex          // protects serviceMap
	serviceMap map[string]*service // map[string]*service
	reqLock    sync.Mutex          // protects freeReq
	freeReq    *Request
	respLock   sync.Mutex // protects freeResp
	freeResp   *Response
}

// NewServer returns a new [Server].
func NewServer() *Server {
	return &Server{serviceMap: make(map[string]*service)}
}

// DefaultServer is the default instance of [*Server].
var DefaultServer = NewServer()

// Register publishes in the server the set of methods of the
// receiver value that satisfy the following conditions:
//   - exported method of exported type
//   - two arguments, both of exported type
//   - the second argument is a pointer
//   - one return value, of type error
//
// It returns an error if the receiver is not an exported type or has
// no suitable methods. It also logs the error using package log.
// The client accesses each method using a string of the form "Type.Method",
// where Type is the receiver's concrete type.
func (server *Server) Register(rcvr any) error {
	return server.register(rcvr, "", false)
}

// RegisterName is like [Register] but uses the provided name for the type
// instead of the receiver's concrete type.
func (server *Server) RegisterName(name string, rcvr any) error {
	return server.register(rcvr, name, true)
}

// logRegisterError specifies whether to log problems during method registration.
// To debug registration, recompile the package with this set to true.
const logRegisterError = false

// MODEL: the receiver's facts reflection gives (its type's name and string, the methods
// suitableMethods finds for its type and for a pointer to it) are the program's generated
// Codec's (codec.go, Receiver), which is stuck (Stuck) for a receiver of a type it does not list.
func (server *Server) register(rcvr any, name string, useName bool) error {
	s := new(service)
	r := getCodec().Receiver(rcvr)
	s.rcvr = rcvr
	sname := name
	if !useName {
		if r.NilPtr {
			// reflect.Indirect of a nil pointer is the zero Value, whose Type panics
			panic("reflect: call of reflect.Value.Type on zero Value")
		}
		sname = r.Name
	}
	if sname == "" {
		s := "rpc.Register: no service name for type " + r.Type
		log.Println(s) // MODEL: log.Print, as log.Println (Perennial models Println; one string operand: the same output)
		return errors.New(s)
	}
	if !useName && !token.IsExported(sname) {
		s := "rpc.Register: type " + sname + " is not exported"
		log.Println(s) // MODEL: log.Print, as log.Println (Perennial models Println; one string operand: the same output)
		return errors.New(s)
	}
	s.name = sname

	// Install the methods
	s.method = make(map[string]*methodType)
	for mname, m := range r.Methods {
		s.method[mname] = &methodType{m: m}
	}

	if len(s.method) == 0 {
		str := ""

		// To help the user, see if a pointer receiver would work.
		if r.PtrHasMethods {
			str = "rpc.Register: type " + sname + " has no exported methods of suitable type (hint: pass a pointer to value of that type)"
		} else {
			str = "rpc.Register: type " + sname + " has no exported methods of suitable type"
		}
		log.Println(str) // MODEL: log.Print, as log.Println (one string operand: the same output)
		return errors.New(str)
	}

	server.mapLock.Lock()
	_, dup := server.serviceMap[sname]
	if !dup {
		server.serviceMap[sname] = s
	}
	server.mapLock.Unlock()
	if dup {
		return errors.New("rpc: service already defined: " + sname)
	}
	return nil
}

// A value sent as a placeholder for the server's response value when the server
// receives an invalid request. It is never decoded by the client since the Response
// contains an error when it is used.
var invalidRequest = struct{}{}

func (server *Server) sendResponse(sending *sync.Mutex, req *Request, reply any, codec ServerCodec, errmsg string) {
	resp := server.getResponse()
	// Encode the response header
	resp.ServiceMethod = req.ServiceMethod
	if errmsg != "" {
		resp.Error = errmsg
		reply = invalidRequest
	}
	resp.Seq = req.Seq
	sending.Lock()
	err := codec.WriteResponse(resp, reply)
	if debugLog && err != nil {
		log.Println("rpc: writing response:", err)
	}
	sending.Unlock()
	server.freeResponse(resp)
}

func (m *methodType) NumCalls() (n uint) {
	m.Lock()
	n = m.numCalls
	m.Unlock()
	return n
}

// MODEL: the method is called through the program's generated Method (codec.go) in place of
// reflect's Value.Call.
func (s *service) call(server *Server, sending *sync.Mutex, wg *sync.WaitGroup, mtype *methodType, req *Request, argv, replyv any, codec ServerCodec) {
	if wg != nil {
		defer wg.Done()
	}
	mtype.Lock()
	mtype.numCalls++
	mtype.Unlock()
	// Invoke the method, providing a new value for the reply.
	errInter := mtype.m.Call(s.rcvr, argv, replyv)
	// The return value for the method is an error.
	errmsg := ""
	if errInter != nil {
		errmsg = errInter.Error()
	}
	server.sendResponse(sending, req, replyv, codec, errmsg)
	server.freeRequest(req)
}

// ServeConn runs the server on a single connection.
// ServeConn blocks, serving the connection until the client hangs up.
// The caller typically invokes ServeConn in a go statement.
// ServeConn uses the gob wire format (see package gob) on the
// connection. To use an alternate codec, use [ServeCodec].
// See [NewClient]'s comment for information about concurrent access.
//
// MODEL: the codec is the model's frame codec over the program's generated Codec
// (codec.go), in place of gob's.
func (server *Server) ServeConn(conn io.ReadWriteCloser) {
	server.ServeCodec(newServerCodec(conn))
}

// ServeCodec is like [ServeConn] but uses the specified codec to
// decode requests and encode responses.
func (server *Server) ServeCodec(codec ServerCodec) {
	sending := new(sync.Mutex)
	wg := new(sync.WaitGroup)
	for {
		service, mtype, req, argv, replyv, keepReading, err := server.readRequest(codec)
		if err != nil {
			if debugLog && err != io.EOF {
				log.Println("rpc:", err)
			}
			if !keepReading {
				break
			}
			// send a response if we actually managed to read a header.
			if req != nil {
				server.sendResponse(sending, req, invalidRequest, codec, err.Error())
				server.freeRequest(req)
			}
			continue
		}
		wg.Add(1)
		go service.call(server, sending, wg, mtype, req, argv, replyv, codec)
	}
	// We've seen that there are no more requests.
	// Wait for responses to be sent before closing codec.
	wg.Wait()
	codec.Close()
}

// ServeRequest is like [ServeCodec] but synchronously serves a single request.
// It does not close the codec upon completion.
func (server *Server) ServeRequest(codec ServerCodec) error {
	sending := new(sync.Mutex)
	service, mtype, req, argv, replyv, keepReading, err := server.readRequest(codec)
	if err != nil {
		if !keepReading {
			return err
		}
		// send a response if we actually managed to read a header.
		if req != nil {
			server.sendResponse(sending, req, invalidRequest, codec, err.Error())
			server.freeRequest(req)
		}
		return err
	}
	service.call(server, sending, nil, mtype, req, argv, replyv, codec)
	return nil
}

func (server *Server) getRequest() *Request {
	server.reqLock.Lock()
	req := server.freeReq
	if req == nil {
		req = new(Request)
	} else {
		server.freeReq = req.next
		*req = Request{}
	}
	server.reqLock.Unlock()
	return req
}

func (server *Server) freeRequest(req *Request) {
	server.reqLock.Lock()
	req.next = server.freeReq
	server.freeReq = req
	server.reqLock.Unlock()
}

func (server *Server) getResponse() *Response {
	server.respLock.Lock()
	resp := server.freeResp
	if resp == nil {
		resp = new(Response)
	} else {
		server.freeResp = resp.next
		*resp = Response{}
	}
	server.respLock.Unlock()
	return resp
}

func (server *Server) freeResponse(resp *Response) {
	server.respLock.Lock()
	resp.next = server.freeResp
	server.freeResp = resp
	server.respLock.Unlock()
}

// MODEL: the argument and reply values are made by the program's generated Method (codec.go)
// in place of reflect.New (and reflect.MakeMap, MakeSlice for a map or slice reply): argv is
// always a pointer to the argument (the Method dereferences it for a method that takes a value).
func (server *Server) readRequest(codec ServerCodec) (service *service, mtype *methodType, req *Request, argv, replyv any, keepReading bool, err error) {
	service, mtype, req, keepReading, err = server.readRequestHeader(codec)
	if err != nil {
		if !keepReading {
			return
		}
		// discard body
		codec.ReadRequestBody(nil)
		return
	}

	// Decode the argument value.
	argv = mtype.m.NewArg()
	// argv guaranteed to be a pointer now.
	if err = codec.ReadRequestBody(argv); err != nil {
		return
	}

	replyv = mtype.m.NewReply()
	return
}

func (server *Server) readRequestHeader(codec ServerCodec) (svc *service, mtype *methodType, req *Request, keepReading bool, err error) {
	// Grab the request header.
	req = server.getRequest()
	err = codec.ReadRequestHeader(req)
	if err != nil {
		req = nil
		if err == io.EOF || err == io.ErrUnexpectedEOF {
			return
		}
		err = errors.New("rpc: server cannot decode request: " + err.Error())
		return
	}

	// We read the header successfully. If we see an error now,
	// we can still recover and move on to the next request.
	keepReading = true

	// MODEL: strings.LastIndex(req.ServiceMethod, "."), as a backwards byte loop (Perennial has no
	// model of LastIndex; for a one-byte separator the same index, -1 if absent)
	dot := -1
	for i := len(req.ServiceMethod) - 1; i >= 0; i-- {
		if req.ServiceMethod[i] == '.' {
			dot = i
			break
		}
	}
	if dot < 0 {
		err = errors.New("rpc: service/method request ill-formed: " + req.ServiceMethod)
		return
	}
	serviceName := req.ServiceMethod[:dot]
	methodName := req.ServiceMethod[dot+1:]

	// Look up the request.
	server.mapLock.Lock()
	svci, ok := server.serviceMap[serviceName]
	server.mapLock.Unlock()
	if !ok {
		err = errors.New("rpc: can't find service " + req.ServiceMethod)
		return
	}
	svc = svci
	mtype = svc.method[methodName]
	if mtype == nil {
		err = errors.New("rpc: can't find method " + req.ServiceMethod)
	}
	return
}

// Accept accepts connections on the listener and serves requests
// for each incoming connection. Accept blocks until the listener
// returns a non-nil error. The caller typically invokes Accept in a
// go statement.
func (server *Server) Accept(lis net.Listener) {
	for {
		conn, err := lis.Accept()
		if err != nil {
			// MODEL: log.Print("rpc.Serve: accept:", err.Error()), as log.Println of the concatenation
			// (fmt.Sprint puts no space between string operands: the same output)
			log.Println("rpc.Serve: accept:" + err.Error())
			return
		}
		go server.ServeConn(conn)
	}
}

// Register publishes the receiver's methods in the [DefaultServer].
func Register(rcvr any) error { return DefaultServer.Register(rcvr) }

// RegisterName is like [Register] but uses the provided name for the type
// instead of the receiver's concrete type.
func RegisterName(name string, rcvr any) error {
	return DefaultServer.RegisterName(name, rcvr)
}

// A ServerCodec implements reading of RPC requests and writing of
// RPC responses for the server side of an RPC session.
// The server calls [ServerCodec.ReadRequestHeader] and [ServerCodec.ReadRequestBody] in pairs
// to read requests from the connection, and it calls [ServerCodec.WriteResponse] to
// write a response back. The server calls [ServerCodec.Close] when finished with the
// connection. ReadRequestBody may be called with a nil
// argument to force the body of the request to be read and discarded.
// See [NewClient]'s comment for information about concurrent access.
type ServerCodec interface {
	ReadRequestHeader(*Request) error
	ReadRequestBody(any) error
	WriteResponse(*Response, any) error

	// Close can be called multiple times and must be idempotent.
	Close() error
}

// ServeConn runs the [DefaultServer] on a single connection.
// ServeConn blocks, serving the connection until the client hangs up.
// The caller typically invokes ServeConn in a go statement.
// ServeConn uses the gob wire format (see package gob) on the
// connection. To use an alternate codec, use [ServeCodec].
// See [NewClient]'s comment for information about concurrent access.
func ServeConn(conn io.ReadWriteCloser) {
	DefaultServer.ServeConn(conn)
}

// ServeCodec is like [ServeConn] but uses the specified codec to
// decode requests and encode responses.
func ServeCodec(codec ServerCodec) {
	DefaultServer.ServeCodec(codec)
}

// ServeRequest is like [ServeCodec] but synchronously serves a single request.
// It does not close the codec upon completion.
func ServeRequest(codec ServerCodec) error {
	return DefaultServer.ServeRequest(codec)
}

// Accept accepts connections on the listener and serves requests
// to [DefaultServer] for each incoming connection.
// Accept blocks; the caller typically invokes it in a go statement.
func Accept(lis net.Listener) { DefaultServer.Accept(lis) }

// Can connect to RPC service using HTTP CONNECT to rpcPath.
var connected = "200 Connected to Go RPC"

// ServeHTTP implements an [http.Handler] that answers RPC requests.
func (server *Server) ServeHTTP(w http.ResponseWriter, req *http.Request) {
	if req.Method != "CONNECT" {
		w.Header().Set("Content-Type", "text/plain; charset=utf-8")
		w.WriteHeader(http.StatusMethodNotAllowed)
		io.WriteString(w, "405 must CONNECT\n")
		return
	}
	conn, _, err := w.(http.Hijacker).Hijack()
	if err != nil {
		// MODEL: log.Print of four strings, as log.Println of their concatenation (the same output)
		log.Println("rpc hijacking " + req.RemoteAddr + ": " + err.Error())
		return
	}
	// MODEL: io.WriteString(conn, s) as conn.Write([]byte(s)), as in DialHTTPPath.
	conn.Write([]byte("HTTP/1.0 " + connected + "\n\n"))
	server.ServeConn(conn)
}

// HandleHTTP registers an HTTP handler for RPC messages on rpcPath,
// and a debugging handler on debugPath.
// It is still necessary to invoke [http.Serve](), typically in a go statement.
func (server *Server) HandleHTTP(rpcPath, debugPath string) {
	http.Handle(rpcPath, server)
	http.Handle(debugPath, debugHTTP{server})
}

// HandleHTTP registers an HTTP handler for RPC messages to [DefaultServer]
// on [DefaultRPCPath] and a debugging handler on [DefaultDebugPath].
// It is still necessary to invoke [http.Serve](), typically in a go statement.
func HandleHTTP() {
	DefaultServer.HandleHTTP(DefaultRPCPath, DefaultDebugPath)
}
