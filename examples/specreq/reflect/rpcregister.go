package reflect

// Method sets by reflection and Value.Call: net/rpc's Register and its
// dispatch.
//
// Mirrors Go 1.27.3 net/rpc/server.go:
//   - :152 (`typeOfError = reflect.TypeFor[error]()`);
//   - :206-212 (isExportedOrBuiltinType: strip pointers by Elem, then
//     `isExportedName(t.Name()) || t.PkgPath() == ""`);
//   - :236-278 (register: `s.typ = reflect.TypeOf(rcvr)`, `s.rcvr =
//     reflect.ValueOf(rcvr)`, `sname := reflect.Indirect(s.rcvr).Type().Name()`,
//     errors for an empty or unexported name and for no suitable method, with
//     a hint from `reflect.PointerTo(s.typ)`'s methods);
//   - :285-341 (suitableMethods: `typ.NumMethod()`, `typ.Method(m)`,
//     `method.IsExported()`, `mtype.NumIn() != 3`, `mtype.In(1)`,
//     `mtype.In(2).Kind() != reflect.Pointer`, `mtype.NumOut() != 1`,
//     `mtype.Out(0) != typeOfError`);
//   - :561-582 (readRequest: `reflect.New(mtype.ArgType.Elem())` for a
//     pointer argument, else `reflect.New(ArgType)` and Elem after decoding;
//     the reply `reflect.New(mtype.ReplyType.Elem())`, pre-filled by MakeMap or
//     MakeSlice for map and slice replies);
//   - :381-390 (call: `function.Call([]reflect.Value{s.rcvr, argv, replyv})`,
//     `returnValues[0].Interface()`, `.(error).Error()`).
// Users: examples/dsverify/epaxos/master/master.go:67 (`rpc.Register(master)`)
// and the dsverify ports' servers; this repository's net/rpc model (models/
// net/rpc, models/README.md) replaces the reflection by a generated codec, and
// models/rpcdesc copies suitableMethods to derive it. go-cmp's tryMethod
// (MethodByName("Equal") then Call) and protobuf-go's
// `PtrTo(t).MethodByName("XXX_OneofWrappers")` + `Func.Call` (internal/impl/
// message.go:198-212) are the same pattern. snippets_test.go checks the
// mirror against net/rpc's own Register.
//
// Go's panic: Register(nil) panics in reflect ("reflect: call of
// reflect.Value.Type on zero Value"): Indirect of the zero Value is zero.
//
// To prove: register finds exactly the methods of the form
// `func (T) M(*Args or exported/builtin type, *Reply) error` (and refuses
// the receiver type with an error otherwise); a call through Value.Call runs
// the method on the receiver with the new argument and reply and returns its
// error; the reply written by the method is the caller's.
//
// Needs R1 (method sets of a type in order, Method(i) with Name, Type,
// IsExported; func types' NumIn/In/NumOut/Out; Name, PkgPath, Kind, Elem;
// PointerTo; type identity with error's type) and R2 (ValueOf, Indirect, New,
// Elem, Method's Func as a Value, Call with the receiver first, Interface).

import (
	"errors"
	"reflect"
)

type Args struct{ A, B int }

type Arith int

func (t *Arith) Multiply(args *Args, reply *int) error {
	*reply = args.A * args.B
	return nil
}

func (t *Arith) Divide(args Args, reply *int) error {
	if args.B == 0 {
		return errors.New("divide by zero")
	}
	*reply = args.A / args.B
	return nil
}

// not suitable: no reply pointer, two results, unexported
func (t *Arith) Bad(args *Args) error                { return nil }
func (t *Arith) Two(args *Args, r *int) (int, error) { return 0, nil }
func (t *Arith) hidden(args *Args, r *int) error     { return nil }

type noMethods struct{}

var typeOfError = reflect.TypeFor[error]()

type rpcMethod struct {
	method    reflect.Method
	ArgType   reflect.Type
	ReplyType reflect.Type
}

// isExportedName is go/token's IsExported for ASCII names (unicode.IsUpper of the first rune;
// this repository's go/token is a trusted model in the part Net/, which the main tree does not
// import).
func isExportedName(name string) bool {
	return name != "" && 'A' <= name[0] && name[0] <= 'Z'
}

func isExportedOrBuiltinType(t reflect.Type) bool {
	for t.Kind() == reflect.Pointer {
		t = t.Elem()
	}
	return isExportedName(t.Name()) || t.PkgPath() == ""
}

func suitableMethods(typ reflect.Type) map[string]*rpcMethod {
	methods := make(map[string]*rpcMethod)
	for m := 0; m < typ.NumMethod(); m++ {
		method := typ.Method(m)
		mtype := method.Type
		mname := method.Name
		if !method.IsExported() {
			continue
		}
		if mtype.NumIn() != 3 {
			continue
		}
		argType := mtype.In(1)
		if !isExportedOrBuiltinType(argType) {
			continue
		}
		replyType := mtype.In(2)
		if replyType.Kind() != reflect.Pointer || !isExportedOrBuiltinType(replyType) {
			continue
		}
		if mtype.NumOut() != 1 || mtype.Out(0) != typeOfError {
			continue
		}
		methods[mname] = &rpcMethod{method: method, ArgType: argType, ReplyType: replyType}
	}
	return methods
}

type rpcService struct {
	name   string
	rcvr   reflect.Value
	typ    reflect.Type
	method map[string]*rpcMethod
}

// register is server.go:236-278, its errors as strings.
func register(rcvr any) (*rpcService, string) {
	s := new(rpcService)
	s.typ = reflect.TypeOf(rcvr)
	s.rcvr = reflect.ValueOf(rcvr)
	sname := reflect.Indirect(s.rcvr).Type().Name()
	if sname == "" {
		return nil, "rpc.Register: no service name for type " + s.typ.String()
	}
	if !isExportedName(sname) {
		return nil, "rpc.Register: type " + sname + " is not exported"
	}
	s.name = sname
	s.method = suitableMethods(s.typ)
	if len(s.method) == 0 {
		if len(suitableMethods(reflect.PointerTo(s.typ))) != 0 {
			return nil, "rpc.Register: type " + sname + " has no exported methods of suitable type (hint: pass a pointer to value of that type)"
		}
		return nil, "rpc.Register: type " + sname + " has no exported methods of suitable type"
	}
	return s, ""
}

// call is readRequest's allocation, then service.call: the argument is
// "decoded" by set.
func (s *rpcService) call(name string, set func(argv reflect.Value)) (reflect.Value, string) {
	mtype := s.method[name]
	var argv reflect.Value
	argIsValue := false
	if mtype.ArgType.Kind() == reflect.Pointer {
		argv = reflect.New(mtype.ArgType.Elem())
	} else {
		argv = reflect.New(mtype.ArgType)
		argIsValue = true
	}
	set(argv)
	if argIsValue {
		argv = argv.Elem()
	}
	replyv := reflect.New(mtype.ReplyType.Elem())
	function := mtype.method.Func
	returnValues := function.Call([]reflect.Value{s.rcvr, argv, replyv})
	if errInter := returnValues[0].Interface(); errInter != nil {
		return replyv, errInter.(error).Error()
	}
	return replyv, ""
}

// REQ reflect/rpc-register: register of *Arith finds exactly Multiply and Divide; calls through
// Value.Call run them with a pointer argument and with a value argument, write the reply, and
// return the method's error; register refuses a value of a type with only pointer methods
// (with the hint), an unexported type and a type with no methods.
// Users: Go net/rpc server.go:236-390 (Register, ServeCodec); examples/dsverify/epaxos/master/
// master.go:67; models/rpcdesc's copy of suitableMethods; go-cmp tryMethod; protobuf-go
// message.go:198-212.
// Assumes: nothing.
// Specs: none yet; needs R1 (method sets, func types) and R2 (Call) (doc.go).
func ReqRPCRegister() {
	s, err := register(new(Arith))
	if err != "" || s.name != "Arith" || len(s.method) != 2 || s.method["Multiply"] == nil || s.method["Divide"] == nil {
		panic("rpc-register: suitable methods")
	}
	reply, err := s.call("Multiply", func(argv reflect.Value) { argv.Elem().Set(reflect.ValueOf(Args{6, 7})) })
	if err != "" || reply.Elem().Int() != 42 {
		panic("rpc-register: Multiply")
	}
	reply, err = s.call("Divide", func(argv reflect.Value) { argv.Interface().(*Args).A = 9; argv.Elem().Field(1).SetInt(3) })
	if err != "" || *reply.Interface().(*int) != 3 {
		panic("rpc-register: Divide with a value argument")
	}
	if _, err = s.call("Divide", func(argv reflect.Value) {}); err != "divide by zero" {
		panic("rpc-register: the method's error")
	}
	if _, err := register(Arith(0)); err != "rpc.Register: type Arith has no exported methods of suitable type (hint: pass a pointer to value of that type)" {
		panic("rpc-register: a value receiver: " + err)
	}
	if _, err := register(&noMethods{}); err != "rpc.Register: type noMethods is not exported" {
		panic("rpc-register: an unexported type: " + err)
	}
	if _, err := register(&Pod2{}); err != "rpc.Register: type Pod2 has no exported methods of suitable type" {
		panic("rpc-register: no suitable method: " + err)
	}
}

// REQ reflect/rpc-register (panics): register(nil) panics "reflect: call of
// reflect.Value.Type on zero Value", as net/rpc's Register(nil) does.
// Specs: none yet.
func MustPanicRegisterNil() {
	register(nil)
}
