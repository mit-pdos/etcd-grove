package unsafe

// a generated message's ProtoReflect method.
//
// Mirrors every generated *.pb.go (e.g. etcd's api/v3/etcdserverpb/rpc.pb.go,
// raft's raftpb/raft.pb.go):
//
//	func (x *Entry) ProtoReflect() protoreflect.Message {
//		mi := &file_raft_proto_msgTypes[0]
//		if x != nil {
//			ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
//			if ms.LoadMessageInfo() == nil {
//				ms.StoreMessageInfo(mi)
//			}
//			return ms
//		}
//		return mi.MessageOf(x)
//	}
//
// and google.golang.org/protobuf@v1.36.12/internal/impl/pointer_unsafe.go:
// 187-217 (MessageStateOf casts the message pointer to *messageState, its
// first field, documented in message_state.go as "Super-tricky"; the message
// info is loaded and stored with atomic.LoadPointer/StorePointer through a
// *unsafe.Pointer cast of a typed field; atomicNilMessage.Init publishes a
// wrapper with CompareAndSwapPointer), and messageState.messageInfo's panic
// "invalid nil message info; this suggests memory corruption due to a race or
// shallow copy on the message struct". The reverse direction, from the state
// back to the message, is pointer.AsIfaceOf (pointer_unsafe.go:82):
// reflect.NewAt(t, p).Interface().
//
// To prove: messageInfo never panics after ProtoReflect, including when two
// goroutines call ProtoReflect on the same message concurrently (both store
// the same pointer; a reader sees nil or mi), and the message recovered from
// the state is the original one, with the type assertion to *Entry
// succeeding.
//
// Needs U2 (*Entry as *messageState: the first field is at offset 0; a
// *MessageInfo field read as an unsafe.Pointer), U4 (pointer atomics on that
// field), and of examples/specreq/reflect R3 (reflect.NewAt) and R1 (the type
// the message info records).

import (
	"reflect"
	"sync/atomic"
	"unsafe"
)

// MessageState is protoimpl.MessageState (impl/message_state.go): the first
// field of every generated message.
type MessageState struct {
	atomicMessageInfo *MessageInfo
}

type messageState MessageState

type MessageInfo struct {
	GoReflectType reflect.Type // pointer to struct
	nilMessage    atomicNilMessage
}

func MessageStateOf(p unsafe.Pointer) *messageState { return (*messageState)(p) }

func (ms *messageState) pointer() pointer { return pointer{p: unsafe.Pointer(ms)} }

func (ms *messageState) LoadMessageInfo() *MessageInfo {
	return (*MessageInfo)(atomic.LoadPointer((*unsafe.Pointer)(unsafe.Pointer(&ms.atomicMessageInfo))))
}

func (ms *messageState) StoreMessageInfo(mi *MessageInfo) {
	atomic.StorePointer((*unsafe.Pointer)(unsafe.Pointer(&ms.atomicMessageInfo)), unsafe.Pointer(mi))
}

func (ms *messageState) messageInfo() *MessageInfo {
	mi := ms.LoadMessageInfo()
	if mi == nil {
		panic("invalid nil message info; this suggests memory corruption due to a race or shallow copy on the message struct")
	}
	return mi
}

// Interface is messageState.protoUnwrap: back from the state to the message.
func (ms *messageState) Interface() any {
	return reflect.NewAt(ms.messageInfo().GoReflectType.Elem(), ms.pointer().p).Interface()
}

// messageReflectWrapper stands for a nil message's reflective view.
type messageReflectWrapper struct{ mi *MessageInfo }

type atomicNilMessage struct{ p unsafe.Pointer } // p is a *messageReflectWrapper

func (m *atomicNilMessage) Init(mi *MessageInfo) *messageReflectWrapper {
	if p := atomic.LoadPointer(&m.p); p != nil {
		return (*messageReflectWrapper)(p)
	}
	w := &messageReflectWrapper{mi: mi}
	atomic.CompareAndSwapPointer(&m.p, nil, unsafe.Pointer(w))
	return (*messageReflectWrapper)(atomic.LoadPointer(&m.p))
}

// Entry is a generated message.
type Entry struct {
	state     MessageState
	sizeCache int32
	Term      uint64 `protobuf:"varint,2,opt,name=Term"`
}

var entryMsgInfo = MessageInfo{GoReflectType: reflect.TypeOf((*Entry)(nil))}

// ProtoReflect returns a *messageState for a non-nil message, a
// *messageReflectWrapper for a nil one.
func (x *Entry) ProtoReflect() any {
	mi := &entryMsgInfo
	if x != nil {
		ms := MessageStateOf(unsafe.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.nilMessage.Init(mi)
}

// REQ unsafe/message-state: ProtoReflect, called on one message from two goroutines at once,
// gives one state whose message info is set (messageInfo does not panic) and which converts back
// to the same message; on a nil message it gives the one shared nil wrapper.
// Users: every generated *.pb.go's ProtoReflect (etcd's api/v3, raft's raftpb), called by
// proto.Marshal/Size/Clone/Equal; internal/impl/pointer_unsafe.go:187-217.
// Assumes: nothing.
// Specs: none yet; needs U2, U4 (doc.go), and R3 of examples/specreq/reflect.
func ReqMessageState() *Entry {
	e := &Entry{Term: 7}
	done := make(chan *messageState)
	go func() { done <- e.ProtoReflect().(*messageState) }()
	ms := e.ProtoReflect().(*messageState)
	ms2 := <-done
	if ms != ms2 || ms.messageInfo() != &entryMsgInfo {
		panic("message-state: two states, or the wrong info")
	}
	if back := ms.Interface().(*Entry); back != e {
		panic("message-state: not the same message")
	}
	w1 := (*Entry)(nil).ProtoReflect().(*messageReflectWrapper)
	w2 := (*Entry)(nil).ProtoReflect().(*messageReflectWrapper)
	if w1 != w2 || w1.mi != &entryMsgInfo {
		panic("message-state: nil wrapper not shared")
	}
	return e
}
