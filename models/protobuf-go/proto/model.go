// MODEL: this file is the model's (models/protobuf-go, a model of google.golang.org/protobuf
// v1.36.12's proto package; models/README.md, "The protobuf model"). The rest of the package is
// protobuf-go's, but for the codec's entry points, each marked MODEL: where it changes.
//
// THE ONE TRUSTED STEP (#37, decision D1, kaashoek's review). The shipped binary links the real
// protobuf-go and calls its reflection-based Marshal, Unmarshal, Size, Clone, Merge, Reset and
// CheckInitialized; this model calls instead the methods models/protobuf/pbgen.py's pbmodel mode
// emits into each message type's own package (pbmodel_gen.go: PbModelSize, PbModelAppend,
// PbModelUnmarshal, PbModelClone, PbModelIsInit, PbModelIsNil, PbModelReset, PbModelSelf,
// PbModelMerge), which are verified code (Goose translates them with the message packages, build
// tag goose; the Go model build sets tag pbmodel). What is trusted is that the two agree: for
// every message type pbgen accepts (its trusted core, pbgen_core.py, states the subset and every
// choice with its protobuf-go citation), the bytes, the decoded or merged message (fields and
// unknown fields), error-or-not and the error's class (Marshal's: invalid UTF-8, a size mismatch,
// a required field missing; Unmarshal's: a required field missing or another error;
// CheckInitialized's: a required field missing), what comes with an error, and the effect on
// every level's size cache, of each entry point below are the real one's. This file composes the
// methods as protobuf-go's proto package composes its internal/impl methods (cited at each
// function); the evidence is models/internal/pbgenrand (random schemas, both the methods against
// protobuf-go and this composition restated in each generated test), the per-package generated
// tests (pbmodel_gen_test.go, run on etcd's and raft's message packages by
// examples/models/pbetcd/pbmodel_forks.py), and models/internal/pbmodeltest (the same program built
// against protobuf-go and against this model, equal transcripts).
//
// Not claimed: the error values (only their class: protobuf-go's carry the message's name, these
// the methods' *pbcodec.Error or errRequiredNotSet), slice capacities and which appends share an
// array (lengths and contents are claimed; Marshal's buffer is pre-sized as protobuf-go pre-sizes
// it, so its nil-ness is protobuf-go's).
//
// NOT MODELLED: STUCK (models/README.md, "Not modelled: stuck"; #37, the S3 review's item 1).
// Where the model does not model protobuf-go it calls stuck (below, marked "MODEL: not modelled
// (stuck)"), which has no behavior: its Lean model is the stuck `Panic "not modelled"`, so a proof
// of the program shows it never gets there.
//
// Every entry point of the package, and its status (the S3 review's item 2: none is left to what
// the translation would do with reflection):
//   - modelled, by the methods (this file's composition, each at its function): Marshal,
//     MarshalOptions.{Marshal,MarshalAppend,Size} (UseCachedSize, AllowPartial, Deterministic),
//     Size, Unmarshal, UnmarshalOptions.Unmarshal (default options), Clone, CloneOf, Merge
//     (PbModelMerge: golang/protobuf v1's Merge is this one, client/v3/kv.go:105 reaches it),
//     Reset (PbModelReset), CheckInitialized (PbModelIsInit: golang/protobuf v1's Marshal runs it
//     after MarshalAppend, its checkRequiredNotSet); a nil interface where protobuf-go treats it as
//     an empty message (Marshal, MarshalAppend, Size, Clone, CheckInitialized), as protobuf-go;
//   - stuck (not modelled): a message whose type has no generated methods (no pbmodel_gen.go: a
//     type pbgen was not run on, or refused, or of another API: descriptorpb, anypb, grpc's status
//     and health messages, a dynamicpb message), a nil interface where protobuf-go dereferences it
//     (Unmarshal, Merge, Reset), a Merge source of another type than the destination (protobuf-go
//     panics, a descriptor mismatch), UnmarshalOptions other than the default ones,
//     MarshalOptions.MarshalState, UnmarshalOptions.UnmarshalState, Equal (but on a nil
//     interface), MessageName (but on a nil interface), HasExtension, ClearExtension,
//     GetExtension, SetExtension, RangeExtensions (but their nil guards: pbgen refuses
//     extensions);
//   - protobuf-go's code, unchanged (no reflection): the wrappers' constructors (Bool, Int32,
//     Int64, Float32, Float64, Uint32, Uint64, String), ValueOrNil, ValueOrDefault,
//     ValueOrDefaultBytes, the Error variable, the option types;
//   - protoadapt: MessageV2Of and MessageV1Of, the message itself where it is already of the
//     other API (protoc-gen-go's messages are both), nil for a nil interface; otherwise stuck.
//
// A type embedding a message promotes the methods as it promotes ProtoReflect and Reset; a type
// that declares its own ProtoReflect or Reset would make protobuf-go dispatch to it and the model
// to the embedded message's methods: the gates check that no type of the forks at the pins or of
// the translated packages does (examples/models/pbetcd/pbmodel_forks.py).
package proto

import (
	"google.golang.org/protobuf/encoding/protowire"
	protoerrors "google.golang.org/protobuf/internal/errors"
)

// pbModelMessage: the methods of a message of the model (pbgen's pbmodel mode).
type pbModelMessage interface {
	PbModelSize(cached bool) int
	PbModelAppend(b []byte, cached bool) ([]byte, error)
	PbModelUnmarshal(b []byte) error
	PbModelClone() interface{}
	PbModelIsInit() bool
	PbModelIsNil() bool
	PbModelReset()
	PbModelSelf() interface{}
	PbModelMerge(src interface{}) bool
}

// modelOf: m's methods; a value without them is not modelled (stuck), a nil interface
// included (protobuf-go panics on it, a nil dereference of m.ProtoReflect(), wherever it does not
// treat it as empty).
func modelOf(m interface{}) pbModelMessage {
	x, ok := m.(pbModelMessage)
	if !ok {
		// MODEL: not modelled (stuck): a message whose type has no generated methods (pbgen --pbmodel)
		stuck()
	}
	return x
}

// errRequiredNotSet: the model's error for a required field not set (protobuf-go's is
// errors.RequiredNotSet(name), internal/errors/errors.go; only the class is modelled).
var errRequiredNotSet = protoerrors.New("required field not set")

// modelMarshal is MarshalOptions.marshal (encode.go:174-210) on a message of the model: the size
// pass with the options' UseCachedSize (184-188), the buffer grown as protobuf-go grows it when
// the size does not fit (189-192: growcap), the append pass reading the size caches (193-195:
// MarshalUseCachedSize set whatever the options), a size mismatch returned as the append returned
// it (199-205: protobuf-go wraps it, a value not modelled), then, unless AllowPartial, the
// required-field check (206-209). Deterministic changes nothing in pbgen's subset (no maps, no
// extensions, no lazy fields: the only places internal/impl's encoder reads it).
func (o MarshalOptions) modelMarshal(b []byte, x pbModelMessage) ([]byte, error) {
	n := x.PbModelSize(o.UseCachedSize)
	if cap(b) < len(b)+n {
		nb := make([]byte, len(b), growcap(cap(b), len(b)+n))
		copy(nb, b)
		b = nb
	}
	out, err := x.PbModelAppend(b, true)
	if err != nil {
		return out, err
	}
	if o.AllowPartial || x.PbModelIsInit() {
		return out, nil
	}
	return out, errRequiredNotSet
}

// modelUnmarshal is UnmarshalOptions.Unmarshal with the default options (decode.go:61-64, 90-136):
// the generated Reset, the decode with the recursion limit, the required-field check, all in the
// method. Any other option is not modelled.
func (o UnmarshalOptions) modelUnmarshal(b []byte, m Message) error {
	if o.Merge || o.AllowPartial || o.DiscardUnknown || o.Resolver != nil || o.NoLazyDecoding ||
		(o.RecursionLimit != 0 && o.RecursionLimit != protowire.DefaultRecursionLimit) {
		// MODEL: not modelled (stuck): UnmarshalOptions other than the default ones
		stuck()
	}
	return modelOf(m).PbModelUnmarshal(b)
}

// stuck is the model's not-modelled point (MODEL: not in protobuf-go; models/README.md, "Not modelled:
// stuck"): where the model does not model protobuf-go's behavior it calls stuck (after a comment
// `MODEL: not modelled (stuck): ...`), which has no behavior. Its Lean model is Perennial's
// internal/gomodel.Stuck, `Panic "not modelled"`: a stuck panic, which no recover catches and no
// WP rule steps, so a proof of the program shows that it never gets here. Not a value panic, which
// a program could recover and so observe a behavior protobuf-go does not have; not a bare `select {}`,
// whose WP has the precondition True and so would prove anything after it. Its Go body blocks
// forever, which the tests detect (models/internal/stuck).
func stuck() {
	select {}
}
