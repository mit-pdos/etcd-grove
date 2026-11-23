// MODEL: this file is the model's (models/protobuf-go, a model of google.golang.org/protobuf
// v1.36.12's proto package; models/README.md, "The protobuf model"). The rest of the package is
// protobuf-go's, but for the codec's entry points, each marked MODEL: where it changes.
//
// THE ONE TRUSTED STEP (#37, decision D1, kaashoek's review). The shipped binary links the real
// protobuf-go and calls its reflection-based Marshal, Unmarshal, Size and Clone; this model calls
// instead the methods models/protobuf/pbgen.py's pbmodel mode emits into each message type's own
// package (pbmodel_gen.go: PbModelSize, PbModelAppend, PbModelUnmarshal, PbModelClone,
// PbModelIsInit, PbModelIsNil), which are verified code (Goose translates them with the message
// packages, build tag goose; the Go model build sets tag pbmodel). What is trusted is that the two
// agree: for every message type pbgen accepts (its trusted core, pbgen_core.py, states the subset
// and every choice with its protobuf-go citation), the bytes, the decoded message (fields and
// unknown fields), error-or-not and the error's class (Marshal's: invalid UTF-8, a size mismatch,
// a required field missing; Unmarshal's: a required field missing or another error), what comes
// with an error, and the effect on every level's size cache, of each entry point below are the
// real one's. This file composes
// the methods as protobuf-go's proto package composes its internal/impl methods (cited at each
// function); the evidence is models/internal/pbgenrand (random schemas, both the methods against
// protobuf-go and this composition restated in each generated test), the per-package generated
// tests (pbmodel_gen_test.go, run on etcd's and raft's message packages by
// examples/models/pbetcd/pbmodel_forks.py), and models/internal/pbmodeltest (the same program built
// against protobuf-go and against this model, equal transcripts).
//
// Not claimed: the error values (only their class: protobuf-go's carry the message's name, these
// the methods' *pbcodec.Error or errRequired), slice capacities and which appends share an array
// (lengths and contents are claimed; Marshal's buffer is pre-sized as protobuf-go pre-sizes it, so
// its nil-ness is protobuf-go's). Outside the model, a panic with a NotModelled value: a message
// whose type has no such methods (no pbmodel_gen.go: a type pbgen was not run on, or refused, or a
// type of another API: descriptorpb, anypb, grpc's status and health messages, a dynamicpb
// message), UnmarshalOptions other than the default ones, MarshalState and UnmarshalState. The
// other functions of the package (Equal, Merge, Reset, CheckInitialized, the extension functions,
// the wrappers' constructors) are protobuf-go's code, unchanged and outside the claim (they use
// reflection, which Goose does not translate).
package proto

import (
	"google.golang.org/protobuf/encoding/protowire"
	protoerrors "google.golang.org/protobuf/internal/errors"
)

// NotModelled is the value the model panics with outside the model (models/README.md: every
// model's NotModelled panic has a NotModelled method).
type NotModelled string

// NotModelled marks the value as the models' panic.
func (NotModelled) NotModelled() {}

// pbModelMessage: the methods of a message of the model (pbgen's pbmodel mode).
type pbModelMessage interface {
	PbModelSize(cached bool) int
	PbModelAppend(b []byte, cached bool) ([]byte, error)
	PbModelUnmarshal(b []byte) error
	PbModelClone() interface{}
	PbModelIsInit() bool
	PbModelIsNil() bool
}

// modelOf: m's methods, or a NotModelled panic (a nil interface included: protobuf-go panics on
// it too, a nil dereference of m.ProtoReflect(), wherever it does not treat it as empty).
func modelOf(m interface{}) pbModelMessage {
	x, ok := m.(pbModelMessage)
	if !ok {
		panic(NotModelled("protobuf model: a message whose type has no generated methods (pbgen --pbmodel)"))
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
		panic(NotModelled("protobuf model: UnmarshalOptions other than the default ones"))
	}
	return modelOf(m).PbModelUnmarshal(b)
}
