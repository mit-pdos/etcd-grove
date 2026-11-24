package reflect

// encoding/json's reflective walks, minimized: the fields of a struct from
// its tags, maps with sorted keys, nil pointers, Marshaler methods found by
// Implements, and the decoder's allocation through pointers.
//
// In Go 1.27.3, encoding/json is encoding/json/v2 underneath
// (GOEXPERIMENT=jsonv2 is on by default; encoding/json's v2_*.go shims call
// it; the legacy encode.go/decode.go are not built). Mirrors
// encoding/json/v2:
//   - arshal.go:228-241 (marshalEncode: a nil pointer is null; a value that
//     is not a pointer is copied into `reflect.New(v.Type()).Elem()` so that
//     it is addressable, but marked forcedAddr: under encoding/json's v1
//     options (CallMethodsWithLegacySemantics, arshal_methods.go:229-236) a
//     pointer-receiver MarshalJSON is not called on such a value or its
//     fields, so Marshal(m) and Marshal(&m) differ) and :447-449 (unmarshalDecode: `Kind() != Pointer ||
//     IsNil()` is an error, encoding/json's InvalidUnmarshalError,
//     v2_inject.go:73-74);
//   - arshal.go:526-539 (the arshaler cache: a sync.Map keyed by
//     reflect.Type), arshal_default.go:89-124 (dispatch on Kind);
//   - fields.go:80-130, 410-551 (makeStructFields: NumField, Field(i),
//     `sf.Tag.Lookup("json")`, "-" skips, unexported non-embedded fields
//     skipped (`!sf.IsExported() && !sf.Anonymous`), embedded structs
//     flattened, options omitempty and string);
//   - arshal_methods.go:417-429 (implements: `t.Implements(iface) ||
//     reflect.PointerTo(t).Implements(iface)`, then the method through
//     `va.Addr()`);
//   - arshal_default.go:913-940 (maps: MapRange, keys sorted), :984,1063
//     (decode: MakeMap, SetMapIndex), :1562-1600 (slices: SetLen, Grow),
//     :1776 (pointers: `va.Set(reflect.New(t.Elem()))`).
// Users: etcd's membership records (storev2.go:125,150,188,195,
// cluster.go:320,376; this repository's json model replaces them,
// models/jsoncodec), etcdserver cluster_util.go:98,281,356, corrupt.go:545-622,
// server.go:1415,1550,1680,2062,2092, v2store store.go:734-772, the
// client's endpoints manager (naming/endpoints/endpoints_impl.go:72-185),
// storage/schema/membership.go:53,158,220; zap's reflected encoder
// (zapcore/reflected_encoder.go:36, json.NewEncoder), the fallback of
// zap.Any. snippets_test.go checks that marshal agrees with encoding/json.
//
// To prove: marshal returns the JSON text below for each value (fields in
// declaration order with their tag names, embedded fields flattened, "-"
// and unexported fields left out, omitempty fields left out when empty, map
// keys sorted, nil pointers and nil slices null, a Marshaler's own text); the
// decode of that text back into a fresh pointer gives the value back; the
// decode into a non-pointer is an error, not a panic.
//
// Needs R1 (Kind, Elem, Key, NumField, Field(i) with Name, Tag, Anonymous,
// IsExported; Implements; PointerTo) and R2 (New, Elem, Set, Addr, CanAddr,
// Interface, Field, IsNil, Len, Index, MapRange, MakeMap, SetMapIndex,
// MakeSlice, Append, the typed getters and setters).

import (
	"reflect"
	"sort"
	"strconv"
	"strings"
)

type URLs []string

// Peer has a Marshaler on its pointer, as etcd's types.URLs-like fields do.
type Peer struct{ Host string }

func (p *Peer) MarshalJSON() ([]byte, error) { return []byte(strconv.Quote("peer:" + p.Host)), nil }

type RaftAttributes struct {
	PeerURLs  []string `json:"peerURLs"`
	IsLearner bool     `json:"isLearner,omitempty"`
}

type MemberRecord struct {
	ID uint64 `json:"id"`
	RaftAttributes
	Name    string            `json:"name,omitempty"`
	Labels  map[string]string `json:"labels"`
	Peer    Peer              `json:"peer"`
	Parent  *MemberRecord     `json:"parent"`
	Ignored string            `json:"-"`
	secret  string
}

// jsonMarshaler is encoding/json's Marshaler (in Go 1.27.3 an alias of encoding/json/v2's): the
// same method set, declared here so that the snippet does not import encoding/json, whose
// translation in this repository is its model's (models/encoding/json).
type jsonMarshaler interface {
	MarshalJSON() ([]byte, error)
}

var marshalerType = reflect.TypeOf((*jsonMarshaler)(nil)).Elem()

type jsonField struct {
	index     []int
	name      string
	omitempty bool
}

// structFields is makeStructFields, minimized: tags, "-", unexported, embedded, omitempty.
func structFields(t reflect.Type, prefix []int) []jsonField {
	var fs []jsonField
	for i := 0; i < t.NumField(); i++ {
		sf := t.Field(i)
		tag, hasTag := sf.Tag.Lookup("json")
		if tag == "-" {
			continue
		}
		if !sf.IsExported() && !sf.Anonymous {
			continue
		}
		index := append(append([]int{}, prefix...), i)
		if sf.Anonymous && !hasTag && sf.Type.Kind() == reflect.Struct {
			fs = append(fs, structFields(sf.Type, index)...)
			continue
		}
		name, opts, _ := strings.Cut(tag, ",")
		if name == "" {
			name = sf.Name
		}
		fs = append(fs, jsonField{index: index, name: name, omitempty: opts == "omitempty"})
	}
	return fs
}

func isEmptyValue(v reflect.Value) bool {
	switch v.Kind() {
	case reflect.String, reflect.Slice, reflect.Map:
		return v.Len() == 0
	case reflect.Bool:
		return !v.Bool()
	case reflect.Uint64, reflect.Int64, reflect.Int:
		return v.IsZero()
	case reflect.Pointer, reflect.Interface:
		return v.IsNil()
	}
	return false
}

// encodeValue writes v (addressable) as JSON; forcedAddr is v2's addressableValue.forcedAddr.
func encodeValue(b []byte, v reflect.Value, forcedAddr bool) []byte {
	t := v.Type()
	if t.Kind() != reflect.Pointer && !forcedAddr && v.CanAddr() && reflect.PointerTo(t).Implements(marshalerType) {
		out, err := v.Addr().Interface().(jsonMarshaler).MarshalJSON()
		if err != nil {
			panic("json-walk: MarshalJSON: " + err.Error())
		}
		return append(b, out...)
	}
	switch v.Kind() {
	case reflect.Bool:
		return strconv.AppendBool(b, v.Bool())
	case reflect.Int, reflect.Int64:
		return strconv.AppendInt(b, v.Int(), 10)
	case reflect.Uint64:
		return strconv.AppendUint(b, v.Uint(), 10)
	case reflect.String:
		return strconv.AppendQuote(b, v.String())
	case reflect.Pointer, reflect.Interface:
		if v.IsNil() {
			return append(b, "null"...)
		}
		return encodeValue(b, v.Elem(), false)
	case reflect.Slice:
		if v.IsNil() {
			return append(b, "null"...)
		}
		b = append(b, '[')
		for i := 0; i < v.Len(); i++ {
			if i > 0 {
				b = append(b, ',')
			}
			b = encodeValue(b, v.Index(i), false)
		}
		return append(b, ']')
	case reflect.Map:
		if v.IsNil() {
			return append(b, "null"...)
		}
		var keys []string
		vals := map[string]reflect.Value{}
		for it := v.MapRange(); it.Next(); {
			k := it.Key().String()
			keys = append(keys, k)
			vals[k] = it.Value()
		}
		sort.Strings(keys)
		b = append(b, '{')
		for i, k := range keys {
			if i > 0 {
				b = append(b, ',')
			}
			b = strconv.AppendQuote(b, k)
			b = append(b, ':')
			mv := reflect.New(vals[k].Type()).Elem()
			mv.Set(vals[k])
			b = encodeValue(b, mv, true)
		}
		return append(b, '}')
	case reflect.Struct:
		b = append(b, '{')
		first := true
		for _, f := range structFields(t, nil) {
			fv := v.FieldByIndex(f.index)
			if f.omitempty && isEmptyValue(fv) {
				continue
			}
			if !first {
				b = append(b, ',')
			}
			first = false
			b = strconv.AppendQuote(b, f.name)
			b = append(b, ':')
			b = encodeValue(b, fv, forcedAddr)
		}
		return append(b, '}')
	}
	panic("json-walk: unsupported kind " + v.Kind().String())
}

// marshal is marshalEncode: nil pointer null, else the pointee, or an addressable copy marked
// forcedAddr.
func marshal(x any) string {
	v := reflect.ValueOf(x)
	if !v.IsValid() || (v.Kind() == reflect.Pointer && v.IsNil()) {
		return "null"
	}
	forceAddr := v.Kind() != reflect.Pointer
	if forceAddr {
		v2 := reflect.New(v.Type())
		v2.Elem().Set(v)
		v = v2
	}
	return string(encodeValue(nil, v.Elem(), forceAddr))
}

// decodeInto stores the parsed JSON tree t (encoding/json's any: map[string]any, []any,
// float64, string, bool, nil) into the settable v, allocating through pointers, maps and
// slices as the v2 decoder does.
func decodeInto(v reflect.Value, t any) {
	if t == nil {
		v.Set(reflect.Zero(v.Type()))
		return
	}
	switch v.Kind() {
	case reflect.Pointer:
		if v.IsNil() {
			v.Set(reflect.New(v.Type().Elem()))
		}
		decodeInto(v.Elem(), t)
	case reflect.Bool:
		v.SetBool(t.(bool))
	case reflect.Uint64:
		v.SetUint(uint64(t.(float64)))
	case reflect.String:
		v.SetString(t.(string))
	case reflect.Slice:
		arr := t.([]any)
		v.Set(reflect.MakeSlice(v.Type(), 0, len(arr)))
		for _, e := range arr {
			ev := reflect.New(v.Type().Elem()).Elem()
			decodeInto(ev, e)
			v.Set(reflect.Append(v, ev))
		}
	case reflect.Map:
		obj := t.(map[string]any)
		if v.IsNil() {
			v.Set(reflect.MakeMap(v.Type()))
		}
		for k, e := range obj {
			ev := reflect.New(v.Type().Elem()).Elem()
			decodeInto(ev, e)
			v.SetMapIndex(reflect.ValueOf(k).Convert(v.Type().Key()), ev)
		}
	case reflect.Struct:
		obj := t.(map[string]any)
		for _, f := range structFields(v.Type(), nil) {
			if e, ok := obj[f.name]; ok {
				decodeInto(v.FieldByIndex(f.index), e)
			}
		}
	default:
		panic("json-walk: unsupported kind " + v.Kind().String())
	}
}

// unmarshal is unmarshalDecode: the target must be a non-nil pointer.
func unmarshal(t any, out any) string {
	v := reflect.ValueOf(out)
	if v.Kind() != reflect.Pointer || v.IsNil() {
		if !v.IsValid() {
			return "json: Unmarshal(nil)"
		}
		return "json: Unmarshal(non-pointer " + v.Type().String() + ")"
	}
	decodeInto(v.Elem(), t)
	return ""
}

const memberJSON = `{"id":7,"peerURLs":["http://a:2380"],"labels":{"a":"1","b":"2"},"peer":"peer:h","parent":null}`

// memberJSONValue is Marshal of the record itself, not of a pointer: the copy is not
// addressable for MarshalJSON, so Peer is written field by field.
const memberJSONValue = `{"id":7,"peerURLs":["http://a:2380"],"labels":{"a":"1","b":"2"},"peer":{"Host":"h"},"parent":null}`

// REQ reflect/json-walk: the reflective marshal of a member record writes its fields by tag
// name in declaration order, flattens the embedded RaftAttributes, leaves out "-", unexported
// and empty omitempty fields, sorts map keys, writes nil pointers and nil slices as null and
// a field's pointer-receiver Marshaler's text when the record is marshaled through a pointer
// (and the field's own fields when it is marshaled by value); the decode of a parsed record into a fresh
// pointer gives the record back (a map and slices allocated, a nil pointer kept nil); a
// non-pointer target is an error.
// Users: etcd membership storev2.go:125,150,188,195, cluster.go:320,376; etcdserver
// cluster_util.go, corrupt.go, server.go; v2store store.go:734-772; client/v3
// naming/endpoints; zap's reflected encoder.
// Assumes: nothing.
// Specs: none yet; needs R1 and R2 (doc.go).
func ReqJSONWalk() {
	m := MemberRecord{ID: 7, RaftAttributes: RaftAttributes{PeerURLs: []string{"http://a:2380"}},
		Labels: map[string]string{"b": "2", "a": "1"}, Peer: Peer{Host: "h"}, Ignored: "x", secret: "s"}
	if s := marshal(&m); s != memberJSON {
		panic("json-walk: marshal: " + s)
	}
	if s := marshal(m); s != memberJSONValue {
		panic("json-walk: marshal by value: " + s)
	}
	if marshal((*MemberRecord)(nil)) != "null" || marshal(URLs(nil)) != "null" || marshal(URLs{}) != "[]" {
		panic("json-walk: null and empty")
	}
	if s := marshal(RaftAttributes{IsLearner: true}); s != `{"peerURLs":null,"isLearner":true}` {
		panic("json-walk: omitempty kept when not empty: " + s)
	}
	parsed := map[string]any{"id": float64(7), "peerURLs": []any{"http://a:2380"},
		"labels": map[string]any{"a": "1", "b": "2"}, "parent": nil, "isLearner": true}
	var out *MemberRecord
	if err := unmarshal(parsed, &out); err != "" {
		panic("json-walk: " + err)
	}
	if out == nil || out.ID != 7 || len(out.PeerURLs) != 1 || out.PeerURLs[0] != "http://a:2380" ||
		!out.IsLearner || out.Labels["b"] != "2" || len(out.Labels) != 2 || out.Parent != nil {
		panic("json-walk: decode")
	}
	if err := unmarshal(parsed, MemberRecord{}); err != "json: Unmarshal(non-pointer reflect.MemberRecord)" {
		panic("json-walk: a non-pointer target: " + err)
	}
	if err := unmarshal(parsed, nil); err != "json: Unmarshal(nil)" {
		panic("json-walk: a nil target")
	}
}
