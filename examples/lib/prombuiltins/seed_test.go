package prombuiltins

import (
	"os"
	"reflect"
	"regexp"
	"runtime"
	"runtime/debug"
	"strconv"
	"strings"
	"testing"
	"unsafe"

	"github.com/prometheus/client_golang/prometheus"
)

// The trusted model of prometheus's init() and the versions its constants are measured on.
const (
	leanFile      = "../../../TrustedCode/github_com/prometheus/client_golang/prometheus.lean"
	goToolchain   = "go1.27.3" // etc/goose.py's GO_TOOLCHAIN
	clientGolang  = "v1.24.1"  // the translated client_golang (Code/github_com/prometheus/client_golang)
	clientGolangP = "github.com/prometheus/client_golang"
)

// field reads the unexported field name of the struct v.
func field(v reflect.Value, name string) reflect.Value {
	f := v.FieldByName(name)
	return reflect.NewAt(f.Type(), unsafe.Pointer(f.UnsafeAddr())).Elem()
}

// state is what the model sets of a *prometheus.Registry: its descriptor IDs, its names with their dim
// hashes, and its collector IDs, and the number of unchecked collectors.
type state struct {
	ids       map[uint64]bool
	dims      map[string]uint64
	cols      map[uint64]bool
	unchecked int
}

func realState(r *prometheus.Registry) state {
	v := reflect.ValueOf(r).Elem()
	s := state{ids: map[uint64]bool{}, dims: map[string]uint64{}, cols: map[uint64]bool{}}
	for _, k := range field(v, "descIDs").MapKeys() {
		s.ids[k.Uint()] = true
	}
	dm := field(v, "dimHashesByName")
	for _, k := range dm.MapKeys() {
		s.dims[k.String()] = dm.MapIndex(k).Uint()
	}
	for _, k := range field(v, "collectorsByID").MapKeys() {
		s.cols[k.Uint()] = true
	}
	s.unchecked = field(v, "uncheckedCollectors").Len()
	return s
}

// defBody is the body of the Lean definition `def name ... :=`, up to the next definition.
func defBody(t *testing.T, src, name string) string {
	t.Helper()
	i := strings.Index(src, "def "+name+" ")
	if i < 0 {
		t.Fatalf("%s: no definition %s", leanFile, name)
	}
	rest := src[i+len("def "+name+" "):]
	if j := strings.Index(rest, "\ndef "); j >= 0 {
		rest = rest[:j]
	}
	if j := strings.Index(rest, "\n/--"); j >= 0 {
		rest = rest[:j]
	}
	return rest
}

var hexRE = regexp.MustCompile(`0x[0-9a-f]+`)
var dimRE = regexp.MustCompile(`\(go!"([^"]*)", (0x[0-9a-f]+)\)`)

func hex(t *testing.T, s string) uint64 {
	t.Helper()
	n, err := strconv.ParseUint(s[2:], 16, 64)
	if err != nil {
		t.Fatal(err)
	}
	return n
}

// leanState is the state the model's init() leaves in the empty registry.
func leanState(t *testing.T) state {
	b, err := os.ReadFile(leanFile)
	if err != nil {
		t.Fatal(err)
	}
	src := string(b)
	s := state{ids: map[uint64]bool{}, dims: map[string]uint64{}, cols: map[uint64]bool{}}
	ids := hexRE.FindAllString(defBody(t, src, "seed.descIDs"), -1)
	for _, h := range ids {
		s.ids[hex(t, h)] = true
	}
	ds := dimRE.FindAllStringSubmatch(defBody(t, src, "seed.dims"), -1)
	for _, m := range ds {
		s.dims[m[1]] = hex(t, m[2])
	}
	cs := hexRE.FindAllString(defBody(t, src, "seed.collectorIDs"), -1)
	for _, h := range cs {
		s.cols[hex(t, h)] = true
	}
	if len(ids) != 38 || len(s.ids) != 38 || len(ds) != 38 || len(s.dims) != 38 || len(cs) != 2 || len(s.cols) != 2 {
		t.Fatalf("%s: expected 38 distinct IDs, 38 distinct names, 2 collector IDs; read %d (%d), %d (%d), %d (%d)",
			leanFile, len(ids), len(s.ids), len(ds), len(s.dims), len(cs), len(s.cols))
	}
	return s
}

func checkVersions(t *testing.T) {
	if v := runtime.Version(); v != goToolchain {
		t.Fatalf("toolchain %s, the constants are %s's: run with GOTOOLCHAIN=%s", v, goToolchain, goToolchain)
	}
	if runtime.GOOS != "linux" || runtime.GOARCH != "amd64" {
		t.Fatalf("%s/%s: the constants are linux/amd64's (configuration C)", runtime.GOOS, runtime.GOARCH)
	}
	bi, ok := debug.ReadBuildInfo()
	if !ok {
		t.Fatal("no build info")
	}
	for _, d := range bi.Deps {
		if d.Path == clientGolangP {
			if d.Version != clientGolang || d.Replace != nil {
				t.Fatalf("%s %s (replace %v), the constants are %s's", d.Path, d.Version, d.Replace, clientGolang)
			}
			return
		}
	}
	t.Fatalf("%s not a dependency", clientGolangP)
}

func same(t *testing.T, what string, got, want state) {
	t.Helper()
	if !reflect.DeepEqual(got, want) {
		t.Fatalf("%s differs from the trusted init()'s constants:\nreal %+v\nlean %+v", what, got, want)
	}
}

// TestSeedConstants: the trusted init()'s constants are the state client_golang v1.24.1's init() leaves in
// its default registry (and the state the same two registrations leave in a new registry): its descriptor
// IDs, its names with their dim hashes, its collector IDs, and no unchecked collector.
func TestSeedConstants(t *testing.T) {
	checkVersions(t)
	want := leanState(t)
	same(t, "the default registry", realState(prometheus.DefaultRegisterer.(*prometheus.Registry)), want)
	r := prometheus.NewRegistry()
	r.MustRegister(prometheus.NewProcessCollector(prometheus.ProcessCollectorOpts{}))
	r.MustRegister(prometheus.NewGoCollector())
	same(t, "a new registry with the two collectors", realState(r), want)
}
