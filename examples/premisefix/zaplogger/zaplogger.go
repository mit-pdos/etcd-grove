// Package zaplogger checks premise fixes 6, part A (the zap logger family, 2026-11-11): the Go
// meaning of zapLoggerOk (Spec/go_uber_org/zap/Defs.lean: a non-nil *zap.Logger as zap's
// constructors build it) and srvLoggerOk (Proof/go_etcd_io/etcd/server/v3/etcdserver/InvApplier.lean)
// as runtime checks, and a walk that finds every *zap.Logger reachable from a value. The tests
// (zaplogger_test.go) show that the premises are needed (a zero &zap.Logger{} makes zap's logging
// methods and etcd's logger family panic) and met (by zap's constructors and by every logger the
// examples' servers and clients hold).
//
// Lifted from examples/sweeprepairs/logger (sweep repairs 1, group "logger").
package zaplogger

import (
	"fmt"
	"reflect"
	"unsafe"

	"go.uber.org/zap"
	"go.uber.org/zap/zapcore"

	"go.etcd.io/etcd/server/v3/etcdserver"
)

// field reads the (possibly unexported) field name of the addressable struct value v.
func field(v reflect.Value, name string) reflect.Value {
	f := v.FieldByName(name)
	if !f.IsValid() {
		panic("no field " + name + " in " + v.Type().String())
	}
	return reflect.NewAt(f.Type(), unsafe.Pointer(f.UnsafeAddr())).Elem()
}

// coreOk: c is one of zap's own cores (nopCore, ioCore over a non-nil encoder and write syncer,
// multiCore, levelFilterCore and sampler of such), the cores zap's constructors build. A user core
// (zapcore.RegisterHooks's hooked, or any other implementation) is not admitted: its methods may
// panic or exit.
func coreOk(c zapcore.Core) error {
	if c == nil {
		return fmt.Errorf("nil core")
	}
	v := reflect.ValueOf(c)
	switch v.Type().String() {
	case "zapcore.nopCore":
		return nil
	case "*zapcore.ioCore":
		e := v.Elem()
		if field(e, "enc").IsNil() || field(e, "out").IsNil() || field(e, "LevelEnabler").IsNil() {
			return fmt.Errorf("ioCore with a nil encoder, output or level")
		}
		return nil
	case "zapcore.multiCore":
		for i := 0; i < v.Len(); i++ {
			if err := coreOk(v.Index(i).Interface().(zapcore.Core)); err != nil {
				return fmt.Errorf("multiCore[%d]: %w", i, err)
			}
		}
		return nil
	case "*zapcore.sampler":
		inner := field(v.Elem(), "Core")
		if inner.IsNil() {
			return fmt.Errorf("sampler over nil")
		}
		return coreOk(inner.Interface().(zapcore.Core))
	case "*zapcore.levelFilterCore":
		e := v.Elem()
		inner := field(e, "core")
		if inner.IsNil() {
			return fmt.Errorf("levelFilterCore over nil")
		}
		return coreOk(inner.Interface().(zapcore.Core))
	}
	return fmt.Errorf("core of type %s is not one of zap's", v.Type())
}

// ZapLoggerOk is zapLoggerOk's Go meaning (L1): l is non-nil and holds what zap's constructors
// put there (zap.New, NewNop, NewProduction, NewDevelopment, NewExample, Config.Build, and the
// derivations Named/With/WithOptions(AddCaller*, Development...)): one of zap's own cores, a
// non-nil clock, error output and stack level, and the default terminal hooks (a Fatal entry
// exits, a Panic entry panics with the message). A zero Logger fails it: nil core and clock.
func ZapLoggerOk(l *zap.Logger) error {
	if l == nil {
		return fmt.Errorf("nil *zap.Logger")
	}
	v := reflect.ValueOf(l).Elem()
	core := field(v, "core")
	if core.IsNil() {
		return fmt.Errorf("nil core")
	}
	if err := coreOk(core.Interface().(zapcore.Core)); err != nil {
		return err
	}
	if field(v, "clock").IsNil() {
		return fmt.Errorf("nil clock")
	}
	if field(v, "errorOutput").IsNil() {
		return fmt.Errorf("nil errorOutput")
	}
	if field(v, "addStack").IsNil() {
		return fmt.Errorf("nil addStack")
	}
	for _, h := range []struct {
		name string
		def  zapcore.CheckWriteAction
	}{{"onFatal", zapcore.WriteThenFatal}, {"onPanic", zapcore.WriteThenPanic}} {
		f := field(v, h.name)
		if f.IsNil() {
			continue
		}
		hk := f.Interface()
		if hk != zapcore.CheckWriteHook(zapcore.WriteThenNoop) && hk != zapcore.CheckWriteHook(h.def) {
			return fmt.Errorf("%s hook %v is not the default", h.name, hk)
		}
	}
	return nil
}

// Found is a *zap.Logger reachable from a root, with the path to it.
type Found struct {
	Path string
	L    *zap.Logger
}

var loggerType = reflect.TypeOf((*zap.Logger)(nil))

type ptrKey struct {
	p uintptr
	t reflect.Type
}

type walker struct {
	seen  map[ptrKey]bool
	out   []Found
	nodes int
	limit int
}

func basic(k reflect.Kind) bool {
	switch k {
	case reflect.Bool, reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64,
		reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64, reflect.Uintptr,
		reflect.Float32, reflect.Float64, reflect.Complex64, reflect.Complex128, reflect.String:
		return true
	}
	return false
}

// rw gives a readable copy of v (an addressable value, possibly reached through unexported fields).
func rw(v reflect.Value) reflect.Value {
	if v.CanAddr() {
		return reflect.NewAt(v.Type(), unsafe.Pointer(v.UnsafeAddr())).Elem()
	}
	return v
}

func (w *walker) walk(v reflect.Value, path string, depth int) {
	if w.nodes > w.limit || depth > 60 || !v.IsValid() {
		return
	}
	w.nodes++
	v = rw(v)
	switch v.Kind() {
	case reflect.Pointer:
		if v.IsNil() {
			return
		}
		if v.Type() == loggerType {
			w.out = append(w.out, Found{path, v.Interface().(*zap.Logger)})
			return
		}
		key := ptrKey{v.Pointer(), v.Type()}
		if w.seen[key] {
			return
		}
		w.seen[key] = true
		if v.Type().Elem().Kind() == reflect.Struct || v.Type().Elem().Kind() == reflect.Array ||
			v.Type().Elem().Kind() == reflect.Pointer || v.Type().Elem().Kind() == reflect.Interface ||
			v.Type().Elem().Kind() == reflect.Map || v.Type().Elem().Kind() == reflect.Slice {
			w.walk(v.Elem(), path, depth+1)
		}
	case reflect.Interface:
		if v.IsNil() {
			return
		}
		e := v.Elem()
		c := reflect.New(e.Type()).Elem()
		c.Set(e)
		w.walk(c, path+"("+e.Type().String()+")", depth+1)
	case reflect.Struct:
		t := v.Type()
		if t.PkgPath() == "sync" || t.PkgPath() == "sync/atomic" || t.PkgPath() == "time" {
			return
		}
		for i := 0; i < v.NumField(); i++ {
			w.walk(v.Field(i), path+"."+t.Field(i).Name, depth+1)
		}
	case reflect.Slice, reflect.Array:
		if basic(v.Type().Elem().Kind()) {
			return
		}
		n := v.Len()
		if n > 4096 {
			n = 4096
		}
		for i := 0; i < n; i++ {
			w.walk(v.Index(i), fmt.Sprintf("%s[%d]", path, i), depth+1)
		}
	case reflect.Map:
		if v.IsNil() || basic(v.Type().Elem().Kind()) && basic(v.Type().Key().Kind()) {
			return
		}
		it := v.MapRange()
		i := 0
		for it.Next() && i < 4096 {
			c := reflect.New(it.Value().Type()).Elem()
			c.Set(it.Value())
			w.walk(c, fmt.Sprintf("%s[#%d]", path, i), depth+1)
			i++
		}
	}
}

// Loggers lists the *zap.Logger values reachable from root (a pointer), through structs,
// pointers, interfaces, slices and maps (not channels, functions, or sync/time internals).
func Loggers(root any) []Found {
	w := &walker{seen: map[ptrKey]bool{}, limit: 5_000_000}
	r := reflect.ValueOf(root)
	c := reflect.New(r.Type()).Elem()
	c.Set(r)
	w.walk(c, reflect.TypeOf(root).String(), 0)
	return w.out
}

// Safe runs f and returns what it panicked with, or nil.
func Safe(f func()) (r any) {
	defer func() { r = recover() }()
	f()
	return nil
}

// SrvLoggerOk is srvLoggerOk s (Proof/go_etcd_io/etcd/server/v3/etcdserver/InvApplier.lean: s.lg
// holds a zapLoggerOk logger), with the lock Logger() reads it under (s.lgMu) set.
func SrvLoggerOk(s *etcdserver.EtcdServer) error {
	v := reflect.ValueOf(s).Elem()
	if field(v, "lgMu").IsNil() {
		return fmt.Errorf("nil lgMu")
	}
	return ZapLoggerOk(field(v, "lg").Interface().(*zap.Logger))
}
